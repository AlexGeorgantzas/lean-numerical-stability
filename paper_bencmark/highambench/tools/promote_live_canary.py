#!/usr/bin/env python3
"""Explicitly promote authenticated private live-canary evidence.

Promotion is opt-in: callers must name the attestation(s) to promote.  Each
candidate and every artifact it references is authenticated before any frozen
metadata changes.  The operation then atomically replaces the selected evidence
file(s), sets only their matching descriptor(s) to ``passed``, and refreshes the
release/environment hashes without rewriting benchmark tasks or shared sources.
On any error, all touched files are restored byte-for-byte.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import tempfile
from typing import Any, Mapping, Sequence

try:
    from .common import BenchmarkToolError, read_json, sha256_file
    from . import refresh_snapshot
    from . import run_matrix
    from . import run_token_control_canary as token_canary
    from . import run_ultra_orchestration_canary as ultra_canary
except ImportError:  # Direct script execution.
    from common import BenchmarkToolError, read_json, sha256_file  # type: ignore
    import refresh_snapshot  # type: ignore
    import run_matrix  # type: ignore
    import run_token_control_canary as token_canary  # type: ignore
    import run_ultra_orchestration_canary as ultra_canary  # type: ignore


TOKEN_EVIDENCE_RELATIVE = Path("metadata/evidence/token_control_live_canary.json")
ULTRA_EVIDENCE_RELATIVE = Path(
    "metadata/evidence/ultra_orchestration_live_canary.json"
)
MUTATED_METADATA_RELATIVES = (
    Path("metadata/config.json"),
    Path("metadata/environment.json"),
    Path("metadata/release_files.json"),
)


def _mapping(value: Any, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise BenchmarkToolError(f"{label} must be a JSON object")
    return value


def _read_candidate(path: Path, project_root: Path, label: str) -> tuple[bytes, Mapping[str, Any]]:
    path = path.resolve()
    project = project_root.resolve()
    try:
        path.relative_to(project)
    except ValueError as error:
        raise BenchmarkToolError(f"{label} attestation must be below project root") from error
    if path.is_symlink() or not path.is_file():
        raise BenchmarkToolError(f"{label} attestation must be a regular non-symlink file")
    payload = path.read_bytes()
    try:
        value = json.loads(payload)
    except json.JSONDecodeError as error:
        raise BenchmarkToolError(f"{label} attestation is invalid JSON: {error}") from error
    return payload, _mapping(value, f"{label} attestation")


def _atomic_bytes(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.NamedTemporaryFile(
        prefix=f".{path.name}.promote-", dir=path.parent, delete=False
    ) as stream:
        temporary = Path(stream.name)
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())
    os.replace(temporary, path)


def _restore(path: Path, payload: bytes | None) -> None:
    if payload is None:
        path.unlink(missing_ok=True)
    else:
        _atomic_bytes(path, payload)


def _expected_agent(frozen: Mapping[str, Any]) -> dict[str, Any]:
    return {
        "id": frozen.get("agent_id"),
        "version": frozen.get("agent_version"),
        "binary_sha256": frozen.get("agent_binary_sha256"),
        "model": frozen.get("model_version"),
        "reasoning_effort": frozen.get("model_reasoning_effort"),
        "ultra_orchestration": frozen.get("ultra_orchestration"),
    }


def promote(
    benchmark_root: Path,
    project_root: Path,
    *,
    token_control_attestation: Path | None = None,
    ultra_orchestration_attestation: Path | None = None,
) -> dict[str, Any]:
    """Validate and transactionally promote one or both named attestations."""

    if token_control_attestation is None and ultra_orchestration_attestation is None:
        raise BenchmarkToolError("promotion requires at least one explicit attestation")
    root = benchmark_root.resolve()
    project = project_root.resolve()
    try:
        root.relative_to(project)
    except ValueError as error:
        raise BenchmarkToolError("benchmark root must be below project root") from error
    config = dict(_mapping(read_json(root / "metadata/config.json"), "config"))
    environment = dict(
        _mapping(read_json(root / "metadata/environment.json"), "environment")
    )
    manifest = _mapping(read_json(root / "metadata/manifest.json"), "manifest")
    frozen = dict(_mapping(config.get("frozen_environment"), "frozen environment"))
    config["frozen_environment"] = frozen
    expected_agent = _expected_agent(frozen)
    expected_prompt_protocol, expected_execution_components = (
        run_matrix.production_freeze_bindings(config, environment)
    )
    benchmark_id = config.get("benchmark_id")
    limits = _mapping(config.get("limits"), "config limits")
    token_limit = limits.get("total_model_tokens")
    if not isinstance(benchmark_id, str) or not benchmark_id:
        raise BenchmarkToolError("config benchmark_id is invalid")
    if not isinstance(token_limit, int) or isinstance(token_limit, bool) or token_limit <= 0:
        raise BenchmarkToolError("config token limit is invalid")

    candidates: dict[str, tuple[Path, bytes, Mapping[str, Any], dict[str, Any]]] = {}
    if ultra_orchestration_attestation is not None:
        payload, evidence = _read_candidate(
            ultra_orchestration_attestation, project, "Ultra orchestration"
        )
        summary = ultra_canary.verify_evidence_document(
            evidence,
            project_root=project,
            expected_benchmark_id=benchmark_id,
            expected_agent=expected_agent,
            expected_token_limit=token_limit,
            expected_prompt_protocol=expected_prompt_protocol,
            expected_execution_components=expected_execution_components,
        )
        candidates["ultra_orchestration_canary"] = (
            root / ULTRA_EVIDENCE_RELATIVE,
            payload,
            evidence,
            summary,
        )
    if token_control_attestation is not None:
        payload, evidence = _read_candidate(
            token_control_attestation, project, "token-control"
        )
        summary = token_canary.validate_attestation_document(
            evidence,
            project_root=project,
            expected_benchmark_id=benchmark_id,
            expected_agent=expected_agent,
            expected_frozen_token_limit=token_limit,
        )
        candidates["token_control_canary"] = (
            root / TOKEN_EVIDENCE_RELATIVE,
            payload,
            evidence,
            summary,
        )

    touched = [item[0] for item in candidates.values()]
    touched.extend(root / relative for relative in MUTATED_METADATA_RELATIVES)
    backups = {path: path.read_bytes() if path.is_file() else None for path in touched}
    try:
        for key, (destination, payload, _evidence, _summary) in candidates.items():
            _atomic_bytes(destination, payload)
            descriptor = {
                "path": (
                    token_canary.FROZEN_EVIDENCE_PATH
                    if key == "token_control_canary"
                    else ultra_canary.FROZEN_EVIDENCE_PATH
                ),
                "sha256": sha256_file(destination),
                "status": "passed",
            }
            frozen[key] = descriptor
            environment[key] = dict(descriptor)

        paper_ids = [
            str(paper.get("paper_id"))
            for paper in manifest.get("papers", [])
            if isinstance(paper, Mapping)
        ]
        if not paper_ids or any(not paper_id for paper_id in paper_ids):
            raise BenchmarkToolError("manifest paper IDs are invalid")
        refresh_snapshot._sync_release_and_environment(
            root,
            config,
            environment,
            manifest,
            corpus_slug=refresh_snapshot._corpus_slug(paper_ids),
        )
    except Exception:
        for path in reversed(touched):
            _restore(path, backups[path])
        raise

    return {
        "status": "passed",
        "promoted": {
            key: {
                "descriptor": frozen[key],
                "summary": summary,
            }
            for key, (_destination, _payload, _evidence, summary) in candidates.items()
        },
        "environment_id": environment.get("environment_id"),
        "release_manifest_sha256": environment.get("release_manifest_sha256"),
        "benchmark_task_files_modified": False,
    }


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--benchmark-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
    )
    parser.add_argument("--project-root", type=Path, required=True)
    parser.add_argument("--token-control-attestation", type=Path)
    parser.add_argument("--ultra-orchestration-attestation", type=Path)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    try:
        result = promote(
            args.benchmark_root,
            args.project_root,
            token_control_attestation=args.token_control_attestation,
            ultra_orchestration_attestation=args.ultra_orchestration_attestation,
        )
    except (OSError, BenchmarkToolError, ValueError) as error:
        print(f"live-canary promotion error: {error}")
        return 2
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
