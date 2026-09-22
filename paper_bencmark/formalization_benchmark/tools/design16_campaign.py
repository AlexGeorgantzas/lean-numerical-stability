#!/usr/bin/env python3
"""Run the frozen 13-task Design-16 exploratory campaign sequentially.

This is a provider-free control-plane wrapper around ``design16_matched.py``:
it never calls a model itself.  A single host-wide lock prevents two campaign
controllers from running timed contestants concurrently.  State and summaries
are hash-chained JSONL journals, so resume never rewrites prior evidence.

The campaign is explicitly exploratory.  Its two primary engineering tasks,
six negative controls, and five excluded/collision diagnostics are always
reported as separate strata; no pooled treatment estimate is produced.
"""

from __future__ import annotations

import argparse
import ast
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import secrets
import shutil
import subprocess
import sys
from typing import Any, Callable, Iterator, Mapping, Sequence

from common import (
    BenchmarkError,
    canonical_json_bytes,
    file_tree_fingerprint,
    sha256_file,
    treatment_free_runtime_manifest,
    tree_manifest,
    utc_now,
)
from deployment import Deployment, load_deployment
from hardware import (
    EXPECTED_LOGICAL_CPUS,
    EXPECTED_MEMORY_BYTES,
    EXPECTED_TASKS_MAX,
    frozen_hardware_identity,
    snapshot_hardware,
    systemd_service_envelope_prefix,
)
from manifest_control import ROOT
from measure_library_build import validate_build_record
from titan_envelope import COMMAND_CGROUP_VARIABLE, prepare_command_cgroup


SCHEMA = "formalization-design16-exploratory-campaign-1"
SCIENTIFIC_STATUS = "UNSCORED_ENGINEERING_EXPLORATORY"
EXPECTED_TASKS = (
    "H22-11",
    "H22-5",
    "H20-6",
    "H7-12",
    "H20-9",
    "H20-8",
    "H23-6",
    "H5-5",
    "H10-7",
    "H12-4",
    "H19-5",
    "H7-14",
    "H15-3",
)
EXPECTED_STRATA = {
    "primary_engineering": ("H5-5", "H10-7"),
    "negative_control": (
        "H22-11",
        "H20-6",
        "H7-12",
        "H12-4",
        "H19-5",
        "H7-14",
    ),
    "excluded_collision_or_router_error": (
        "H22-5",
        "H20-9",
        "H20-8",
        "H23-6",
        "H15-3",
    ),
}
TERMINAL_EVENT_TYPES = frozenset(
    {
        "TASK_FORMALIZATION_COMPLETE",
        "TASK_AUDITED_FAITHFUL",
        "TASK_AUDITED_INELIGIBLE",
        "TASK_INCIDENT",
        "TASK_RECOVERED_FORMALIZATION_COMPLETE",
        "TASK_RECOVERED_AUDITED_FAITHFUL",
        "TASK_RECOVERED_AUDITED_INELIGIBLE",
        "TASK_RECOVERED_INCIDENT",
    }
)
HEX40 = re.compile(r"[0-9a-f]{40}")
HEX64 = re.compile(r"[0-9a-f]{64}")
TITAN_ENVELOPE_MARKER = "HIGHAMBENCH_DESIGN16_TITAN_ENVELOPE"
PAIR_ATTESTATION = "campaign-pair-attestation.json"
AUDIT_PENDING = "FORMALIZATION_COMPLETE_AUDIT_PENDING"
AUDITED_FAITHFUL = "AUDITED_FAITHFUL_PAIR"
AUDITED_INELIGIBLE = "AUDITED_PAIR_INELIGIBLE"
ATTESTED_PAIR_INCIDENT = "PAIR_INFRASTRUCTURE_INCIDENT"
ATTESTABLE_PAIR_OUTCOMES = frozenset(
    {
        AUDIT_PENDING,
        AUDITED_FAITHFUL,
        AUDITED_INELIGIBLE,
        ATTESTED_PAIR_INCIDENT,
    }
)
INCIDENT_OUTCOMES = frozenset({"INCIDENT", ATTESTED_PAIR_INCIDENT})


def _read_object(path: Path, label: str) -> dict[str, Any]:
    if path.is_symlink() or not path.is_file():
        raise BenchmarkError(f"{label} is missing or unsafe: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise BenchmarkError(f"cannot read {label}: {error}") from error
    if not isinstance(value, dict):
        raise BenchmarkError(f"{label} is not a JSON object")
    return value


def _canonical_hash(value: Mapping[str, Any]) -> str:
    return hashlib.sha256(canonical_json_bytes(value)).hexdigest()


def _file_identity(path: Path, label: str) -> dict[str, Any]:
    expanded = path.expanduser()
    if expanded.is_symlink() or not expanded.is_file():
        raise BenchmarkError(f"{label} is missing or unsafe: {expanded}")
    resolved = expanded.resolve()
    return {
        "path": str(resolved),
        "sha256": sha256_file(resolved),
        "size_bytes": resolved.stat().st_size,
    }


def _local_python_closure(entrypoints: Sequence[Path]) -> list[dict[str, Any]]:
    """Hash the statically discoverable local-Python import closure.

    Design-16 tools deliberately use sibling modules rather than a package.
    Resolving only imports that map to a ``.py`` file beside the importing
    script is therefore both deterministic and fail-closed for this runner.
    External/stdlib imports are runtime dependencies, not mutable controller
    source inputs, and are authenticated by the deployment/runtime records.
    """

    pending = [path.resolve() for path in entrypoints]
    observed: set[Path] = set()
    while pending:
        path = pending.pop()
        if path in observed:
            continue
        _file_identity(path, "Python controller dependency")
        observed.add(path)
        try:
            tree = ast.parse(path.read_text(encoding="utf-8"), filename=str(path))
        except (OSError, SyntaxError, UnicodeError) as error:
            raise BenchmarkError(f"cannot parse Python dependency {path}: {error}") from error
        candidates: set[str] = set()
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                candidates.update(alias.name.split(".", 1)[0] for alias in node.names)
            elif isinstance(node, ast.ImportFrom) and node.level == 0 and node.module:
                candidates.add(node.module.split(".", 1)[0])
        for module in sorted(candidates):
            sibling = path.parent / f"{module}.py"
            if sibling.is_file() and not sibling.is_symlink():
                pending.append(sibling.resolve())
    repository = ROOT.parents[1].resolve()
    records: list[dict[str, Any]] = []
    for path in sorted(observed):
        identity = _file_identity(path, "Python controller dependency")
        try:
            identity["repository_relative_path"] = path.relative_to(repository).as_posix()
        except ValueError:
            identity["repository_relative_path"] = None
        records.append(identity)
    return records


def _tree_identity(root: Path, expected: Any, *, label: str) -> dict[str, Any]:
    """Verify a frozen tree and return its compact, campaign-bound identity."""

    actual = tree_manifest(root)
    if not isinstance(expected, dict) or actual != expected:
        raise BenchmarkError(f"{label} snapshot tree mismatch")
    entries = actual.get("entries")
    tree_sha256 = actual.get("tree_sha256")
    if (
        not isinstance(entries, list)
        or not isinstance(tree_sha256, str)
        or HEX64.fullmatch(tree_sha256) is None
    ):
        raise BenchmarkError(f"{label} snapshot manifest is malformed")
    return {
        "root": str(root.resolve()),
        "tree_sha256": tree_sha256,
        "entry_count": len(entries),
        "manifest_sha256": _canonical_hash(actual),
    }


def _required_record_identity(
    deployment_record: Mapping[str, Any],
    *,
    path_field: str,
    sha256_field: str,
    expected_path: Path | None = None,
) -> dict[str, Any]:
    raw_path = deployment_record.get(path_field)
    expected_sha256 = deployment_record.get(sha256_field)
    if (
        not isinstance(raw_path, str)
        or not raw_path
        or not isinstance(expected_sha256, str)
        or HEX64.fullmatch(expected_sha256) is None
    ):
        raise BenchmarkError(f"deployment {path_field} identity is missing or malformed")
    path = Path(raw_path).expanduser()
    if not path.is_absolute() or path.is_symlink() or not path.is_file():
        raise BenchmarkError(f"deployment {path_field} is missing or unsafe")
    path = path.resolve()
    if expected_path is not None and path != expected_path.resolve():
        raise BenchmarkError(f"deployment {path_field} path changed")
    actual_sha256 = sha256_file(path)
    if actual_sha256 != expected_sha256:
        raise BenchmarkError(f"deployment {path_field} changed after installation")
    return {
        "path": str(path),
        "sha256": actual_sha256,
        "size_bytes": path.stat().st_size,
    }


def _required_binary_identity(
    deployment_record: Mapping[str, Any],
    *,
    path: Path,
    sha256_field: str,
    label: str,
) -> dict[str, Any]:
    if path.is_symlink() or not path.is_file():
        raise BenchmarkError(f"{label} is missing or unsafe")
    expected = deployment_record.get(sha256_field)
    actual = sha256_file(path)
    if (
        not isinstance(expected, str)
        or HEX64.fullmatch(expected) is None
        or actual != expected
    ):
        raise BenchmarkError(f"{label} changed after deployment")
    return {"path": str(path.resolve()), "sha256": actual, "size_bytes": path.stat().st_size}


def _verify_deployment_runtime(
    args: argparse.Namespace, *, deployment: Deployment | None = None
) -> dict[str, Any]:
    """Authenticate the actual installed runtime before any paid model call.

    Hashing the deployment JSON and its snapshot records is not sufficient: a
    mutable source, OLean, toolchain, or package tree can drift while those
    small records remain unchanged.  This is the tree-verification subset of
    ``PairController.doctor`` lifted to campaign admission.  The returned
    compact identities are embedded in ``campaign_core`` so every resume must
    observe the same already-verified installation.
    """

    resolved_deployment = deployment or load_deployment(args.deployment)
    deployment_path = args.deployment.expanduser().resolve()
    if resolved_deployment.path.resolve() != deployment_path:
        raise BenchmarkError("loaded deployment path does not match campaign request")
    deployment_record = _read_object(deployment_path, "deployment JSON")
    config = _read_object(args.config, "condition-order config")

    library_record_identity = _required_record_identity(
        deployment_record,
        path_field="library_snapshot_record",
        sha256_field="library_snapshot_record_sha256",
        expected_path=resolved_deployment.library_snapshot_record,
    )
    runtime_record_identity = _required_record_identity(
        deployment_record,
        path_field="runtime_snapshot_record",
        sha256_field="runtime_snapshot_record_sha256",
        expected_path=resolved_deployment.runtime_snapshot_record,
    )
    build_record_path = resolved_deployment.library_snapshot_record.parent / "build" / "build-record.json"
    build_record_identity = _required_record_identity(
        deployment_record,
        path_field="library_build_record",
        sha256_field="library_build_record_sha256",
        expected_path=build_record_path,
    )
    visible_runtime_identity = _required_record_identity(
        deployment_record,
        path_field="visible_system_runtime_record",
        sha256_field="visible_system_runtime_record_sha256",
    )

    library = _read_object(
        resolved_deployment.library_snapshot_record,
        "NumStability snapshot record",
    )
    expected_library_commit = config.get("numstability_commit")
    if (
        library.get("schema_version") != "numstability-formalization-snapshot-1"
        or not isinstance(expected_library_commit, str)
        or HEX40.fullmatch(expected_library_commit) is None
        or library.get("commit") != expected_library_commit
    ):
        raise BenchmarkError("deployed NumStability snapshot identity mismatch")
    source_root = resolved_deployment.library_source.parent
    build_root = resolved_deployment.library_snapshot_record.parent / "build"
    library_trees = {
        "source": _tree_identity(source_root, library.get("source"), label="NumStability source"),
        "olean": _tree_identity(
            resolved_deployment.library_olean,
            library.get("olean"),
            label="NumStability OLean",
        ),
        "build": _tree_identity(
            build_root,
            library.get("build"),
            label="NumStability setup build evidence",
        ),
    }

    runtime = _read_object(
        resolved_deployment.runtime_snapshot_record,
        "Lean/Mathlib snapshot record",
    )
    expected_toolchain = config.get("lean_toolchain")
    expected_mathlib_commit = config.get("mathlib_commit")
    if (
        runtime.get("schema_version") != "formalization-runtime-snapshot-1"
        or runtime.get("lean_toolchain") != expected_toolchain
        or runtime.get("mathlib_commit") != expected_mathlib_commit
    ):
        raise BenchmarkError("deployed Lean/Mathlib snapshot identity mismatch")
    runtime_trees = {
        "toolchain": _tree_identity(
            resolved_deployment.toolchain_root,
            runtime.get("toolchain"),
            label="Lean toolchain",
        ),
        "packages": _tree_identity(
            resolved_deployment.packages_root,
            runtime.get("packages"),
            label="Lean package closure",
        ),
    }
    treatment_absence = treatment_free_runtime_manifest(
        {
            "packages": resolved_deployment.packages_root,
            "toolchain": resolved_deployment.toolchain_root,
        }
    )
    if runtime.get("condition_n_treatment_absence") != treatment_absence:
        raise BenchmarkError(
            "condition N runtime treatment-absence record changed after deployment"
        )

    build_record = _read_object(build_record_path, "NumStability setup build record")
    validate_build_record(
        build_record,
        expected_source_commit=expected_library_commit,
        expected_mathlib_commit=expected_mathlib_commit,
        expected_toolchain=expected_toolchain,
        expected_tool_hashes={
            "lake_sha256": sha256_file(resolved_deployment.toolchain_root / "bin" / "lake"),
            "lean_sha256": sha256_file(resolved_deployment.toolchain_root / "bin" / "lean"),
            "gnu_time_sha256": sha256_file(Path("/usr/bin/time")),
        },
    )
    generated_output_tree = {
        "present": True,
        **file_tree_fingerprint(resolved_deployment.library_olean),
    }
    generated_olean = {
        "present": True,
        **file_tree_fingerprint(resolved_deployment.library_olean, suffix=".olean"),
    }
    if build_record.get("generated_output_tree") != generated_output_tree:
        raise BenchmarkError("deployed NumStability build output digest changed")
    if build_record.get("generated_olean") != generated_olean:
        raise BenchmarkError("deployed NumStability OLean inventory changed")
    for section_name, expected_name in (
        ("build_output", "build-output.log"),
        ("gnu_time", "gnu-time.txt"),
    ):
        section = build_record.get(section_name)
        artifact = build_root / expected_name
        if (
            not isinstance(section, Mapping)
            or section.get("relative_path") != expected_name
            or artifact.is_symlink()
            or not artifact.is_file()
            or section.get("sha256") != sha256_file(artifact)
            or section.get("bytes") != artifact.stat().st_size
        ):
            raise BenchmarkError(f"NumStability {section_name} artifact changed")

    binary_identities = {
        "codex": _required_binary_identity(
            deployment_record,
            path=resolved_deployment.codex_binary,
            sha256_field="codex_binary_sha256",
            label="Codex binary",
        ),
        "code_mode_host": _required_binary_identity(
            deployment_record,
            path=resolved_deployment.codex_binary.with_name("codex-code-mode-host"),
            sha256_field="code_mode_host_sha256",
            label="Codex Code Mode host",
        ),
        "bwrap": _required_binary_identity(
            deployment_record,
            path=resolved_deployment.bwrap_binary,
            sha256_field="bwrap_binary_sha256",
            label="Bubblewrap binary",
        ),
        "offline_shell": _required_binary_identity(
            deployment_record,
            path=resolved_deployment.offline_shell,
            sha256_field="offline_shell_sha256",
            label="offline shell",
        ),
    }

    identity: dict[str, Any] = {
        "schema_version": "formalization-design17-verified-deployment-runtime-1",
        "deployment": _file_identity(deployment_path, "deployment JSON"),
        "library_commit": expected_library_commit,
        "lean_toolchain": expected_toolchain,
        "mathlib_commit": expected_mathlib_commit,
        "records": {
            "library_snapshot": library_record_identity,
            "library_build": build_record_identity,
            "runtime_snapshot": runtime_record_identity,
            "visible_system_runtime": visible_runtime_identity,
        },
        "library_trees": library_trees,
        "runtime_trees": runtime_trees,
        "condition_n_treatment_absence_sha256": _canonical_hash(treatment_absence),
        "generated_output_tree": generated_output_tree,
        "generated_olean": generated_olean,
        "runtime_binaries": binary_identities,
    }
    identity["identity_sha256"] = _canonical_hash(identity)
    return identity


def _frozen_input_closure(args: argparse.Namespace) -> dict[str, Any]:
    """Resolve and hash every readily discoverable campaign input."""

    deployment_path = args.deployment.expanduser()
    deployment_identity = _file_identity(deployment_path, "deployment JSON")
    deployment = _read_object(deployment_path, "deployment JSON")
    if deployment.get("schema_version") != "formalization-deployment-1":
        raise BenchmarkError("campaign deployment has an unsupported schema")
    raw_pdf_root = deployment.get("pdf_root")
    if not isinstance(raw_pdf_root, str) or not raw_pdf_root:
        raise BenchmarkError("campaign deployment has no PDF root")
    pdf_root = Path(raw_pdf_root).expanduser()
    if pdf_root.is_symlink() or not pdf_root.is_dir():
        raise BenchmarkError("campaign deployment PDF root is missing or unsafe")
    pdf_root = pdf_root.resolve()

    prompt_names = (
        (
            "statement_formalizer.md",
            "design17_statement_addendum.md",
            "statement_repair.md",
        )
        if args.statement_only
        else ("formalizer.md", "design16_matched_addendum.md")
    )
    prompts = [
        _file_identity(ROOT / "prompts" / name, f"campaign prompt {name}")
        for name in prompt_names
    ]
    audit_protocol_files: list[dict[str, Any]] = []
    if args.statement_only:
        for directory, pattern in (
            (ROOT / "audit" / "prompts", "*.md"),
            (ROOT / "audit" / "schemas", "*.json"),
        ):
            paths = sorted(directory.glob(pattern))
            if not paths:
                raise BenchmarkError(f"statement audit protocol directory is empty: {directory}")
            audit_protocol_files.extend(
                _file_identity(path, "statement audit protocol input") for path in paths
            )
        audit_protocol_files.append(
            _file_identity(
                Path(__file__).with_name("declaration_dossier.lean"),
                "semantic dossier extractor",
            )
        )
        audit_protocol_files.append(
            _file_identity(
                Path(__file__).with_name("signature_interface.lean"),
                "packet signature-interface extractor",
            )
        )

    packets: list[dict[str, Any]] = []
    papers_by_name: dict[str, dict[str, Any]] = {}
    for task_id in EXPECTED_TASKS:
        packet_path = ROOT / "packets" / f"{task_id}.json"
        packet_identity = _file_identity(packet_path, f"{task_id} source packet")
        packet = _read_object(packet_path, f"{task_id} source packet")
        paper_ref = packet.get("paper_pdf")
        if packet.get("task_id") != task_id or not isinstance(paper_ref, dict):
            raise BenchmarkError(f"{task_id} source packet identity is malformed")
        basename = paper_ref.get("path_basename")
        expected_pdf_sha = paper_ref.get("sha256")
        if (
            not isinstance(basename, str)
            or not basename
            or Path(basename).name != basename
            or not isinstance(expected_pdf_sha, str)
            or HEX64.fullmatch(expected_pdf_sha) is None
        ):
            raise BenchmarkError(f"{task_id} source PDF reference is malformed")
        paper_identity = _file_identity(pdf_root / basename, f"{task_id} source PDF")
        if paper_identity["sha256"] != expected_pdf_sha:
            raise BenchmarkError(f"{task_id} source PDF hash does not match its packet")
        existing = papers_by_name.get(basename)
        if existing is not None and existing != paper_identity:
            raise BenchmarkError(f"inconsistent repeated source PDF identity: {basename}")
        papers_by_name[basename] = paper_identity
        overlay_path = ROOT / "design16" / "contracts" / f"{task_id}.json"
        overlay = (
            {"present": True, **_file_identity(overlay_path, f"{task_id} contract overlay")}
            if overlay_path.exists() or overlay_path.is_symlink()
            else {"present": False, "expected_path": str(overlay_path.resolve())}
        )
        packets.append(
            {
                "task_id": task_id,
                "packet": packet_identity,
                "paper_basename": basename,
                "paper_sha256": expected_pdf_sha,
                "contract_overlay": overlay,
            }
        )

    deployment_artifacts: dict[str, Any] = {}
    for key in ("library_snapshot_record", "runtime_snapshot_record"):
        raw = deployment.get(key)
        if not isinstance(raw, str) or not raw:
            raise BenchmarkError(f"deployment input {key} is missing")
        deployment_artifacts[key] = _file_identity(Path(raw), f"deployment {key}")
    raw_treatment_atlas = deployment.get("library_atlas")
    if not isinstance(raw_treatment_atlas, str) or not raw_treatment_atlas:
        raise BenchmarkError("deployment library_atlas is missing")
    deployment_artifacts["library_atlas"] = _atlas_identity(
        Path(raw_treatment_atlas).expanduser()
    )

    verified_deployment_runtime = _verify_deployment_runtime(args)
    closure: dict[str, Any] = {
        "deployment": deployment_identity,
        "deployment_artifacts": deployment_artifacts,
        "verified_deployment_runtime": verified_deployment_runtime,
        "config": _file_identity(args.config, "condition-order config"),
        "readiness": _file_identity(args.readiness, "Design-16 readiness screen"),
        "prompts": prompts,
        "audit_protocol_files": audit_protocol_files,
        "task_packets": packets,
        "source_pdfs": [papers_by_name[name] for name in sorted(papers_by_name)],
        "python_modules": _local_python_closure(
            [Path(__file__).resolve(), args.runner.expanduser().resolve()]
        ),
    }
    closure["closure_sha256"] = _canonical_hash(closure)
    return closure


def _write_once(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(value, indent=2, sort_keys=True) + "\n"
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o400)
    try:
        with os.fdopen(descriptor, "w", encoding="utf-8", newline="") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
    except BaseException:
        if path.exists() and not path.is_symlink():
            path.unlink()
        raise


def _append_record(path: Path, payload: Mapping[str, Any]) -> dict[str, Any]:
    records = _read_journal(path) if path.exists() else []
    record = dict(payload)
    record["sequence"] = len(records) + 1
    record["previous_record_sha256"] = (
        records[-1]["record_sha256"] if records else None
    )
    digest_input = dict(record)
    record["record_sha256"] = _canonical_hash(digest_input)
    path.parent.mkdir(parents=True, exist_ok=True)
    # Journals are append-only by protocol, but must remain owner-writable for
    # later records and resumed campaigns.
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_APPEND, 0o600)
    with os.fdopen(descriptor, "ab", closefd=True) as stream:
        stream.write(canonical_json_bytes(record))
        stream.flush()
        os.fsync(stream.fileno())
    return record


def _read_journal(path: Path) -> list[dict[str, Any]]:
    if path.is_symlink() or not path.is_file():
        raise BenchmarkError(f"journal is missing or unsafe: {path}")
    records: list[dict[str, Any]] = []
    previous: str | None = None
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        try:
            value = json.loads(line)
        except json.JSONDecodeError as error:
            raise BenchmarkError(f"malformed journal record {path}:{line_number}") from error
        if not isinstance(value, dict):
            raise BenchmarkError(f"non-object journal record {path}:{line_number}")
        if value.get("sequence") != line_number:
            raise BenchmarkError(f"non-contiguous journal sequence {path}:{line_number}")
        if value.get("previous_record_sha256") != previous:
            raise BenchmarkError(f"broken journal chain {path}:{line_number}")
        observed = value.get("record_sha256")
        if not isinstance(observed, str) or HEX64.fullmatch(observed) is None:
            raise BenchmarkError(f"invalid journal digest {path}:{line_number}")
        unhashed = dict(value)
        unhashed.pop("record_sha256")
        if _canonical_hash(unhashed) != observed:
            raise BenchmarkError(f"stale journal digest {path}:{line_number}")
        previous = observed
        records.append(value)
    return records


def _atlas_identity(root: Path) -> dict[str, Any]:
    if root.is_symlink() or not root.is_dir():
        raise BenchmarkError(f"Mathlib atlas is missing or unsafe: {root}")
    metadata_path = root / "atlas.json"
    declarations_path = root / "declarations.jsonl"
    metadata = _read_object(metadata_path, "Mathlib atlas metadata")
    if declarations_path.is_symlink() or not declarations_path.is_file():
        raise BenchmarkError("Mathlib declarations atlas is missing or unsafe")
    declarations_sha256 = sha256_file(declarations_path)
    if (
        metadata.get("schema_version") != "numstability-library-atlas-3"
        or not isinstance(metadata.get("declaration_count"), int)
        or metadata["declaration_count"] < 1
        or metadata.get("declarations_sha256") != declarations_sha256
    ):
        raise BenchmarkError("Mathlib atlas identity is malformed or stale")
    return {
        "path": str(root.resolve()),
        "metadata_sha256": sha256_file(metadata_path),
        "declarations_sha256": declarations_sha256,
        "schema_version": metadata.get("schema_version"),
        "declaration_count": metadata.get("declaration_count"),
    }


def _runner_identity(runner: Path, commit: str, expected_sha256: str) -> dict[str, Any]:
    if HEX40.fullmatch(commit) is None:
        raise BenchmarkError("runner commit must be a full lowercase 40-digit Git SHA")
    if HEX64.fullmatch(expected_sha256) is None:
        raise BenchmarkError("runner SHA-256 must be 64 lowercase hexadecimal digits")
    if runner.is_symlink() or not runner.is_file():
        raise BenchmarkError(f"runner is missing or unsafe: {runner}")
    runner = runner.resolve()
    if sha256_file(runner) != expected_sha256:
        raise BenchmarkError("working runner does not match the frozen SHA-256")
    try:
        repository = Path(
            subprocess.run(
                ["git", "-C", str(runner.parent), "rev-parse", "--show-toplevel"],
                check=True,
                capture_output=True,
                text=True,
            ).stdout.strip()
        ).resolve()
        canonical_commit = subprocess.run(
            ["git", "-C", str(repository), "rev-parse", f"{commit}^{{commit}}"],
            check=True,
            capture_output=True,
            text=True,
        ).stdout.strip()
        relative = runner.relative_to(repository).as_posix()
        committed_bytes = subprocess.run(
            ["git", "-C", str(repository), "show", f"{commit}:{relative}"],
            check=True,
            capture_output=True,
        ).stdout
    except (subprocess.SubprocessError, ValueError) as error:
        raise BenchmarkError(f"cannot authenticate frozen runner commit: {error}") from error
    if canonical_commit != commit:
        raise BenchmarkError("runner commit is not canonical")
    if hashlib.sha256(committed_bytes).hexdigest() != expected_sha256:
        raise BenchmarkError("runner bytes at the frozen commit do not match SHA-256")
    return {
        "path": str(runner),
        "repository": str(repository),
        "repository_relative_path": relative,
        "commit": commit,
        "sha256": expected_sha256,
    }


def _stratum(decision: str) -> str:
    if decision.startswith("INCLUDE_PRIMARY_ENGINEERING"):
        return "primary_engineering"
    if decision == "NEGATIVE_CONTROL_ONLY":
        return "negative_control"
    return "excluded_collision_or_router_error"


def load_plan(config_path: Path, readiness_path: Path) -> list[dict[str, Any]]:
    config = _read_object(config_path, "frozen condition-order config")
    readiness = _read_object(readiness_path, "Design-16 readiness screen")
    if tuple(readiness.get("task_set", ())) != EXPECTED_TASKS:
        raise BenchmarkError("readiness screen does not contain the exact Higham-13 order")
    raw_tasks = readiness.get("tasks")
    if not isinstance(raw_tasks, list):
        raise BenchmarkError("readiness screen lacks task records")
    by_id = {
        value.get("task_id"): value
        for value in raw_tasks
        if isinstance(value, dict) and isinstance(value.get("task_id"), str)
    }
    orders = config.get("condition_order")
    if not isinstance(orders, dict):
        raise BenchmarkError("config lacks condition_order")
    plan: list[dict[str, Any]] = []
    observed_strata: dict[str, list[str]] = {name: [] for name in EXPECTED_STRATA}
    previous_order: tuple[str, str] | None = None
    translation = {"N": "R0", "L": "R1"}
    for task_id in EXPECTED_TASKS:
        task = by_id.get(task_id)
        if not isinstance(task, dict) or not isinstance(task.get("decision"), str):
            raise BenchmarkError(f"readiness task record is missing: {task_id}")
        raw_order = orders.get(task_id)
        if not isinstance(raw_order, list) or len(raw_order) != 2 or set(raw_order) != {"N", "L"}:
            raise BenchmarkError(f"invalid frozen condition order for {task_id}")
        matched_order = tuple(translation[value] for value in raw_order)
        if previous_order == matched_order:
            raise BenchmarkError("Higham-13 frozen condition orders do not alternate")
        previous_order = matched_order
        stratum = _stratum(task["decision"])
        observed_strata[stratum].append(task_id)
        plan.append(
            {
                "task_id": task_id,
                "condition_order": list(matched_order),
                "legacy_condition_order": list(raw_order),
                "stratum": stratum,
                "readiness_decision": task["decision"],
                "coverage_stratum": task.get("coverage_stratum"),
            }
        )
    if {name: tuple(ids) for name, ids in observed_strata.items()} != EXPECTED_STRATA:
        raise BenchmarkError("readiness strata no longer match the frozen 2/6/5 partition")
    return plan


def _activate_hardware_envelope(args: argparse.Namespace) -> dict[str, Any] | None:
    if not args.enforce_titan_envelope:
        return None
    command_cgroup = prepare_command_cgroup()
    os.environ[COMMAND_CGROUP_VARIABLE] = str(command_cgroup)
    snapshot = snapshot_hardware(strict=True)
    return {
        "identity": frozen_hardware_identity(snapshot),
        "logical_cpus": EXPECTED_LOGICAL_CPUS,
        "memory_bytes": EXPECTED_MEMORY_BYTES,
        "tasks_max": EXPECTED_TASKS_MAX,
        "swap_enabled": False,
        "generated_command_cgroup": {
            "memory_bytes": 24 * 1024 * 1024 * 1024,
            "tasks_max": 384,
            "swap_enabled": False,
        },
    }


def _manifest_core(
    args: argparse.Namespace, *, hardware_envelope: Mapping[str, Any] | None
) -> dict[str, Any]:
    if args.model != "gpt-5.6-sol" or args.reasoning_effort != "xhigh":
        raise BenchmarkError("Design-16 campaign formalizer is frozen to gpt-5.6-sol xhigh")
    if args.statement_only and (
        args.audit_model != "gpt-6-astra"
        or args.audit_reasoning_effort != "high"
        or args.submission_limit != 4
    ):
        raise BenchmarkError(
            "Design-17 freezes gpt-6-astra high auditors and four submissions"
        )
    positive_limits = {
        "time limit": args.time_limit_seconds,
        "validation timeout": args.validation_timeout_seconds,
        "root limit": args.root_limit,
        "dependency limit": args.dependency_limit,
        "packet-byte limit": args.maximum_packet_bytes,
    }
    if any(not isinstance(value, int) or value < 1 for value in positive_limits.values()):
        raise BenchmarkError("all campaign limits must be positive integers")
    if (
        not isinstance(args.audit_timeout_seconds, (int, float))
        or isinstance(args.audit_timeout_seconds, bool)
        or args.audit_timeout_seconds <= 0
        or not isinstance(args.audit_infrastructure_retries, int)
        or args.audit_infrastructure_retries < 0
        or not isinstance(args.submission_limit, int)
        or args.submission_limit < 1
    ):
        raise BenchmarkError("audit/repair limits are malformed")
    plan = load_plan(args.config, args.readiness)
    input_closure = _frozen_input_closure(args)
    verified_runtime = input_closure.get("verified_deployment_runtime")
    if verified_runtime is None:
        if args.controller_commit is not None:
            raise BenchmarkError(
                "measured campaign input closure lacks verified deployment runtime identity"
            )
    elif (
        not isinstance(verified_runtime, dict)
        or verified_runtime.get("schema_version")
        != "formalization-design17-verified-deployment-runtime-1"
        or verified_runtime.get("identity_sha256")
        != _canonical_hash(
            {
                key: value
                for key, value in verified_runtime.items()
                if key != "identity_sha256"
            }
        )
    ):
        raise BenchmarkError("verified deployment runtime identity is malformed or stale")
    core = {
        "schema_version": SCHEMA,
        "scientific_status": SCIENTIFIC_STATUS,
        "tasks_run_sequentially": True,
        "pooled_effect_estimate_forbidden": True,
        "plan": plan,
        "campaign_controller": (
            _runner_identity(
                Path(__file__).resolve(),
                args.controller_commit,
                args.controller_sha256,
            )
            if args.controller_commit is not None
            else {"test_mode_unfrozen": True}
        ),
        "runner": _runner_identity(args.runner, args.runner_commit, args.runner_sha256),
        "mathlib_atlas": _atlas_identity(args.mathlib_atlas.expanduser()),
        "config": {
            "path": str(args.config.resolve()),
            "sha256": sha256_file(args.config),
        },
        "readiness": {
            "path": str(args.readiness.resolve()),
            "sha256": sha256_file(args.readiness),
        },
        "deployment_path": str(args.deployment.resolve()),
        "verified_deployment_runtime": verified_runtime,
        "frozen_input_closure": input_closure,
        "formalizer": {
            "model": args.model,
            "reasoning_effort": args.reasoning_effort,
            "time_limit_seconds": args.time_limit_seconds,
            "validation_timeout_seconds": args.validation_timeout_seconds,
            "benchmark_object": (
                "FORMALIZED_STATEMENT_ONLY"
                if args.statement_only
                else "FORMALIZED_STATEMENT_AND_COMPLETE_PROOF"
            ),
            "source_contract": (
                "statement-only-single-target-sorry"
                if args.statement_only
                else "complete-kernel-checked-proof"
            ),
            "submission_limit": args.submission_limit,
            "audit_model": args.audit_model,
            "audit_reasoning_effort": args.audit_reasoning_effort,
            "audit_timeout_seconds": args.audit_timeout_seconds,
            "audit_infrastructure_retries": args.audit_infrastructure_retries,
        },
        "hardware_envelope": (
            dict(hardware_envelope)
            if hardware_envelope is not None
            else {"enforced": False}
        ),
        "retrieval": {
            "root_limit": args.root_limit,
            "dependency_limit": args.dependency_limit,
            "maximum_packet_bytes": args.maximum_packet_bytes,
        },
    }
    return core


def _load_or_create_manifest(root: Path, core: Mapping[str, Any]) -> dict[str, Any]:
    path = root / "campaign-manifest.json"
    identity = _canonical_hash(core)
    input_closure = core.get("frozen_input_closure")
    if not isinstance(input_closure, dict):
        raise BenchmarkError("campaign core lacks a frozen input closure")
    unsigned_closure = dict(input_closure)
    observed_closure_hash = unsigned_closure.pop("closure_sha256", None)
    if observed_closure_hash != _canonical_hash(unsigned_closure):
        raise BenchmarkError("campaign frozen input closure self-hash is stale")
    if path.exists() or path.is_symlink():
        manifest = _read_object(path, "campaign manifest")
        observed_core = manifest.get("campaign_core")
        unsigned = dict(manifest)
        observed_payload_hash = unsigned.pop("manifest_payload_sha256", None)
        nonce = manifest.get("campaign_nonce")
        if (
            observed_core != core
            or manifest.get("campaign_identity_sha256") != identity
            or not isinstance(nonce, str)
            or HEX64.fullmatch(nonce) is None
            or observed_payload_hash != _canonical_hash(unsigned)
        ):
            raise BenchmarkError("campaign manifest does not match the requested frozen inputs")
        return manifest
    manifest = {
        "campaign_core": dict(core),
        "campaign_identity_sha256": identity,
        "campaign_nonce": secrets.token_hex(32),
        "created_at_utc": utc_now(),
    }
    manifest["manifest_payload_sha256"] = _canonical_hash(manifest)
    _write_once(path, manifest)
    return manifest


def _terminal_by_task(events: Sequence[Mapping[str, Any]]) -> dict[str, Mapping[str, Any]]:
    terminals: dict[str, Mapping[str, Any]] = {}
    for event in events:
        if event.get("event_type") in TERMINAL_EVENT_TYPES:
            task_id = event.get("task_id")
            if task_id not in EXPECTED_TASKS or task_id in terminals:
                raise BenchmarkError("duplicate or malformed terminal task event")
            terminals[task_id] = event
    return terminals


def _summary_payload(
    *,
    manifest: Mapping[str, Any],
    events: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    plan = manifest["campaign_core"]["plan"]
    terminals = _terminal_by_task(events)
    strata: dict[str, Any] = {}
    for stratum in EXPECTED_STRATA:
        entries = [item for item in plan if item["stratum"] == stratum]
        audit_pending = [
            item["task_id"]
            for item in entries
            if terminals.get(item["task_id"], {}).get("outcome") == AUDIT_PENDING
        ]
        audited_faithful = [
            item["task_id"]
            for item in entries
            if terminals.get(item["task_id"], {}).get("outcome") == AUDITED_FAITHFUL
        ]
        audited_ineligible = [
            item["task_id"]
            for item in entries
            if terminals.get(item["task_id"], {}).get("outcome") == AUDITED_INELIGIBLE
        ]
        incidents = [
            item["task_id"]
            for item in entries
            if terminals.get(item["task_id"], {}).get("outcome")
            in INCIDENT_OUTCOMES
        ]
        strata[stratum] = {
            "planned_task_ids": [item["task_id"] for item in entries],
            # Compilation/integrity validation is not a scientific completion.
            "completed_task_ids": [],
            "formalization_complete_audit_pending_task_ids": audit_pending,
            "audited_faithful_pair_task_ids": audited_faithful,
            "audited_ineligible_pair_task_ids": audited_ineligible,
            "incident_task_ids": incidents,
            "pending_task_ids": [
                item["task_id"] for item in entries if item["task_id"] not in terminals
            ],
            "completed_count": 0,
            "formalization_complete_audit_pending_count": len(audit_pending),
            "audited_faithful_pair_count": len(audited_faithful),
            "audited_ineligible_pair_count": len(audited_ineligible),
            "incident_count": len(incidents),
            "pending_count": (
                len(entries)
                - len(audit_pending)
                - len(audited_faithful)
                - len(audited_ineligible)
                - len(incidents)
            ),
            "comparison": "SEPARATE_STRATUM_ONLY",
        }
    return {
        "schema_version": SCHEMA,
        "scientific_status": SCIENTIFIC_STATUS,
        "campaign_identity_sha256": manifest["campaign_identity_sha256"],
        "recorded_at_utc": utc_now(),
        "latest_state_sequence": len(events),
        "latest_state_sha256": events[-1]["record_sha256"] if events else None,
        "strata": strata,
        "pooled_effect_estimate": None,
        "pooling_policy": (
            "primary, negative-control, and excluded/collision strata "
            "must not be pooled"
        ),
    }


def _record_event(root: Path, manifest: Mapping[str, Any], event: Mapping[str, Any]) -> None:
    state_path = root / "campaign-state.jsonl"
    recorded = _append_record(
        state_path,
        {**event, "recorded_at_utc": utc_now(), "schema_version": SCHEMA},
    )
    events = _read_journal(state_path)
    if events[-1]["record_sha256"] != recorded["record_sha256"]:
        raise BenchmarkError("state journal append was not durable")
    _sync_summaries(root, manifest, events)


def _sync_summaries(
    root: Path,
    manifest: Mapping[str, Any],
    events: Sequence[Mapping[str, Any]],
) -> None:
    """Append missing snapshots after a crash between state and summary writes."""

    summary_path = root / "campaign-summary.jsonl"
    summaries = _read_journal(summary_path) if summary_path.exists() else []
    if len(summaries) > len(events):
        raise BenchmarkError("summary journal is ahead of the state journal")
    for index, summary in enumerate(summaries, 1):
        if (
            summary.get("latest_state_sequence") != index
            or summary.get("latest_state_sha256") != events[index - 1].get("record_sha256")
        ):
            raise BenchmarkError("summary journal does not correspond to state history")
    for index in range(len(summaries) + 1, len(events) + 1):
        _append_record(
            summary_path,
            _summary_payload(manifest=manifest, events=events[:index]),
        )


def _pair_artifact_closure(pair_root: Path) -> list[dict[str, Any]]:
    if pair_root.is_symlink() or not pair_root.is_dir():
        raise BenchmarkError("matched pair root is missing or unsafe")
    records: list[dict[str, Any]] = []
    for path in sorted(pair_root.rglob("*")):
        if path.is_symlink():
            raise BenchmarkError(f"matched pair artifact may not be a symlink: {path}")
        if path.is_dir():
            continue
        if not path.is_file():
            raise BenchmarkError(f"matched pair contains a non-regular artifact: {path}")
        records.append(
            {
                "relative_path": path.relative_to(pair_root).as_posix(),
                "sha256": sha256_file(path),
                "size_bytes": path.stat().st_size,
            }
        )
    if not records:
        raise BenchmarkError("matched pair artifact closure is empty")
    return records


def _inspect_pair(
    pair_root: Path,
    *,
    task_id: str,
    condition_order: Sequence[str],
    statement_only: bool,
    require_titan_envelope: bool,
) -> tuple[str, dict[str, Any]]:
    report_path = pair_root / "pair-report.json"
    if report_path.is_symlink() or not report_path.is_file():
        return "INCIDENT", {"reason": "pair report is absent"}
    report = _read_object(report_path, "matched pair report")
    if report.get("task_id") != task_id:
        return "INCIDENT", {"reason": "pair report task ID mismatch"}
    expected_object = (
        "FORMALIZED_STATEMENT_ONLY"
        if statement_only
        else "FORMALIZED_STATEMENT_AND_COMPLETE_PROOF"
    )
    expected_contract = (
        "statement-only-single-target-sorry"
        if statement_only
        else "complete-kernel-checked-proof"
    )
    status = report.get("pair_status")
    expected_pair_faithfulness = (
        "BOTH_FAITHFUL"
        if status == AUDITED_FAITHFUL
        else "PAIR_NOT_BOTH_FAITHFUL"
        if status == AUDITED_INELIGIBLE
        else "NOT_DECIDED_INFRASTRUCTURE"
        if status == "PAIR_INCIDENT" and statement_only
        else "NOT_AUDITED"
    )
    if (
        report.get("condition_order") != list(condition_order)
        or report.get("conditions_run_sequentially") is not True
        or report.get("benchmark_object") != expected_object
        or report.get("source_contract") != expected_contract
        or report.get("faithfulness_status") != expected_pair_faithfulness
    ):
        return "INCIDENT", {"reason": "pair report mode/order contract mismatch"}
    details = {
        "pair_status": status,
        "pair_report_sha256": sha256_file(report_path),
        "pair_report_path": str(report_path),
    }
    accepted_status = (
        status in {AUDITED_FAITHFUL, AUDITED_INELIGIBLE, "PAIR_INCIDENT"}
        if statement_only
        else status in {"FORMALIZATION_FROZEN_PENDING_AUDIT", "COMPILED_UNAUDITED"}
    )
    if not accepted_status:
        details["reason"] = "pair is not frozen and pending independent audit"
        return "INCIDENT", details

    condition_reports = report.get("condition_reports")
    if not isinstance(condition_reports, dict) or set(condition_reports) != {"R0", "R1"}:
        details["reason"] = "pair does not contain exactly R0 and R1 reports"
        return "INCIDENT", details
    prompt_path = pair_root / "prompt.txt"
    if (
        prompt_path.is_symlink()
        or not prompt_path.is_file()
        or sha256_file(prompt_path) != report.get("prompt_sha256")
    ):
        details["reason"] = "pair prompt is absent, unsafe, or hash-mismatched"
        return "INCIDENT", details

    source_packet_hashes: set[str] = set()
    source_pdf_hashes: set[str] = set()
    source_task_hashes: set[str] = set()
    for condition in ("R0", "R1"):
        condition_root = pair_root / condition
        condition_report_path = condition_root / "report.json"
        if condition_report_path.is_symlink() or not condition_report_path.is_file():
            details["reason"] = f"{condition} report is absent or unsafe"
            return "INCIDENT", details
        condition_report = _read_object(condition_report_path, f"{condition} report")
        if condition_reports.get(condition) != condition_report:
            details["reason"] = f"{condition} embedded/on-disk reports disagree"
            return "INCIDENT", details
        common_contract_pass = (
            condition_report.get("task_id") == task_id
            and condition_report.get("condition") == condition
            and condition_report.get("benchmark_object") == expected_object
            and condition_report.get("source_contract") == expected_contract
        )
        if statement_only:
            accepted_condition = condition_report.get("result_status") == "ACCEPTED_FAITHFUL"
            condition_incident = condition_report.get("result_status") in {
                "FORMALIZER_INCIDENT",
                "VALIDATION_INFRASTRUCTURE_INCIDENT",
                "AUDIT_PREPARATION_INCIDENT",
                "AUDIT_SYSTEM_INCIDENT",
            }
            condition_contract_pass = (
                condition_report.get("faithfulness_status")
                == (
                    "FAITHFUL"
                    if accepted_condition
                    else "NOT_DECIDED_INFRASTRUCTURE"
                    if condition_incident
                    else "UNFAITHFUL_OR_FAILED"
                )
                and isinstance(condition_report.get("attempts"), list)
                and bool(condition_report["attempts"])
                and condition_report.get("submission_count")
                == len(condition_report["attempts"])
            )
        else:
            accepted_condition = False
            condition_contract_pass = (
                condition_report.get("faithfulness_status") == "NOT_AUDITED"
                and condition_report.get("result_status")
                == "COMPILED_AND_INTEGRITY_VALIDATED"
                and condition_report.get("validation_pass") is True
                and condition_report.get("prompt_sha256")
                == report.get("prompt_sha256")
            )
        if not common_contract_pass or not condition_contract_pass:
            details["reason"] = f"{condition} report contract mismatch"
            return "INCIDENT", details
        if require_titan_envelope and (
            condition_report.get("hardware_envelope_required") is not True
            or not isinstance(condition_report.get("hardware_snapshot"), dict)
            or (
                not statement_only
                and not isinstance(condition_report.get("hardware_snapshot_after"), dict)
            )
        ):
            details["reason"] = f"{condition} lacks the required Titan hardware evidence"
            return "INCIDENT", details

        candidate_record = condition_report.get("candidate")
        if isinstance(candidate_record, dict):
            recorded_path = candidate_record.get("path")
            if not isinstance(recorded_path, str):
                details["reason"] = f"{condition} frozen candidate path is malformed"
                return "INCIDENT", details
            candidate_path = Path(recorded_path)
            if not candidate_path.is_absolute():
                candidate_path = (pair_root / candidate_path).resolve()
            else:
                candidate_path = candidate_path.resolve()
            submissions_root = (condition_root / "submissions").resolve()
            expected_proof_candidate = (
                condition_root / "submissions" / "01" / "Candidate.lean"
            ).resolve()
            if (
                candidate_path.name != "Candidate.lean"
                or (
                    statement_only
                    and submissions_root not in candidate_path.parents
                )
                or (not statement_only and candidate_path != expected_proof_candidate)
            ):
                details["reason"] = f"{condition} frozen candidate path is unexpected"
                return "INCIDENT", details
        else:
            # Compatibility for already-produced proof-inclusive diagnostics.
            candidate_path = condition_root / "workspace" / "Candidate.lean"
        if (
            candidate_path.is_symlink()
            or not candidate_path.is_file()
            or sha256_file(candidate_path) != condition_report.get("candidate_sha256")
        ):
            details["reason"] = f"{condition} candidate is absent, unsafe, or stale"
            return "INCIDENT", details
        for relative, field in (
            (Path("composition-packet.json"), "composition_packet_sha256"),
            (Path("workspace") / "LIBRARY_API.md", "library_api_sha256"),
        ):
            artifact = condition_root / relative
            if (
                artifact.is_symlink()
                or not artifact.is_file()
                or sha256_file(artifact) != condition_report.get(field)
            ):
                details["reason"] = f"{condition} {relative} is absent, unsafe, or stale"
                return "INCIDENT", details
        if statement_only:
            attempts = condition_report["attempts"]
            for attempt_number, attempt in enumerate(attempts, 1):
                if not isinstance(attempt, dict) or attempt.get("attempt") != attempt_number:
                    details["reason"] = f"{condition} attempt sequence is malformed"
                    return "INCIDENT", details
                attempt_root = condition_root / "submissions" / f"{attempt_number:02d}"
                attempt_candidate = attempt_root / "Candidate.lean"
                attempt_validation = attempt_root / "validation.json"
                attempt_candidate_record = attempt.get("candidate")
                if (
                    not isinstance(attempt_candidate_record, dict)
                    or attempt_candidate.is_symlink()
                    or not attempt_candidate.is_file()
                    or sha256_file(attempt_candidate)
                    != attempt_candidate_record.get("sha256")
                    or attempt_validation.is_symlink()
                    or not attempt_validation.is_file()
                    or sha256_file(attempt_validation) != attempt.get("validation_sha256")
                    or not isinstance(attempt.get("hardware_after"), dict)
                ):
                    details["reason"] = f"{condition} attempt artifact closure is stale"
                    return "INCIDENT", details
            if condition_report.get("candidate") != attempts[-1].get("candidate"):
                details["reason"] = f"{condition} final candidate is not the final submission"
                return "INCIDENT", details
            if accepted_condition and attempts[-1].get("status") != "ACCEPTED_FAITHFUL":
                details["reason"] = f"{condition} accepted status lacks an accepted audit"
                return "INCIDENT", details
        else:
            validation_path = condition_root / "validation.json"
            if validation_path.is_symlink() or not validation_path.is_file():
                details["reason"] = f"{condition} validation record is absent or unsafe"
                return "INCIDENT", details
            validation = _read_object(validation_path, f"{condition} validation record")
            if validation.get("pass") is not True:
                details["reason"] = f"{condition} validation record is not passing"
                return "INCIDENT", details
        source_paper = condition_root / "workspace" / "source" / "paper.pdf"
        source_task = condition_root / "workspace" / "source" / "task.md"
        if any(
            path.is_symlink() or not path.is_file()
            for path in (source_paper, source_task)
        ):
            details["reason"] = f"{condition} source artifacts are absent or unsafe"
            return "INCIDENT", details
        if statement_only:
            if condition_report.get("source_pdf_sha256") != sha256_file(source_paper):
                details["reason"] = f"{condition} source PDF report hash is stale"
                return "INCIDENT", details
            if condition_report.get("staged_task_sha256") != sha256_file(source_task):
                details["reason"] = f"{condition} staged task report hash is stale"
                return "INCIDENT", details
        else:
            source_packet_hashes.add(str(condition_report.get("source_packet_sha256")))
        source_pdf_hashes.add(sha256_file(source_paper))
        source_task_hashes.add(sha256_file(source_task))
    if (
        (not statement_only and source_packet_hashes != {str(report.get("source_packet_sha256"))})
        or source_pdf_hashes != {str(report.get("source_pdf_sha256"))}
        or len(source_task_hashes) != 1
    ):
        details["reason"] = "matched condition source identities disagree"
        return "INCIDENT", details
    details["pair_artifact_closure"] = _pair_artifact_closure(pair_root)
    details["pair_artifact_closure_sha256"] = _canonical_hash(
        {"files": details["pair_artifact_closure"]}
    )
    if statement_only:
        accepted_conditions = {
            condition
            for condition, condition_report in condition_reports.items()
            if condition_report.get("result_status") == "ACCEPTED_FAITHFUL"
        }
        if status == AUDITED_FAITHFUL and accepted_conditions != {"R0", "R1"}:
            details["reason"] = "faithful pair status disagrees with condition audits"
            return "INCIDENT", details
        if status == AUDITED_INELIGIBLE and accepted_conditions == {"R0", "R1"}:
            details["reason"] = "ineligible pair status disagrees with condition audits"
            return "INCIDENT", details
        if status == "PAIR_INCIDENT":
            details["reason"] = "statement pair contains an infrastructure incident"
            return ATTESTED_PAIR_INCIDENT, details
        return status, details
    return AUDIT_PENDING, details


def _attest_pair(
    *,
    task_root: Path,
    manifest: Mapping[str, Any],
    pair_nonce: str,
    item: Mapping[str, Any],
    details: Mapping[str, Any],
    runner_return_code: int,
) -> dict[str, Any]:
    stdout_path = task_root / "runner.stdout.log"
    stderr_path = task_root / "runner.stderr.log"
    attestation = {
        "schema_version": "formalization-design16-campaign-pair-attestation-1",
        "campaign_identity_sha256": manifest["campaign_identity_sha256"],
        "campaign_nonce": manifest["campaign_nonce"],
        "pair_nonce": pair_nonce,
        "task_id": item["task_id"],
        "condition_order": list(item["condition_order"]),
        "benchmark_object": manifest["campaign_core"]["formalizer"]["benchmark_object"],
        "source_contract": manifest["campaign_core"]["formalizer"]["source_contract"],
        "pair_status": details["pair_status"],
        "pair_report_sha256": details["pair_report_sha256"],
        "pair_artifact_closure": details["pair_artifact_closure"],
        "pair_artifact_closure_sha256": details["pair_artifact_closure_sha256"],
        "runner_return_code": runner_return_code,
        "runner_stdout_sha256": sha256_file(stdout_path),
        "runner_stderr_sha256": sha256_file(stderr_path),
        "created_at_utc": utc_now(),
    }
    path = task_root / PAIR_ATTESTATION
    _write_once(path, attestation)
    return attestation


def _verify_pair_attestation(
    *,
    task_root: Path,
    manifest: Mapping[str, Any],
    pair_nonce: str,
    item: Mapping[str, Any],
    details: Mapping[str, Any],
) -> dict[str, Any]:
    path = task_root / PAIR_ATTESTATION
    if path.is_symlink() or not path.is_file():
        raise BenchmarkError("paid pair has no campaign attestation; refusing recovery")
    attestation = _read_object(path, "campaign pair attestation")
    expected = {
        "campaign_identity_sha256": manifest["campaign_identity_sha256"],
        "campaign_nonce": manifest["campaign_nonce"],
        "pair_nonce": pair_nonce,
        "task_id": item["task_id"],
        "condition_order": list(item["condition_order"]),
        "benchmark_object": manifest["campaign_core"]["formalizer"]["benchmark_object"],
        "source_contract": manifest["campaign_core"]["formalizer"]["source_contract"],
        "pair_status": details["pair_status"],
        "pair_report_sha256": details["pair_report_sha256"],
        "pair_artifact_closure": details["pair_artifact_closure"],
        "pair_artifact_closure_sha256": details["pair_artifact_closure_sha256"],
    }
    if attestation.get("schema_version") != "formalization-design16-campaign-pair-attestation-1":
        raise BenchmarkError("campaign pair attestation schema is invalid")
    if any(attestation.get(key) != value for key, value in expected.items()):
        raise BenchmarkError("campaign pair attestation identity or artifact closure changed")
    stdout_path = task_root / "runner.stdout.log"
    stderr_path = task_root / "runner.stderr.log"
    if (
        attestation.get("runner_return_code") != 0
        or stdout_path.is_symlink()
        or not stdout_path.is_file()
        or stderr_path.is_symlink()
        or not stderr_path.is_file()
        or attestation.get("runner_stdout_sha256") != sha256_file(stdout_path)
        or attestation.get("runner_stderr_sha256") != sha256_file(stderr_path)
    ):
        raise BenchmarkError("campaign pair runner/log attestation changed")
    return {
        "pair_attestation_path": str(path),
        "pair_attestation_sha256": sha256_file(path),
        "pair_artifact_closure_sha256": details["pair_artifact_closure_sha256"],
    }


@contextmanager
def _exclusive_host_lock(path: Path) -> Iterator[None]:
    if path.is_symlink():
        raise BenchmarkError("timed-contestant host lock may not be a symlink")
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(path, os.O_RDWR | os.O_CREAT, 0o600)
    try:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError as error:
            raise BenchmarkError("another timed campaign holds the host lock") from error
        yield
    finally:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)


def _command(args: argparse.Namespace, item: Mapping[str, Any], pair_root: Path) -> list[str]:
    command = [
        sys.executable,
        str(args.runner.resolve()),
        "--deployment",
        str(args.deployment.resolve()),
        "--mathlib-atlas",
        str(args.mathlib_atlas.resolve()),
        "--task-id",
        str(item["task_id"]),
        "--condition-order",
        ",".join(item["condition_order"]),
        "--output-root",
        str(pair_root),
        "--model",
        args.model,
        "--reasoning-effort",
        args.reasoning_effort,
        "--time-limit-seconds",
        str(args.time_limit_seconds),
        "--validation-timeout-seconds",
        str(args.validation_timeout_seconds),
        "--root-limit",
        str(args.root_limit),
        "--dependency-limit",
        str(args.dependency_limit),
        "--maximum-packet-bytes",
        str(args.maximum_packet_bytes),
        "--submission-limit",
        str(args.submission_limit),
        "--audit-model",
        args.audit_model,
        "--audit-reasoning-effort",
        args.audit_reasoning_effort,
        "--audit-timeout-seconds",
        str(args.audit_timeout_seconds),
        "--audit-infrastructure-retries",
        str(args.audit_infrastructure_retries),
    ]
    if args.enforce_titan_envelope:
        command.append("--require-titan-envelope")
    if args.statement_only:
        command.append("--statement-only")
    return command


def run_campaign(
    args: argparse.Namespace,
    *,
    process_runner: Callable[..., subprocess.CompletedProcess[Any]] = subprocess.run,
) -> dict[str, Any]:
    if args.statement_only and not args.dry_run and not args.enforce_titan_envelope:
        raise BenchmarkError(
            "statement-only measured campaigns require --enforce-titan-envelope"
        )
    hardware_envelope = _activate_hardware_envelope(args)
    core = _manifest_core(args, hardware_envelope=hardware_envelope)
    max_new_tasks = getattr(args, "max_new_tasks", None)
    if max_new_tasks is not None and (
        not isinstance(max_new_tasks, int) or max_new_tasks < 1
    ):
        raise BenchmarkError("--max-new-tasks must be a positive integer")
    wave_task_ids = getattr(args, "wave_task_ids", None)
    if wave_task_ids is None:
        invocation_plan = list(core["plan"])
    else:
        if (
            not isinstance(wave_task_ids, list)
            or not wave_task_ids
            or len(set(wave_task_ids)) != len(wave_task_ids)
            or any(task_id not in EXPECTED_TASKS for task_id in wave_task_ids)
        ):
            raise BenchmarkError(
                "--wave-task-ids must be a nonempty duplicate-free subset of Higham-13"
            )
        plan_by_id = {item["task_id"]: item for item in core["plan"]}
        invocation_plan = [plan_by_id[task_id] for task_id in wave_task_ids]
    if args.dry_run:
        dry_run_plan = (
            invocation_plan[:max_new_tasks]
            if max_new_tasks is not None
            else invocation_plan
        )
        return {
            "dry_run": True,
            "writes_performed": False,
            "campaign_root": str(args.campaign_root.resolve()),
            "campaign_identity_sha256": _canonical_hash(core),
            "plan": core["plan"],
            "invocation_plan": dry_run_plan,
            "commands": [
                _command(
                    args,
                    item,
                    args.campaign_root.resolve()
                    / "tasks"
                    / item["task_id"]
                    / "pair",
                )
                for item in dry_run_plan
            ],
        }

    requested_root = args.campaign_root.expanduser()
    if requested_root.is_symlink():
        raise BenchmarkError("campaign root may not be a symlink")
    root = requested_root.resolve()
    root.mkdir(parents=True, exist_ok=True)
    requested_lock = args.host_lock.expanduser().absolute()
    with _exclusive_host_lock(requested_lock):
        manifest = _load_or_create_manifest(root, core)
        state_path = root / "campaign-state.jsonl"
        events = _read_journal(state_path) if state_path.exists() else []
        _sync_summaries(root, manifest, events)
        if not events:
            _record_event(
                root,
                manifest,
                {"event_type": "CAMPAIGN_STARTED", "outcome": "RUNNING"},
            )
            events = _read_journal(state_path)
        terminals = _terminal_by_task(events)
        started_events: dict[str, Mapping[str, Any]] = {}
        for event in events:
            if event.get("event_type") != "TASK_STARTED":
                continue
            task_id = event.get("task_id")
            if task_id not in EXPECTED_TASKS or task_id in started_events:
                raise BenchmarkError("duplicate or malformed TASK_STARTED event")
            pair_nonce = event.get("pair_nonce")
            if not isinstance(pair_nonce, str) or HEX64.fullmatch(pair_nonce) is None:
                raise BenchmarkError("TASK_STARTED event lacks a valid pair nonce")
            started_events[task_id] = event

        terminalized_this_invocation = 0
        for item in invocation_plan:
            task_id = item["task_id"]
            if task_id in terminals:
                continue
            if (
                max_new_tasks is not None
                and terminalized_this_invocation >= max_new_tasks
            ):
                break
            task_root = root / "tasks" / task_id
            pair_root = task_root / "pair"
            # A started event or an existing output tree means a paid call may
            # already have occurred.  Reconcile it; never silently rerun it.
            if task_id in started_events or pair_root.exists() or pair_root.is_symlink():
                started_event = started_events.get(task_id)
                if started_event is None:
                    outcome, details = "INCIDENT", {
                        "reason": "unattributed pair output exists without TASK_STARTED"
                    }
                else:
                    try:
                        expected_started = {
                            "task_id": task_id,
                            "stratum": item["stratum"],
                            "condition_order": item["condition_order"],
                            "campaign_identity_sha256": manifest[
                                "campaign_identity_sha256"
                            ],
                            "campaign_nonce": manifest["campaign_nonce"],
                            "benchmark_object": core["formalizer"]["benchmark_object"],
                            "source_contract": core["formalizer"]["source_contract"],
                            "command": _command(args, item, pair_root),
                            "outcome": "RUNNING",
                        }
                        if any(
                            started_event.get(key) != value
                            for key, value in expected_started.items()
                        ):
                            raise BenchmarkError(
                                "TASK_STARTED campaign identity, mode, order, or command changed"
                            )
                        outcome, details = _inspect_pair(
                            pair_root,
                            task_id=task_id,
                            condition_order=item["condition_order"],
                            statement_only=bool(args.statement_only),
                            require_titan_envelope=bool(args.enforce_titan_envelope),
                        )
                        if outcome in ATTESTABLE_PAIR_OUTCOMES:
                            attestation_details = _verify_pair_attestation(
                                task_root=task_root,
                                manifest=manifest,
                                pair_nonce=str(started_event["pair_nonce"]),
                                item=item,
                                details=details,
                            )
                            details = {**details, **attestation_details}
                    except (BenchmarkError, OSError, ValueError) as error:
                        outcome, details = "INCIDENT", {
                            "reason": f"pair recovery authentication failed: {error}"
                        }
                details.pop("pair_artifact_closure", None)
                _record_event(
                    root,
                    manifest,
                    {
                        "event_type": (
                            "TASK_RECOVERED_FORMALIZATION_COMPLETE"
                            if outcome == AUDIT_PENDING
                            else "TASK_RECOVERED_AUDITED_FAITHFUL"
                            if outcome == AUDITED_FAITHFUL
                            else "TASK_RECOVERED_AUDITED_INELIGIBLE"
                            if outcome == AUDITED_INELIGIBLE
                            else "TASK_RECOVERED_INCIDENT"
                        ),
                        "task_id": task_id,
                        "stratum": item["stratum"],
                        "outcome": outcome,
                        "details": details,
                    },
                )
                terminals = _terminal_by_task(_read_journal(state_path))
                terminalized_this_invocation += 1
                continue

            task_root.mkdir(parents=True, mode=0o700)
            command = _command(args, item, pair_root)
            pair_nonce = secrets.token_hex(32)
            _record_event(
                root,
                manifest,
                {
                    "event_type": "TASK_STARTED",
                    "task_id": task_id,
                    "stratum": item["stratum"],
                    "condition_order": item["condition_order"],
                    "campaign_identity_sha256": manifest["campaign_identity_sha256"],
                    "campaign_nonce": manifest["campaign_nonce"],
                    "pair_nonce": pair_nonce,
                    "benchmark_object": core["formalizer"]["benchmark_object"],
                    "source_contract": core["formalizer"]["source_contract"],
                    "command": command,
                    "outcome": "RUNNING",
                },
            )
            stdout_path = task_root / "runner.stdout.log"
            stderr_path = task_root / "runner.stderr.log"
            try:
                with stdout_path.open("wb") as stdout, stderr_path.open("wb") as stderr:
                    result = process_runner(command, stdout=stdout, stderr=stderr, check=False)
                return_code = int(result.returncode)
            except Exception as error:
                return_code = None
                process_error = {"type": type(error).__name__, "message": str(error)}
            else:
                process_error = None
            try:
                outcome, details = _inspect_pair(
                    pair_root,
                    task_id=task_id,
                    condition_order=item["condition_order"],
                    statement_only=bool(args.statement_only),
                    require_titan_envelope=bool(args.enforce_titan_envelope),
                )
            except (BenchmarkError, OSError, ValueError) as error:
                outcome, details = "INCIDENT", {
                    "reason": f"pair output authentication failed: {error}"
                }
            details.update(
                {
                    "runner_return_code": return_code,
                    "process_error": process_error,
                    "stdout_sha256": sha256_file(stdout_path),
                    "stderr_sha256": sha256_file(stderr_path),
                }
            )
            if return_code != 0 or process_error is not None:
                outcome = "INCIDENT"
            elif outcome in ATTESTABLE_PAIR_OUTCOMES:
                try:
                    _attest_pair(
                        task_root=task_root,
                        manifest=manifest,
                        pair_nonce=pair_nonce,
                        item=item,
                        details=details,
                        runner_return_code=return_code,
                    )
                    details.update(
                        _verify_pair_attestation(
                            task_root=task_root,
                            manifest=manifest,
                            pair_nonce=pair_nonce,
                            item=item,
                            details=details,
                        )
                    )
                except (BenchmarkError, OSError, ValueError) as error:
                    outcome = "INCIDENT"
                    details["attestation_error"] = str(error)
            details.pop("pair_artifact_closure", None)
            _record_event(
                root,
                manifest,
                {
                    "event_type": (
                        "TASK_FORMALIZATION_COMPLETE"
                        if outcome == AUDIT_PENDING
                        else "TASK_AUDITED_FAITHFUL"
                        if outcome == AUDITED_FAITHFUL
                        else "TASK_AUDITED_INELIGIBLE"
                        if outcome == AUDITED_INELIGIBLE
                        else "TASK_INCIDENT"
                    ),
                    "task_id": task_id,
                    "stratum": item["stratum"],
                    "outcome": outcome,
                    "details": details,
                },
            )
            terminals = _terminal_by_task(_read_journal(state_path))
            terminalized_this_invocation += 1

        events = _read_journal(state_path)
        terminals = _terminal_by_task(events)
        if set(terminals) == set(EXPECTED_TASKS) and not any(
            event.get("event_type") == "CAMPAIGN_FORMALIZATION_COMPLETE"
            for event in events
        ):
            incident_count = sum(
                event.get("outcome") in INCIDENT_OUTCOMES
                for event in terminals.values()
            )
            audit_pending_count = sum(
                event.get("outcome") == AUDIT_PENDING for event in terminals.values()
            )
            audited_faithful_count = sum(
                event.get("outcome") == AUDITED_FAITHFUL
                for event in terminals.values()
            )
            audited_ineligible_count = sum(
                event.get("outcome") == AUDITED_INELIGIBLE
                for event in terminals.values()
            )
            if incident_count:
                campaign_outcome = "FORMALIZATION_COMPLETE_WITH_INCIDENTS"
            elif audit_pending_count:
                campaign_outcome = "AUDIT_PENDING"
            elif audited_ineligible_count:
                campaign_outcome = "AUDITED_CAMPAIGN_WITH_INELIGIBLE_PAIRS"
            else:
                campaign_outcome = "AUDITED_FAITHFUL_CAMPAIGN_READY"
            _record_event(
                root,
                manifest,
                {
                    "event_type": "CAMPAIGN_FORMALIZATION_COMPLETE",
                    "outcome": campaign_outcome,
                    "scientifically_completed_task_count": 0,
                    "formalization_complete_audit_pending_task_count": audit_pending_count,
                    "audited_faithful_pair_task_count": audited_faithful_count,
                    "audited_ineligible_pair_task_count": audited_ineligible_count,
                    "incident_task_count": incident_count,
                },
            )
        final_events = _read_journal(state_path)
        return _summary_payload(manifest=manifest, events=final_events)


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", type=Path, required=True)
    parser.add_argument("--mathlib-atlas", type=Path, required=True)
    parser.add_argument("--campaign-root", type=Path, required=True)
    parser.add_argument("--runner", type=Path, required=True)
    parser.add_argument("--runner-commit", required=True)
    parser.add_argument("--runner-sha256", required=True)
    parser.add_argument("--controller-commit", required=True)
    parser.add_argument("--controller-sha256", required=True)
    parser.add_argument(
        "--config", type=Path, default=ROOT / "config.json"
    )
    parser.add_argument(
        "--readiness",
        type=Path,
        default=ROOT / "design16" / "higham13_readiness.json",
    )
    parser.add_argument(
        "--host-lock",
        type=Path,
        default=Path("/tmp/highambench-design16-timed-contestant.lock"),
    )
    parser.add_argument("--model", default="gpt-5.6-sol")
    parser.add_argument("--reasoning-effort", default="xhigh")
    parser.add_argument("--time-limit-seconds", type=int, default=18000)
    parser.add_argument("--validation-timeout-seconds", type=int, default=600)
    parser.add_argument("--root-limit", type=int, default=3)
    parser.add_argument("--dependency-limit", type=int, default=5)
    parser.add_argument("--maximum-packet-bytes", type=int, default=48 * 1024)
    parser.add_argument("--submission-limit", type=int, default=4)
    parser.add_argument("--audit-model", default="gpt-6-astra")
    parser.add_argument("--audit-reasoning-effort", default="high")
    parser.add_argument("--audit-timeout-seconds", type=float, default=7200)
    parser.add_argument("--audit-infrastructure-retries", type=int, default=2)
    parser.add_argument(
        "--enforce-titan-envelope",
        action="store_true",
        help=(
            "require a delegated systemd envelope, verify 8 CPUs/32 GiB/no swap, "
            "and bound generated commands in a 24-GiB sub-cgroup"
        ),
    )
    parser.add_argument(
        "--statement-only",
        action="store_true",
        help="freeze the campaign to statement-only formalization with one target sorry",
    )
    parser.add_argument(
        "--max-new-tasks",
        type=int,
        help="stop after this many previously nonterminal tasks; resume later",
    )
    parser.add_argument(
        "--wave-task-ids",
        nargs="+",
        help=(
            "run only this ordered subset during the current invocation; "
            "the frozen 13-task campaign identity and per-task orders are unchanged"
        ),
    )
    parser.add_argument("--dry-run", action="store_true")
    return parser


def main() -> int:
    args = make_parser().parse_args()
    if args.enforce_titan_envelope and os.environ.get(TITAN_ENVELOPE_MARKER) != "1":
        systemd_run = shutil.which("systemd-run")
        if systemd_run is None:
            raise BenchmarkError("systemd-run is required for the Titan envelope")
        command = [
            *systemd_service_envelope_prefix(systemd_run),
            "--working-directory",
            str(Path.cwd().resolve()),
            "--setenv",
            f"{TITAN_ENVELOPE_MARKER}=1",
            sys.executable,
            str(Path(__file__).resolve()),
            *sys.argv[1:],
        ]
        return subprocess.run(command, check=False).returncode
    result = run_campaign(args)
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"Design-16 campaign error: {error}", file=sys.stderr)
        raise SystemExit(2)
