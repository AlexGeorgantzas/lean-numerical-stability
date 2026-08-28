#!/usr/bin/env python3
"""Create or verify one authenticated nine-pair HighamBench shard aggregate."""

from __future__ import annotations

import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import re
import sys
from typing import Any, Mapping, Sequence

import manage_highambench_pair_shard as shard


SCHEMA_VERSION = 1
KIND = "highambench-private-paper-shard-aggregate-index"
HASH_FIELD = "aggregate_index_sha256"
INDEX_NAME = "aggregate_index.json"
HEX64_RE = re.compile(r"[0-9a-f]{64}")
PAPER_FILENAMES = {
    "P05": "P05_IMPROVED BACKWARD ERROR BOUNDS FOR LU ANDCHOLESKY FACTORIZATIONS.pdf",
    "P11": "P11_A note on the error analysis of classical Gram–Schmidt.pdf",
    "P15": "P15_Solving block low-rank linear systems by LU factorization is numerically stable.pdf",
    "P20": "P20_ERROR ANALYSIS OF MATRIX MULTIPLICATION WITHNARROW RANGE FLOATING-POINT ARITHMETIC.pdf",
}


class AggregateError(RuntimeError):
    """Raised when a shard aggregate fails closed."""


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")


def bind_hash(value: Mapping[str, Any]) -> dict[str, Any]:
    result = dict(value)
    result.pop(HASH_FIELD, None)
    result[HASH_FIELD] = shard.canonical_sha256(result)
    return result


def verify_hash(value: Mapping[str, Any]) -> None:
    unsigned = dict(value)
    observed = unsigned.pop(HASH_FIELD, None)
    if (
        not isinstance(observed, str)
        or HEX64_RE.fullmatch(observed) is None
        or shard.canonical_sha256(unsigned) != observed
    ):
        raise AggregateError("aggregate index self-hash is stale")


def read_json(path: Path, label: str) -> Mapping[str, Any]:
    if path.is_symlink() or not path.is_file():
        raise AggregateError(f"{label} is missing or unsafe: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise AggregateError(f"cannot read {label}: {error}") from error
    if not isinstance(value, Mapping):
        raise AggregateError(f"{label} is not a JSON object")
    return value


def atomic_write(path: Path, value: Mapping[str, Any]) -> None:
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}")
    if path.exists() or path.is_symlink():
        raise AggregateError(f"aggregate index already exists: {path}")
    if temporary.exists() or temporary.is_symlink():
        raise AggregateError(f"aggregate temporary already exists: {temporary}")
    payload = json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="") as stream:
            stream.write(payload)
            stream.flush()
            os.fchmod(stream.fileno(), 0o444)
            os.fsync(stream.fileno())
        # Hard-link publication is atomic and refuses to overwrite an index
        # concurrently published by another verifier.
        os.link(temporary, path)
        temporary.unlink()
        shard.fsync_directory(path.parent)
    except BaseException:
        if temporary.exists() and not temporary.is_symlink():
            temporary.unlink()
        raise


def canonical_pair_ids(paper_id: str) -> list[str]:
    return [
        f"{paper_id}-T{tier}-rep-0{repetition}"
        for tier in range(1, 4)
        for repetition in range(1, 4)
    ]


def validate_root_entries(shards_root: Path, pair_ids: Sequence[str]) -> None:
    if shards_root.is_symlink() or not shards_root.is_dir():
        raise AggregateError("shards root is missing, linked, or not a directory")
    allowed = set(pair_ids) | {INDEX_NAME}
    unexpected = sorted(path.name for path in shards_root.iterdir() if path.name not in allowed)
    if unexpected:
        raise AggregateError(f"shards root has unexpected entries: {unexpected}")
    for pair_id in pair_ids:
        root = shards_root / pair_id
        if root.is_symlink() or not root.is_dir():
            raise AggregateError(f"pair shard root is missing or unsafe: {root}")
    aggregate_path = shards_root / INDEX_NAME
    if aggregate_path.exists() and (
        aggregate_path.is_symlink()
        or not aggregate_path.is_file()
        or aggregate_path.stat().st_mode & 0o777 != 0o444
    ):
        raise AggregateError("aggregate index path is unsafe or not sealed mode 0444")


def validate_shard_root_entries(shard_root: Path) -> None:
    """Require the exact launcher-owned top-level shard surface."""

    entries = {path.name: path for path in shard_root.iterdir()}
    if set(entries) != shard.LAUNCHER_ROOT_ENTRIES:
        raise AggregateError(
            f"pair shard has unexpected/missing top-level entries: {shard_root}"
        )
    for name in (".campaign.lock", ".launcher.lock", "campaign_index.json"):
        path = entries[name]
        if path.is_symlink() or not path.is_file():
            raise AggregateError(f"pair shard top-level file is unsafe: {path}")
    for name in ("pair_attempts", "runbook_audit"):
        path = entries[name]
        if path.is_symlink() or not path.is_dir():
            raise AggregateError(f"pair shard top-level directory is unsafe: {path}")


def expected_ledger_paths(
    benchmark_root: Path, paper_id: str
) -> tuple[Path, set[str]]:
    benchmark = benchmark_root.resolve()
    project = benchmark.parents[1]
    if benchmark != project / "paper_bencmark/highambench":
        raise AggregateError("benchmark root is not at its canonical project path")
    fixed = {
        benchmark / "metadata/manifest.json",
        benchmark / "metadata/run_order.json",
        project
        / "paper_bencmark/scratch_pad/HighamBench_Simple_Two_Condition_Specification.pdf",
        project
        / "paper_bencmark/scratch_pad/run_highambench_pair_shard_actual_ultra.sh",
        project / "paper_bencmark/scratch_pad/manage_highambench_pair_shard.py",
        project / "paper_bencmark/reference_papers" / PAPER_FILENAMES[paper_id],
        benchmark / "agent_prompt.md",
        benchmark / "condition_prompts/L.md",
    }
    for relative_tree in ("tasks", "shared", "metadata/controlled"):
        tree = benchmark / relative_tree
        if tree.is_symlink() or not tree.is_dir():
            raise AggregateError(f"frozen benchmark tree is unsafe: {tree}")
        for path in tree.rglob("*"):
            if path.is_symlink():
                raise AggregateError(f"frozen benchmark tree contains a symlink: {path}")
            if path.is_file():
                fixed.add(path)
    expected: set[str] = set()
    for path in fixed:
        if path.is_symlink() or not path.is_file():
            raise AggregateError(f"frozen ledger input is missing or unsafe: {path}")
        try:
            expected.add(path.resolve().relative_to(project).as_posix())
        except ValueError as error:
            raise AggregateError(f"frozen ledger input escapes project: {path}") from error
    return project, expected


def ledger_descriptor(
    shard_root: Path, benchmark_root: Path, paper_id: str
) -> dict[str, Any]:
    path = shard_root / "runbook_audit" / shard.INITIAL_LEDGER_NAME
    if path.is_symlink() or not path.is_file():
        raise AggregateError(f"shard lacks its sealed initial task ledger: {path}")
    if path.stat().st_mode & 0o777 != 0o444:
        raise AggregateError(f"initial task ledger is not mode 0444: {path}")
    lines = path.read_text(encoding="utf-8").splitlines()
    entries: dict[str, str] = {}
    for line in lines:
        match = re.fullmatch(r"([0-9a-f]{64})  ([^\x00\r\n]+)", line)
        if match is None or match.group(2) in entries:
            raise AggregateError(f"initial task ledger is malformed: {path}")
        entries[match.group(2)] = match.group(1)
    if list(entries) != sorted(entries):
        raise AggregateError(f"initial task ledger is not canonically ordered: {path}")
    project, expected = expected_ledger_paths(benchmark_root, paper_id)
    if set(entries) != expected:
        raise AggregateError(f"initial task ledger file set is not exact: {path}")
    for relative, recorded_sha in entries.items():
        candidate = project / relative
        try:
            resolved = candidate.resolve(strict=True)
            resolved.relative_to(project)
        except (OSError, ValueError) as error:
            raise AggregateError(
                f"initial task ledger path is missing or escapes project: {relative}"
            ) from error
        if candidate.is_symlink() or resolved != candidate.absolute() or not candidate.is_file():
            raise AggregateError(f"initial task ledger path is unsafe: {relative}")
        if shard.file_sha256(candidate) != recorded_sha:
            raise AggregateError(f"initial task ledger digest is stale: {relative}")
    return {
        "path": (Path("runbook_audit") / shard.INITIAL_LEDGER_NAME).as_posix(),
        "sha256": shard.file_sha256(path),
        "line_count": len(lines),
        "manager_sha256": entries[
            "paper_bencmark/scratch_pad/manage_highambench_pair_shard.py"
        ],
        "launcher_sha256": entries[
            "paper_bencmark/scratch_pad/run_highambench_pair_shard_actual_ultra.sh"
        ],
    }


def build(
    shards_root: Path,
    benchmark_root: Path,
    paper_id: str,
    *,
    created_at_utc: str | None = None,
) -> dict[str, Any]:
    pair_ids = canonical_pair_ids(paper_id)
    validate_root_entries(shards_root, pair_ids)
    shard_descriptors: list[dict[str, Any]] = []
    reference_snapshot: dict[str, Any] | None = None
    reference_freeze: Mapping[str, Any] | None = None
    reference_ledger_sha: str | None = None
    manager_sha: str | None = None
    launcher_sha: str | None = None
    final_run_ids: set[str] = set()
    final_paths: set[str] = set()

    for pair_id in pair_ids:
        shard.configure_target(paper_id, pair_id)
        root = shards_root / pair_id
        validate_shard_root_entries(root)
        index = shard.load_and_verify_index(root, benchmark_root)
        if index.get("active_pair_attempt") is not None:
            raise AggregateError(f"pair shard remains active: {pair_id}")
        committed = index.get("committed_pairs")
        if not isinstance(committed, Mapping) or set(committed) != {pair_id}:
            raise AggregateError(f"pair shard is not exactly committed: {pair_id}")
        descriptor = committed[pair_id]
        if not isinstance(descriptor, Mapping):
            raise AggregateError(f"pair shard commit is malformed: {pair_id}")
        shard.verify_committed_index_descriptor(
            root, benchmark_root, index, descriptor
        )
        final_records = descriptor.get("final_records")
        if not isinstance(final_records, Mapping) or set(final_records) != {"N", "L"}:
            raise AggregateError(f"pair shard lacks exact N/L final descriptors: {pair_id}")
        for condition in ("N", "L"):
            final = final_records[condition]
            if not isinstance(final, Mapping):
                raise AggregateError(f"pair shard final descriptor is malformed: {pair_id}-{condition}")
            run_id = final.get("run_id")
            expected_run_id = f"{pair_id}-{condition}"
            if run_id != expected_run_id:
                raise AggregateError(
                    f"pair shard final run identity is stale: {run_id!r} != {expected_run_id!r}"
                )
            relative = shard.safe_relative_path(
                final.get("path"), f"{pair_id}-{condition} final path"
            )
            provenance_path = (
                Path(pair_id)
                / shard.safe_relative_path(
                    descriptor.get("path"), f"{pair_id} committed-attempt path"
                )
                / relative
            ).as_posix()
            if run_id in final_run_ids or provenance_path in final_paths:
                raise AggregateError("aggregate aliases a final run identity or path")
            final_run_ids.add(run_id)
            final_paths.add(provenance_path)
        failed = index.get("failed_pair_attempts")
        if not isinstance(failed, list):
            raise AggregateError(f"pair shard failure history is malformed: {pair_id}")
        if shard.attempt_number(descriptor) != len(failed) + 1:
            raise AggregateError(
                f"{pair_id} selected commit is not the first success after retained failures"
            )
        commit_root = shard.resolve_below(
            root, descriptor.get("path"), f"{pair_id} committed attempt"
        )
        freeze = shard.mapping(
            shard.read_json(commit_root / "freeze_check.json", f"{pair_id} freeze"),
            f"{pair_id} freeze",
        )
        if reference_freeze is None:
            reference_freeze = freeze
        else:
            shard.run_matrix.verify_pair_policy_compatible_freeze_checks(
                reference_freeze, freeze
            )

        stable = {
            key: index[key]
            for key in (
                "benchmark_id",
                "manifest",
                "run_order",
                "environment",
                "hardware_matching_policy",
                "hardware_matching_policy_sha256",
                "canonical_pairs",
            )
        }
        if reference_snapshot is None:
            reference_snapshot = stable
        elif stable != reference_snapshot:
            raise AggregateError(f"{pair_id} shard frozen metadata differs")

        ledger = ledger_descriptor(root, benchmark_root, paper_id)
        if reference_ledger_sha is None:
            reference_ledger_sha = str(ledger["sha256"])
            manager_sha = str(ledger["manager_sha256"])
            launcher_sha = str(ledger["launcher_sha256"])
        elif (
            ledger["sha256"] != reference_ledger_sha
            or ledger["manager_sha256"] != manager_sha
            or ledger["launcher_sha256"] != launcher_sha
        ):
            raise AggregateError(f"{pair_id} shard initial task ledger differs")

        index_path = root / "campaign_index.json"
        shard_descriptors.append(
            {
                "pair_id": pair_id,
                "shard_root": pair_id,
                "shard_index": {
                    "path": f"{pair_id}/campaign_index.json",
                    "sha256": shard.file_sha256(index_path),
                    "campaign_index_sha256": index[shard.INDEX_HASH_FIELD],
                },
                "committed_attempt": json.loads(json.dumps(descriptor)),
                "failed_pair_attempt_count": len(failed),
                "failed_pair_attempts": json.loads(json.dumps(failed)),
                "initial_task_ledger": ledger,
            }
        )

    if reference_snapshot is None or reference_freeze is None:
        raise AggregateError("aggregate contains no pair shards")
    if len(final_run_ids) != 18 or len(final_paths) != 18:
        raise AggregateError("aggregate does not cover 18 unique final run IDs and paths")
    if [item["pair_id"] for item in reference_snapshot["canonical_pairs"]] != pair_ids:
        raise AggregateError("aggregate canonical-pair order is stale")
    created = created_at_utc or utc_now()
    try:
        parsed = datetime.fromisoformat(created.removesuffix("Z") + "+00:00")
    except ValueError as error:
        raise AggregateError("aggregate creation time is invalid") from error
    if not created.endswith("Z") or parsed.utcoffset() != timezone.utc.utcoffset(parsed):
        raise AggregateError("aggregate creation time is not canonical UTC")
    return bind_hash(
        {
            "schema_version": SCHEMA_VERSION,
            "kind": KIND,
            "paper_id": paper_id,
            **reference_snapshot,
            "pair_ids": pair_ids,
            "pair_shards": shard_descriptors,
            "common_initial_task_ledger_sha256": reference_ledger_sha,
            "manager_sha256": manager_sha,
            "launcher_sha256": launcher_sha,
            "created_at_utc": created,
        }
    )


def verify_existing(
    shards_root: Path, benchmark_root: Path, paper_id: str
) -> dict[str, Any]:
    path = shards_root / INDEX_NAME
    recorded = dict(read_json(path, "aggregate index"))
    verify_hash(recorded)
    if (
        recorded.get("schema_version") != SCHEMA_VERSION
        or recorded.get("kind") != KIND
        or recorded.get("paper_id") != paper_id
    ):
        raise AggregateError("aggregate index identity is invalid")
    rebuilt = build(
        shards_root,
        benchmark_root,
        paper_id,
        created_at_utc=recorded.get("created_at_utc"),
    )
    if recorded != rebuilt:
        raise AggregateError("aggregate index is stale")
    return recorded


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--paper-id", choices=shard.SUPPORTED_PAPER_IDS, required=True)
    result.add_argument("--shards-root", type=Path, required=True)
    result.add_argument("--benchmark-root", type=Path, required=True)
    result.add_argument("command", choices=("create", "verify"))
    return result


def main(argv: Sequence[str] | None = None) -> int:
    args = parser().parse_args(argv)
    shards_root = args.shards_root.absolute()
    benchmark_root = args.benchmark_root.resolve()
    try:
        path = shards_root / INDEX_NAME
        if args.command == "create":
            if path.exists() or path.is_symlink():
                value = verify_existing(shards_root, benchmark_root, args.paper_id)
            else:
                value = build(shards_root, benchmark_root, args.paper_id)
                atomic_write(path, value)
        else:
            value = verify_existing(shards_root, benchmark_root, args.paper_id)
        print(json.dumps(value, sort_keys=True))
        return 0
    except (
        AggregateError,
        shard.CampaignError,
        shard.run_matrix.BenchmarkToolError,
        OSError,
        ValueError,
    ) as error:
        print(f"pair-shard aggregate error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
