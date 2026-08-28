#!/usr/bin/env python3
"""Manage one private HighamBench pair shard as immutable attempts.

The selected N/L pair is a transaction.  An attempt is created at its permanent path
before provider work begins and is never renamed.  A successful attempt is
committed by authenticating ``pair_commit.json`` and updating the self-hashed
shard index; an unsuccessful attempt is retained and indexed for audit.  Nine
independent shard roots can be authenticated later without sharing a mutable
campaign lock.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
from datetime import datetime, timezone
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import sys
from typing import Any, Iterator, Mapping, Sequence

try:
    from . import run_matrix
except ImportError:  # pragma: no cover - direct script execution
    tools_root = Path(__file__).resolve().parents[1] / "highambench" / "tools"
    if str(tools_root) not in sys.path:
        sys.path.insert(0, str(tools_root))
    import run_matrix  # type: ignore


INDEX_SCHEMA_VERSION = 1
INDEX_KIND = "highambench-private-pair-shard-index"
INDEX_HASH_FIELD = "campaign_index_sha256"
TREE_MANIFEST_KIND = "highambench-recursive-file-manifest"
SUPPORTED_PAPER_IDS = ("P05", "P11", "P15", "P20")
VETTED_NODES = tuple(run_matrix.HARDWARE_MATCHING_POLICY["vetted_nodes"])
PAIR_ID_RE = re.compile(r"P(?:05|11|15|20)-T[123]-rep-0[123]")
JOB_ID_RE = re.compile(r"[1-9][0-9]*")
HEX64_RE = re.compile(r"[0-9a-f]{64}")
ACTIVE_FIELDS = {
    "pair_id",
    "attempt_id",
    "path",
    "slurm_job_id",
    "allocation_node",
    "started_at_utc",
}
COMMITTED_FIELDS = ACTIVE_FIELDS | {
    "committed_at_utc",
    "file_count",
    "total_bytes",
    "tree_sha256",
    "pair_commit",
    "final_records",
    "allocation_hardware",
    "freeze_check_sha256",
    "hardware_matching_policy_sha256",
}
FAILED_FIELDS = ACTIVE_FIELDS | {
    "archived_at_utc",
    "outcome",
    "matrix_exit_code",
    "final_record_count",
    "incidents",
    "last_chunk_status",
    "file_count",
    "total_bytes",
    "tree_sha256",
}
MATRIX_EXIT_MARKER = "campaign_matrix_exit.json"
INDEX_TEMP_RE = re.compile(r"\.campaign_index\.json\.tmp-([1-9][0-9]*)")
LAUNCHER_ROOT_ENTRIES = {
    ".campaign.lock",
    ".launcher.lock",
    "campaign_index.json",
    "pair_attempts",
    "runbook_audit",
}
INITIAL_LEDGER_NAME = "benchmark_task_checksums.initial.sha256"
INDEX_FIELDS = {
    "schema_version",
    "kind",
    "paper_id",
    "target_pair_id",
    "benchmark_id",
    "manifest",
    "run_order",
    "environment",
    "hardware_matching_policy",
    "hardware_matching_policy_sha256",
    "canonical_pairs",
    "committed_pairs",
    "failed_pair_attempts",
    "active_pair_attempt",
    "created_at_utc",
    "updated_at_utc",
    INDEX_HASH_FIELD,
}

_TARGET_PAPER_ID: str | None = None
_TARGET_PAIR_ID: str | None = None


class CampaignError(RuntimeError):
    """Raised when campaign state fails closed."""


def configure_target(paper_id: str, pair_id: str) -> None:
    """Bind this process to exactly one supported paper/pair shard."""

    global _TARGET_PAPER_ID, _TARGET_PAIR_ID
    if paper_id not in SUPPORTED_PAPER_IDS:
        raise CampaignError(
            f"paper ID must be one of {SUPPORTED_PAPER_IDS}, got {paper_id!r}"
        )
    if PAIR_ID_RE.fullmatch(pair_id) is None or not pair_id.startswith(
        f"{paper_id}-"
    ):
        raise CampaignError(
            f"pair ID {pair_id!r} is not canonical for paper {paper_id}"
        )
    _TARGET_PAPER_ID = paper_id
    _TARGET_PAIR_ID = pair_id


def target_paper_id() -> str:
    if _TARGET_PAPER_ID is None:
        raise CampaignError("pair-shard paper target is not configured")
    return _TARGET_PAPER_ID


def target_pair_id() -> str:
    if _TARGET_PAIR_ID is None:
        raise CampaignError("pair-shard pair target is not configured")
    return _TARGET_PAIR_ID


def canonical_bytes(value: Any) -> bytes:
    return json.dumps(
        value,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ).encode("utf-8")


def canonical_sha256(value: Any) -> str:
    return hashlib.sha256(canonical_bytes(value)).hexdigest()


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def read_json(path: Path, label: str) -> Any:
    if path.is_symlink() or not path.is_file():
        raise CampaignError(f"{label} is missing or unsafe: {path}")
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise CampaignError(f"cannot read {label}: {error}") from error


def mapping(value: Any, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise CampaignError(f"{label} is not a JSON object")
    return value


def string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise CampaignError(f"{label} is not a nonempty string")
    return value


def hex64(value: Any, label: str) -> str:
    text = string(value, label)
    if HEX64_RE.fullmatch(text) is None:
        raise CampaignError(f"{label} is not a lowercase SHA-256")
    return text


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat().replace("+00:00", "Z")


def utc_instant(value: Any, label: str) -> datetime:
    text = string(value, label)
    if not text.endswith("Z"):
        raise CampaignError(f"{label} is not a canonical UTC timestamp")
    try:
        parsed = datetime.fromisoformat(text[:-1] + "+00:00")
    except ValueError as error:
        raise CampaignError(f"{label} is not a valid UTC timestamp") from error
    if parsed.utcoffset() != timezone.utc.utcoffset(parsed):
        raise CampaignError(f"{label} is not UTC")
    return parsed


def fsync_directory(path: Path) -> None:
    fd = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def atomic_write_json(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}")
    if temporary.exists() or temporary.is_symlink():
        raise CampaignError(f"temporary index path already exists: {temporary}")
    payload = json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"
    fd = os.open(temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    try:
        with os.fdopen(fd, "w", encoding="utf-8", newline="") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
        fsync_directory(path.parent)
    except BaseException:
        if temporary.exists() and not temporary.is_symlink():
            temporary.unlink()
        raise


def bind_index_hash(index: Mapping[str, Any]) -> dict[str, Any]:
    result = dict(index)
    result.pop(INDEX_HASH_FIELD, None)
    result[INDEX_HASH_FIELD] = canonical_sha256(result)
    return result


def verify_index_hash(index: Mapping[str, Any]) -> None:
    expected = dict(index)
    observed = hex64(expected.pop(INDEX_HASH_FIELD, None), "campaign index self-hash")
    if canonical_sha256(expected) != observed:
        raise CampaignError("campaign index self-hash is stale")


def safe_relative_path(raw: Any, label: str) -> Path:
    text = string(raw, label)
    path = Path(text)
    if path.is_absolute() or not path.parts or any(part in {"", ".", ".."} for part in path.parts):
        raise CampaignError(f"{label} is not a safe relative path: {text!r}")
    if path.as_posix() != text:
        raise CampaignError(f"{label} is not canonical POSIX form: {text!r}")
    return path


def resolve_below(root: Path, raw: Any, label: str) -> Path:
    relative = safe_relative_path(raw, label)
    if root.is_symlink():
        raise CampaignError(f"{label} campaign root is a symlink: {root}")
    root = root.resolve()
    cursor = root
    for part in relative.parts:
        cursor = cursor / part
        if cursor.is_symlink():
            raise CampaignError(f"{label} contains a symlink component: {cursor}")
    candidate = cursor.resolve()
    try:
        candidate.relative_to(root.resolve())
    except ValueError as error:
        raise CampaignError(f"{label} escapes the campaign root") from error
    return candidate


def recursive_tree_summary(root: Path) -> dict[str, Any]:
    if root.is_symlink() or not root.is_dir():
        raise CampaignError(f"pair-attempt root is missing or unsafe: {root}")
    files: list[dict[str, Any]] = []
    for path in sorted(root.rglob("*"), key=lambda item: item.relative_to(root).as_posix()):
        if path.is_symlink():
            raise CampaignError(f"pair-attempt tree contains a symlink: {path}")
        if path.is_dir():
            continue
        if not path.is_file():
            raise CampaignError(f"pair-attempt tree contains a special file: {path}")
        stat = path.stat()
        files.append(
            {
                "path": path.relative_to(root).as_posix(),
                "size_bytes": stat.st_size,
                "sha256": file_sha256(path),
            }
        )
    manifest = {
        "schema_version": 1,
        "kind": TREE_MANIFEST_KIND,
        "files": files,
    }
    return {
        "file_count": len(files),
        "total_bytes": sum(item["size_bytes"] for item in files),
        "tree_sha256": canonical_sha256(manifest),
    }


def canonical_pairs(run_order: Mapping[str, Any]) -> list[dict[str, Any]]:
    paper_id = target_paper_id()
    pairs = run_order.get("pairs")
    if not isinstance(pairs, list):
        raise CampaignError("run order lacks its pair list")
    result: list[dict[str, Any]] = []
    for raw in pairs:
        pair = mapping(raw, "run-order pair")
        pair_id = string(pair.get("pair_id"), "run-order pair ID")
        if not pair_id.startswith(f"{paper_id}-"):
            continue
        if PAIR_ID_RE.fullmatch(pair_id) is None:
            raise CampaignError(
                f"{paper_id} pair ID is not canonical: {pair_id!r}"
            )
        condition_order = pair.get("condition_order")
        run_ids = pair.get("run_ids")
        if (
            not isinstance(condition_order, list)
            or len(condition_order) != 2
            or set(condition_order) != {"N", "L"}
            or not isinstance(run_ids, list)
            or run_ids != [f"{pair_id}-{condition}" for condition in condition_order]
        ):
            raise CampaignError(f"run-order pair {pair_id} has invalid N/L ordering")
        result.append(
            {
                "pair_id": pair_id,
                "task_id": string(pair.get("task_id"), f"{pair_id} task ID"),
                "repetition_id": string(
                    pair.get("repetition_id"), f"{pair_id} repetition ID"
                ),
                "condition_order": list(condition_order),
                "run_ids": list(run_ids),
                "run_order_pair_sha256": hex64(
                    pair.get("sha256"), f"{pair_id} order SHA-256"
                ),
            }
        )
    expected = [
        f"{paper_id}-T{tier}-rep-0{repetition}"
        for tier in range(1, 4)
        for repetition in range(1, 4)
    ]
    if [pair["pair_id"] for pair in result] != expected:
        raise CampaignError(
            f"run order does not contain the exact nine canonical {paper_id} pairs"
        )
    return result


def metadata_snapshot(benchmark_root: Path) -> dict[str, Any]:
    manifest_path = benchmark_root / "metadata" / "manifest.json"
    order_path = benchmark_root / "metadata" / "run_order.json"
    config_path = benchmark_root / "metadata" / "config.json"
    environment_path = benchmark_root / "metadata" / "environment.json"
    manifest = mapping(read_json(manifest_path, "benchmark manifest"), "benchmark manifest")
    order = mapping(read_json(order_path, "run order"), "run order")
    config = mapping(read_json(config_path, "config"), "config")
    environment = mapping(read_json(environment_path, "environment"), "environment")
    benchmark_id = string(config.get("benchmark_id"), "config benchmark ID")
    if manifest.get("benchmark_id") != benchmark_id or order.get("benchmark_id") != benchmark_id:
        raise CampaignError("manifest/config/run-order benchmark IDs disagree")
    frozen = mapping(config.get("frozen_environment"), "frozen environment")
    policy = mapping(environment.get("hardware_matching_policy"), "hardware matching policy")
    if frozen.get("hardware_matching_policy") != policy:
        raise CampaignError("config/environment hardware policies disagree")
    if policy != run_matrix.HARDWARE_MATCHING_POLICY:
        raise CampaignError("hardware policy is not the exact runner policy")
    environment_id = string(environment.get("environment_id"), "environment ID")
    bundle = hex64(environment.get("environment_bundle_sha256"), "environment bundle")
    if frozen.get("environment_id") != environment_id or frozen.get("environment_bundle_sha256") != bundle:
        raise CampaignError("config/environment bundle identifiers disagree")
    if run_matrix.environment_bundle_digest(config, environment) != bundle:
        raise CampaignError("config/environment bundle SHA-256 is stale")
    return {
        "benchmark_id": benchmark_id,
        "manifest": {
            "path": "metadata/manifest.json",
            "sha256": file_sha256(manifest_path),
        },
        "run_order": {
            "path": "metadata/run_order.json",
            "sha256": file_sha256(order_path),
        },
        "environment": {
            "path": "metadata/environment.json",
            "environment_id": environment_id,
            "environment_bundle_sha256": bundle,
        },
        "hardware_matching_policy": json.loads(json.dumps(policy)),
        "hardware_matching_policy_sha256": canonical_sha256(policy),
        "canonical_pairs": canonical_pairs(order),
    }


def planned_pair_assignments(
    benchmark_root: Path, pair_id: str
) -> list[dict[str, Any]]:
    """Rebuild the exact two runner assignments for one canonical pair."""

    config = mapping(
        read_json(benchmark_root / "metadata" / "config.json", "config"), "config"
    )
    order = mapping(
        read_json(benchmark_root / "metadata" / "run_order.json", "run order"),
        "run order",
    )
    repetition_ids = run_matrix.configured_repetition_ids(config)
    assignments = run_matrix.assignments_from_order(
        order, run_matrix.load_task_catalog(benchmark_root), repetition_ids
    )
    seeds: dict[str, int | None] = {}
    for raw in config.get("repetitions", []):
        repetition = mapping(raw, "config repetition")
        repetition_id = string(repetition.get("id"), "config repetition ID")
        seed = repetition.get("backend_seed")
        if seed is not None and (isinstance(seed, bool) or not isinstance(seed, int)):
            raise CampaignError(f"config repetition {repetition_id} has an invalid seed")
        seeds[repetition_id] = seed
    selected: list[dict[str, Any]] = []
    for assignment in assignments:
        if assignment.get("pair_id") == pair_id:
            item = dict(assignment)
            item["backend_seed"] = seeds[item["repetition_id"]]
            selected.append(item)
    if len(selected) != 2 or {item.get("condition") for item in selected} != {"N", "L"}:
        raise CampaignError(f"cannot rebuild exact N/L assignments for {pair_id}")
    return selected


def verify_pair_freeze_against_metadata(
    benchmark_root: Path,
    freeze: Mapping[str, Any],
    index: Mapping[str, Any],
) -> None:
    environment = mapping(
        read_json(
            benchmark_root / "metadata" / "environment.json", "environment"
        ),
        "environment",
    )
    if (
        freeze.get("benchmark_id") != index["benchmark_id"]
        or freeze.get("environment_id") != index["environment"]["environment_id"]
        or freeze.get("environment_bundle_sha256")
        != index["environment"]["environment_bundle_sha256"]
        or freeze.get("hardware_matching_policy") != index["hardware_matching_policy"]
    ):
        raise CampaignError("pair freeze does not match the campaign snapshot and policy")
    reference = json.loads(json.dumps(freeze))
    reference["host_class"] = json.loads(json.dumps(environment.get("host_class")))
    reference["provider_token_gate"] = json.loads(
        json.dumps(environment.get("provider_token_gate"))
    )
    run_matrix.verify_pair_policy_compatible_freeze_checks(reference, freeze)


@contextmanager
def campaign_lock(campaign_root: Path) -> Iterator[None]:
    campaign_root.mkdir(parents=True, exist_ok=True)
    if campaign_root.is_symlink() or not campaign_root.is_dir():
        raise CampaignError(f"campaign root is unsafe: {campaign_root}")
    lock_path = campaign_root / ".campaign.lock"
    with lock_path.open("a+b") as stream:
        fcntl.flock(stream.fileno(), fcntl.LOCK_EX)
        yield
        fcntl.flock(stream.fileno(), fcntl.LOCK_UN)


def recover_launcher_staging(campaign_root: Path, job_id: str) -> dict[str, Any]:
    """Preserve exact crash remnants after the whole-launcher lock is held."""

    if JOB_ID_RE.fullmatch(job_id) is None:
        raise CampaignError("staging-recovery Slurm job ID is noncanonical")
    if campaign_root.is_symlink() or not campaign_root.is_dir():
        raise CampaignError("staging-recovery campaign root is unsafe")
    index_temporaries: list[tuple[Path, str]] = []
    for path in campaign_root.iterdir():
        if path.name in LAUNCHER_ROOT_ENTRIES:
            continue
        match = INDEX_TEMP_RE.fullmatch(path.name)
        if match is None:
            raise CampaignError(f"campaign root has an unexpected entry: {path.name}")
        if path.is_symlink() or not path.is_file():
            raise CampaignError(
                f"campaign index temporary is not a regular non-symlink file: {path}"
            )
        index_temporaries.append((path, match.group(1)))

    audit = campaign_root / "runbook_audit"
    if audit.exists() or audit.is_symlink():
        if audit.is_symlink() or not audit.is_dir():
            raise CampaignError("runbook audit directory is unsafe")
    else:
        audit.mkdir()
        fsync_directory(campaign_root)

    initial_ledger = audit / INITIAL_LEDGER_NAME
    partial_initial_ledger = False
    if initial_ledger.exists() or initial_ledger.is_symlink():
        if initial_ledger.is_symlink() or not initial_ledger.is_file():
            raise CampaignError("initial experiment ledger is unsafe")
        partial_initial_ledger = (initial_ledger.stat().st_mode & 0o777) != 0o444
    if partial_initial_ledger:
        canonical_index = campaign_root / "campaign_index.json"
        if (
            canonical_index.exists()
            or canonical_index.is_symlink()
            or index_temporaries
        ):
            raise CampaignError(
                "unsealed initial ledger coexists with campaign-index state"
            )
        attempts = campaign_root / "pair_attempts"
        if attempts.exists() or attempts.is_symlink():
            if attempts.is_symlink() or not attempts.is_dir():
                raise CampaignError("pair-attempt directory is unsafe")
            if any(attempts.rglob("*")):
                raise CampaignError(
                    "unsealed initial ledger coexists with pair-attempt state"
                )

    preserved: list[str] = []
    for source, pid in sorted(index_temporaries, key=lambda item: int(item[1])):
        destination = audit / (
            f"campaign_index_write.interrupted-pid-{pid}."
            f"recovered-slurm-{job_id}.json"
        )
        if destination.exists() or destination.is_symlink():
            raise CampaignError(
                f"staging-recovery audit destination already exists: {destination}"
            )
        os.rename(source, destination)
        fsync_directory(campaign_root)
        fsync_directory(audit)
        preserved.append(destination.relative_to(campaign_root).as_posix())
    if partial_initial_ledger:
        destination = audit / (
            "benchmark_task_checksums.initial.interrupted."
            f"recovered-slurm-{job_id}.sha256"
        )
        if destination.exists() or destination.is_symlink():
            raise CampaignError(
                f"initial-ledger recovery destination already exists: {destination}"
            )
        os.rename(initial_ledger, destination)
        fsync_directory(audit)
        preserved.append(destination.relative_to(campaign_root).as_posix())
    return {"preserved_staging_artifacts": preserved}


def index_path(campaign_root: Path) -> Path:
    return campaign_root / "campaign_index.json"


def load_and_verify_index(campaign_root: Path, benchmark_root: Path) -> dict[str, Any]:
    value = mapping(read_json(index_path(campaign_root), "campaign index"), "campaign index")
    index = dict(value)
    verify_index_hash(index)
    snapshot = metadata_snapshot(benchmark_root)
    paper_id = target_paper_id()
    target_pair = target_pair_id()
    for key in (
        "benchmark_id",
        "manifest",
        "run_order",
        "environment",
        "hardware_matching_policy",
        "hardware_matching_policy_sha256",
        "canonical_pairs",
    ):
        if index.get(key) != snapshot[key]:
            raise CampaignError(f"campaign index frozen field {key} is stale")
    if (
        set(index) != INDEX_FIELDS
        or index.get("schema_version") != INDEX_SCHEMA_VERSION
        or index.get("kind") != INDEX_KIND
        or index.get("paper_id") != paper_id
        or index.get("target_pair_id") != target_pair
        or not isinstance(index.get("committed_pairs"), dict)
        or not isinstance(index.get("failed_pair_attempts"), list)
        or index.get("active_pair_attempt") is not None
        and not isinstance(index.get("active_pair_attempt"), dict)
    ):
        raise CampaignError("campaign index header/state fields are invalid")
    created_at = utc_instant(index.get("created_at_utc"), "campaign creation time")
    updated_at = utc_instant(index.get("updated_at_utc"), "campaign update time")
    if created_at > updated_at:
        raise CampaignError("campaign creation time follows its update time")
    canonical_pair_ids = [
        str(pair["pair_id"]) for pair in snapshot["canonical_pairs"]
    ]
    pair_ids = set(canonical_pair_ids)
    if target_pair not in pair_ids:
        raise CampaignError("shard target is absent from canonical paper order")
    committed = index["committed_pairs"]
    if set(committed) not in (set(), {target_pair}):
        raise CampaignError(
            "shard committed-pair map is neither empty nor its exact target"
        )
    seen_paths: set[str] = set()
    committed_freezes: list[tuple[str, Mapping[str, Any]]] = []
    attempt_histories: dict[
        str, list[tuple[int, datetime, datetime | None, str]]
    ] = {pair_id: [] for pair_id in canonical_pair_ids}
    previous_committed_at: datetime | None = None
    prior_pair_commit_by_pair: dict[str, datetime | None] = {}
    for pair_id in ([target_pair] if target_pair in committed else []):
        prior_pair_commit_by_pair[pair_id] = previous_committed_at
        descriptor = committed[pair_id]
        item = mapping(descriptor, f"committed pair {pair_id}")
        if item.get("pair_id") != pair_id:
            raise CampaignError(f"committed-pair map key {pair_id} disagrees with descriptor")
        path_text = string(item.get("path"), "committed attempt path")
        if path_text in seen_paths:
            raise CampaignError(f"campaign index repeats attempt path {path_text}")
        seen_paths.add(path_text)
        verify_committed_index_descriptor(campaign_root, benchmark_root, index, item)
        started_at = utc_instant(
            item.get("started_at_utc"), f"committed pair {pair_id} start time"
        )
        committed_at = utc_instant(
            item.get("committed_at_utc"), f"committed pair {pair_id} commit time"
        )
        if started_at > committed_at:
            raise CampaignError(
                f"committed pair {pair_id} starts after its commit time"
            )
        if previous_committed_at is not None and previous_committed_at > started_at:
            raise CampaignError(
                f"committed pair {pair_id} overlaps or precedes the prior pair commit"
            )
        previous_committed_at = committed_at
        attempt_histories[pair_id].append(
            (
                attempt_number(item),
                started_at,
                committed_at,
                "committed",
            )
        )
        pair_root = resolve_below(
            campaign_root, path_text, f"committed pair {pair_id} path"
        )
        committed_freezes.append(
            (
                pair_id,
                mapping(
                    read_json(
                        pair_root / "freeze_check.json",
                        f"committed pair {pair_id} freeze",
                    ),
                    f"committed pair {pair_id} freeze",
                ),
            )
        )
    if committed_freezes:
        reference_pair_id, reference_freeze = committed_freezes[0]
        for pair_id, candidate_freeze in committed_freezes[1:]:
            try:
                run_matrix.verify_pair_policy_compatible_freeze_checks(
                    reference_freeze, candidate_freeze
                )
            except run_matrix.BenchmarkToolError as error:
                raise CampaignError(
                    f"committed pair {pair_id} is incompatible with the campaign "
                    f"reference pair {reference_pair_id}: {error}"
                ) from error
    for descriptor in index["failed_pair_attempts"]:
        item = mapping(descriptor, "failed pair attempt")
        pair_id = string(item.get("pair_id"), "failed pair ID")
        if pair_id != target_pair:
            raise CampaignError(f"failed attempt names another shard pair: {pair_id}")
        path_text = string(item.get("path"), "failed attempt path")
        if path_text in seen_paths:
            raise CampaignError(f"campaign index repeats attempt path {path_text}")
        seen_paths.add(path_text)
        verify_failed_index_descriptor(campaign_root, benchmark_root, index, item)
        failed_started_at = utc_instant(
            item.get("started_at_utc"), f"failed pair {pair_id} start time"
        )
        failed_archived_at = utc_instant(
            item.get("archived_at_utc"), f"failed pair {pair_id} archive time"
        )
        if failed_started_at > failed_archived_at:
            raise CampaignError(
                f"failed pair {pair_id} starts after its archive time"
            )
        attempt_histories[pair_id].append(
            (
                attempt_number(item),
                failed_started_at,
                failed_archived_at,
                "failed",
            )
        )
    active = index.get("active_pair_attempt")
    active_root_exists = False
    if active is not None:
        item = mapping(active, "active pair attempt")
        if set(item) != ACTIVE_FIELDS:
            raise CampaignError("active pair-attempt fields are not exact")
        pair_id = string(item.get("pair_id"), "active pair ID")
        if pair_id != target_pair or pair_id in committed:
            raise CampaignError("active pair attempt is noncanonical or already committed")
        active_path = string(item.get("path"), "active attempt path")
        if active_path in seen_paths:
            raise CampaignError("active pair-attempt path is already historical")
        validate_attempt_identity(item)
        expected_active_pair = target_pair if target_pair not in committed else None
        if pair_id != expected_active_pair:
            raise CampaignError(
                "active pair attempt is not the next canonical uncommitted pair"
            )
        attempt_histories[pair_id].append(
            (
                attempt_number(item),
                utc_instant(
                    item.get("started_at_utc"), "active pair-attempt start time"
                ),
                None,
                "active",
            )
        )
        root = resolve_below(campaign_root, active_path, "active attempt path")
        if root.exists() or root.is_symlink():
            if root.is_symlink() or not root.is_dir():
                raise CampaignError("active pair-attempt directory is unsafe")
            active_root_exists = True
    next_uncommitted_pair = target_pair if target_pair not in committed else None
    if next_uncommitted_pair is not None:
        prior_pair_commit_by_pair[next_uncommitted_pair] = previous_committed_at
    for pair_id, history in attempt_histories.items():
        if not history:
            continue
        ordered = sorted(history, key=lambda entry: entry[0])
        prior_pair_commit = prior_pair_commit_by_pair.get(pair_id)
        if prior_pair_commit is not None and prior_pair_commit > ordered[0][1]:
            raise CampaignError(
                f"pair {pair_id} first attempt starts before the prior canonical "
                "pair commit"
            )
        serials = [entry[0] for entry in ordered]
        if serials != list(range(1, len(ordered) + 1)):
            raise CampaignError(
                f"pair {pair_id} attempt serials are not unique and contiguous from 1"
            )
        for previous, current in zip(ordered, ordered[1:]):
            previous_terminal = previous[2]
            if previous_terminal is None or previous_terminal > current[1]:
                raise CampaignError(
                    f"pair {pair_id} attempt history overlaps or reverses chronology"
                )
        committed_positions = [
            position
            for position, entry in enumerate(ordered)
            if entry[3] == "committed"
        ]
        active_positions = [
            position for position, entry in enumerate(ordered) if entry[3] == "active"
        ]
        if committed_positions and committed_positions != [len(ordered) - 1]:
            raise CampaignError(
                f"pair {pair_id} has attempt history after its committed attempt"
            )
        if active_positions and active_positions != [len(ordered) - 1]:
            raise CampaignError(
                f"pair {pair_id} active attempt is not last in its history"
            )
        if pair_id != target_pair:
            raise CampaignError(
                f"another pair {pair_id} has history inside this shard"
            )
    attempts_root = campaign_root / "pair_attempts"
    actual_attempt_paths: set[str] = set()
    if attempts_root.exists() or attempts_root.is_symlink():
        if attempts_root.is_symlink() or not attempts_root.is_dir():
            raise CampaignError("campaign pair_attempts directory is unsafe")
        for pair_path in attempts_root.iterdir():
            if (
                pair_path.is_symlink()
                or not pair_path.is_dir()
                or pair_path.name != target_pair
            ):
                raise CampaignError(f"campaign has an unsafe/noncanonical pair path: {pair_path}")
            for attempt_path in pair_path.iterdir():
                if attempt_path.is_symlink() or not attempt_path.is_dir():
                    raise CampaignError(f"campaign has an unsafe attempt path: {attempt_path}")
                actual_attempt_paths.add(attempt_path.relative_to(campaign_root).as_posix())
    expected_attempt_paths = set(seen_paths)
    # ``begin`` durably reserves the active identity before creating the leaf
    # directory.  A missing active leaf is therefore the one intentional
    # exception to the disk/index equality rule; ``recover-active`` creates and
    # archives that interrupted setup intent.  Historical roots must all exist.
    if active is not None and active_root_exists:
        expected_attempt_paths.add(string(active.get("path"), "active attempt path"))
    if actual_attempt_paths != expected_attempt_paths:
        raise CampaignError(
            "campaign pair-attempt directories do not exactly match indexed history: "
            f"unindexed={sorted(actual_attempt_paths - expected_attempt_paths)}, "
            f"missing={sorted(expected_attempt_paths - actual_attempt_paths)}"
        )
    return index


def write_index(campaign_root: Path, index: Mapping[str, Any]) -> dict[str, Any]:
    updated = dict(index)
    updated["updated_at_utc"] = utc_now()
    updated = bind_index_hash(updated)
    atomic_write_json(index_path(campaign_root), updated)
    return updated


def initialize(campaign_root: Path, benchmark_root: Path) -> dict[str, Any]:
    path = index_path(campaign_root)
    if path.exists() or path.is_symlink():
        return load_and_verify_index(campaign_root, benchmark_root)
    snapshot = metadata_snapshot(benchmark_root)
    now = utc_now()
    index = {
        "schema_version": INDEX_SCHEMA_VERSION,
        "kind": INDEX_KIND,
        "paper_id": target_paper_id(),
        "target_pair_id": target_pair_id(),
        **snapshot,
        "committed_pairs": {},
        "failed_pair_attempts": [],
        "active_pair_attempt": None,
        "created_at_utc": now,
        "updated_at_utc": now,
    }
    bound = bind_index_hash(index)
    atomic_write_json(path, bound)
    for relative in ("pair_attempts", "runbook_audit"):
        directory = campaign_root / relative
        directory.mkdir(parents=True, exist_ok=True)
        if directory.is_symlink() or not directory.is_dir():
            raise CampaignError(f"campaign directory is unsafe: {directory}")
    return bound


def next_pair_id(index: Mapping[str, Any]) -> str | None:
    committed = mapping(index.get("committed_pairs"), "committed pairs")
    target = string(index.get("target_pair_id"), "shard target pair")
    return None if target in committed else target


def status_payload(index: Mapping[str, Any]) -> dict[str, Any]:
    next_pair = next_pair_id(index)
    return {
        "status": "complete" if next_pair is None else "incomplete",
        "paper_id": index["paper_id"],
        "target_pair_id": index["target_pair_id"],
        "committed_pair_count": len(index["committed_pairs"]),
        "planned_pair_count": 1,
        "failed_pair_attempt_count": len(index["failed_pair_attempts"]),
        "active_pair_attempt": index.get("active_pair_attempt"),
        "next_pair_id": next_pair,
        "campaign_index_sha256": index[INDEX_HASH_FIELD],
    }


def attempt_serial(index: Mapping[str, Any], pair_id: str) -> int:
    serials: list[int] = []
    descriptors: list[Mapping[str, Any]] = list(index["failed_pair_attempts"])
    committed = index["committed_pairs"].get(pair_id)
    if isinstance(committed, Mapping):
        descriptors.append(committed)
    active = index.get("active_pair_attempt")
    if isinstance(active, Mapping):
        descriptors.append(active)
    for descriptor in descriptors:
        if descriptor.get("pair_id") != pair_id:
            continue
        serials.append(attempt_number(descriptor))
    return max(serials, default=0) + 1


def validate_attempt_identity(value: Mapping[str, Any]) -> None:
    if not ACTIVE_FIELDS.issubset(value):
        raise CampaignError("pair-attempt identity fields are incomplete")
    pair_id = string(value.get("pair_id"), "pair-attempt pair ID")
    if PAIR_ID_RE.fullmatch(pair_id) is None:
        raise CampaignError(f"pair-attempt pair ID is noncanonical: {pair_id!r}")
    job_id = string(value.get("slurm_job_id"), "pair-attempt Slurm job ID")
    if JOB_ID_RE.fullmatch(job_id) is None:
        raise CampaignError("pair-attempt Slurm job ID is noncanonical")
    node = string(value.get("allocation_node"), "pair-attempt allocation node")
    if node not in VETTED_NODES:
        raise CampaignError("pair-attempt node is outside the vetted allowlist")
    attempt_id = string(value.get("attempt_id"), "pair-attempt ID")
    if re.fullmatch(rf"attempt-[1-9][0-9]*-slurm-{re.escape(job_id)}", attempt_id) is None:
        raise CampaignError("pair-attempt ID does not bind its Slurm job")
    expected_path = (Path("pair_attempts") / pair_id / attempt_id).as_posix()
    if value.get("path") != expected_path:
        raise CampaignError("pair-attempt path is not its canonical permanent path")
    string(value.get("started_at_utc"), "pair-attempt start time")


def attempt_number(value: Mapping[str, Any]) -> int:
    attempt_id = string(value.get("attempt_id"), "pair-attempt ID")
    match = re.fullmatch(
        r"attempt-([1-9][0-9]*)-slurm-[1-9][0-9]*", attempt_id
    )
    if match is None:
        raise CampaignError(f"indexed attempt ID is malformed: {attempt_id!r}")
    return int(match.group(1))


def begin_attempt(
    campaign_root: Path,
    index: dict[str, Any],
    pair_id: str,
    job_id: str,
    allocation_node: str,
) -> tuple[dict[str, Any], Path]:
    if index.get("active_pair_attempt") is not None:
        raise CampaignError("campaign already has an active pair attempt")
    expected = next_pair_id(index)
    if expected is None:
        raise CampaignError("the shard target pair is already committed")
    if pair_id != expected:
        raise CampaignError(f"next canonical pair is {expected}, not {pair_id}")
    if JOB_ID_RE.fullmatch(job_id) is None:
        raise CampaignError("Slurm job ID is not canonical")
    if allocation_node not in VETTED_NODES:
        raise CampaignError("allocation node is outside the vetted allowlist")
    serial = attempt_serial(index, pair_id)
    attempt_id = f"attempt-{serial}-slurm-{job_id}"
    relative = Path("pair_attempts") / pair_id / attempt_id
    root = campaign_root / relative
    if root.exists() or root.is_symlink():
        raise CampaignError(f"permanent pair-attempt path already exists: {root}")
    active = {
        "pair_id": pair_id,
        "attempt_id": attempt_id,
        "path": relative.as_posix(),
        "slurm_job_id": job_id,
        "allocation_node": allocation_node,
        "started_at_utc": utc_now(),
    }
    updated = dict(index)
    updated["active_pair_attempt"] = active
    updated = write_index(campaign_root, updated)
    try:
        root.mkdir(parents=True, exist_ok=False)
        fsync_directory(root.parent)
    except BaseException:
        # The index-first reservation is intentional.  If directory creation is
        # interrupted, the next launcher sees an active intent rather than an
        # unindexed attempt and can recover it without risking path reuse.
        raise
    return updated, root


def verify_self_hash(value: Mapping[str, Any], field: str, label: str) -> str:
    payload = dict(value)
    observed = hex64(payload.pop(field, None), f"{label} self-hash")
    if canonical_sha256(payload) != observed:
        raise CampaignError(f"{label} self-hash is stale")
    return observed


def write_matrix_exit_marker(
    pair_root: Path, pair_id: str, job_id: str, matrix_exit_code: int | None
) -> dict[str, Any]:
    validate_matrix_exit_code(matrix_exit_code, "matrix exit code")
    path = pair_root / MATRIX_EXIT_MARKER
    if path.exists() or path.is_symlink():
        raise CampaignError("campaign matrix-exit marker already exists")
    marker = {
        "schema_version": 1,
        "kind": "highambench-campaign-matrix-exit",
        "pair_id": pair_id,
        "slurm_job_id": job_id,
        "matrix_exit_code": matrix_exit_code,
        "recorded_at_utc": utc_now(),
    }
    marker["matrix_exit_record_sha256"] = canonical_sha256(marker)
    atomic_write_json(path, marker)
    return marker


def validate_matrix_exit_code(value: Any, label: str) -> int | None:
    if value is None:
        return None
    if isinstance(value, bool) or not isinstance(value, int) or not 0 <= value <= 255:
        raise CampaignError(f"{label} is not a null or shell exit code in [0, 255]")
    return value


def verify_matrix_exit_marker(
    pair_root: Path,
    pair_id: str,
    job_id: str,
    matrix_exit_code: int | None,
) -> dict[str, Any]:
    marker = mapping(
        read_json(pair_root / MATRIX_EXIT_MARKER, "campaign matrix-exit marker"),
        "campaign matrix-exit marker",
    )
    if set(marker) != {
        "schema_version",
        "kind",
        "pair_id",
        "slurm_job_id",
        "matrix_exit_code",
        "recorded_at_utc",
        "matrix_exit_record_sha256",
    }:
        raise CampaignError("campaign matrix-exit marker fields are not exact")
    verify_self_hash(
        marker, "matrix_exit_record_sha256", "campaign matrix-exit marker"
    )
    observed_exit_code = validate_matrix_exit_code(
        marker.get("matrix_exit_code"), "campaign matrix-exit marker code"
    )
    expected_exit_code = validate_matrix_exit_code(
        matrix_exit_code, "expected campaign matrix-exit code"
    )
    if (
        marker.get("schema_version") != 1
        or marker.get("kind") != "highambench-campaign-matrix-exit"
        or marker.get("pair_id") != pair_id
        or marker.get("slurm_job_id") != job_id
        or observed_exit_code != expected_exit_code
    ):
        raise CampaignError("campaign matrix-exit marker identity is stale")
    string(marker.get("recorded_at_utc"), "campaign matrix-exit marker time")
    return dict(marker)


def exact_setup_error_root(pair_root: Path) -> bool:
    """Return whether no runner evidence exists beyond the exit marker.

    The runner may create empty working directories before an early Slurm or
    frozen-environment failure, so directories are permitted.  Any other file,
    symlink, or special entry is useful-work/state evidence and disqualifies the
    narrowly scoped zero-provider setup-error classification.
    """

    marker = pair_root / MATRIX_EXIT_MARKER
    if marker.is_symlink() or not marker.is_file():
        return False
    for path in pair_root.rglob("*"):
        if path.is_symlink() or (not path.is_dir() and not path.is_file()):
            return False
        if path.is_file() and path != marker:
            return False
    return True


def authenticate_present_incidents(
    pair_root: Path,
    assignments: Sequence[Mapping[str, Any]],
    freeze: Mapping[str, Any] | None,
) -> list[dict[str, Any]]:
    """Authenticate every canonical incident JSON currently present in a pair root."""

    incidents = pair_root / "incidents"
    if not incidents.exists() and not incidents.is_symlink():
        return []
    if incidents.is_symlink() or not incidents.is_dir():
        raise CampaignError("failed pair incidents directory is unsafe")
    authenticated: list[dict[str, Any]] = []
    for assignment in assignments:
        run_id = string(assignment.get("run_id"), "failed-pair assignment run ID")
        for attempt in (1, 2):
            path = incidents / f"{run_id}.attempt-{attempt}.json"
            if not path.exists() and not path.is_symlink():
                continue
            if freeze is None:
                raise CampaignError(
                    "failed pair incident exists without a frozen run record"
                )
            try:
                authenticated.append(
                    run_matrix._authenticate_matrix_incident(
                        pair_root,
                        path,
                        assignment,
                        freeze,
                        expected_attempt=attempt,
                    )
                )
            except run_matrix.BenchmarkToolError as error:
                raise CampaignError(
                    f"failed pair incident authentication failed: {error}"
                ) from error
    return authenticated


def authenticated_incident_artifact_names(
    pair_root: Path,
    incidents: Sequence[Mapping[str, Any]],
) -> set[str]:
    """Return exact incident-directory artifacts bound by authenticated JSON."""

    names: set[str] = set()
    for offset, incident in enumerate(incidents):
        for field in ("agent_log", "validation_log"):
            raw = incident.get(field)
            digest_field = f"{field}_sha256"
            if raw is None:
                if incident.get(digest_field) is not None:
                    raise CampaignError(
                        f"authenticated incident {offset} has {digest_field} without {field}"
                    )
                continue
            relative = safe_relative_path(
                raw, f"authenticated incident {offset} {field} path"
            )
            if relative.parent != Path("incidents") or relative.suffix != ".artifact":
                raise CampaignError(
                    f"authenticated incident {offset} {field} is not an incidents/*.artifact path"
                )
            path = resolve_below(
                pair_root,
                relative.as_posix(),
                f"authenticated incident {offset} {field}",
            )
            if path.is_symlink() or not path.is_file():
                raise CampaignError(
                    f"authenticated incident {offset} {field} is missing or unsafe"
                )
            digest = hex64(
                incident.get(digest_field),
                f"authenticated incident {offset} {field} SHA-256",
            )
            if file_sha256(path) != digest:
                raise CampaignError(
                    f"authenticated incident {offset} {field} SHA-256 is stale"
                )
            names.add(relative.name)
    return names


def validate_failed_runner_temporaries(
    pair_root: Path,
    assignments: Sequence[Mapping[str, Any]],
    *,
    authenticated_incidents: Sequence[Mapping[str, Any]] = (),
) -> None:
    """Allow exact write remnants and authenticated incident-owned artifacts."""

    run_ids = {str(item["run_id"]) for item in assignments}
    allowed_targets = {
        "records": {f"{run_id}.json" for run_id in run_ids},
        "incidents": {
            f"{run_id}.attempt-{attempt}.json"
            for run_id in run_ids
            for attempt in (1, 2)
        },
    }
    allowed_targets["incidents"].update(
        authenticated_incident_artifact_names(pair_root, authenticated_incidents)
    )
    temporary = re.compile(r"\.(.+\.json)\.tmp-([1-9][0-9]*)")
    for directory_name, target_names in allowed_targets.items():
        directory = pair_root / directory_name
        if not directory.exists() and not directory.is_symlink():
            continue
        if directory.is_symlink() or not directory.is_dir():
            raise CampaignError(
                f"failed pair {directory_name} directory is unsafe"
            )
        for path in directory.iterdir():
            if path.name in target_names:
                if path.is_symlink() or not path.is_file():
                    raise CampaignError(
                        f"failed pair {directory_name} artifact is unsafe: {path}"
                    )
                continue
            match = temporary.fullmatch(path.name)
            if (
                match is None
                or match.group(1) not in target_names
                or path.is_symlink()
                or not path.is_file()
            ):
                raise CampaignError(
                    f"failed pair {directory_name} directory has a foreign/unsafe "
                    f"write temporary: {path}"
                )


def has_failed_runner_temporaries(pair_root: Path) -> bool:
    for directory_name in ("records", "incidents"):
        directory = pair_root / directory_name
        if not directory.is_dir() or directory.is_symlink():
            continue
        if any(
            re.fullmatch(r"\..+\.json\.tmp-[1-9][0-9]*", path.name)
            is not None
            for path in directory.iterdir()
        ):
            return True
    return False


def verify_active_run_marker(
    pair_root: Path,
    assignments: Sequence[Mapping[str, Any]],
    freeze: Mapping[str, Any],
) -> None:
    """Authenticate retained in-flight evidence without clearing its marker."""

    marker_path = pair_root / run_matrix.ACTIVE_RUN_MARKER
    marker = mapping(
        read_json(marker_path, "failed-pair active-run marker"),
        "failed-pair active-run marker",
    )
    exact_fields = {
        "schema_version",
        "kind",
        "assignment",
        "attempt",
        "attempt_output",
        "started_at_unix",
        "allocation_hardware",
    }
    planned_by_run_id = {str(item["run_id"]): item for item in assignments}
    marker_assignment = mapping(
        marker.get("assignment"), "failed-pair active-run assignment"
    )
    run_id = string(
        marker_assignment.get("run_id"), "failed-pair active-run ID"
    )
    planned = planned_by_run_id.get(run_id)
    attempt = marker.get("attempt")
    started_at = marker.get("started_at_unix")
    if (
        set(marker) != exact_fields
        or marker.get("schema_version") != run_matrix.ACTIVE_RUN_MARKER_SCHEMA_VERSION
        or marker.get("kind") != "highambench-active-hosted-attempt"
        or planned is None
        or dict(marker_assignment)
        != run_matrix._planned_assignment_record_identity(planned)
        or isinstance(attempt, bool)
        or attempt not in {1, 2}
        or isinstance(started_at, bool)
        or not isinstance(started_at, (int, float))
        or started_at <= 0
        or marker.get("attempt_output")
        != f"attempts/{run_id}.attempt-{attempt}.json"
    ):
        raise CampaignError("failed-pair active-run marker is not exact")
    allocation = mapping(
        marker.get("allocation_hardware"),
        "failed-pair active-run allocation descriptor",
    )
    run_matrix.verify_allocation_hardware_descriptor(pair_root, allocation, freeze)


def validate_final_descriptor(
    pair_root: Path,
    pair_id: str,
    condition: str,
    descriptor: Mapping[str, Any],
) -> dict[str, Any]:
    run_id = f"{pair_id}-{condition}"
    if descriptor.get("run_id") != run_id:
        raise CampaignError(f"pair commit changed the {condition} run ID")
    relative = safe_relative_path(descriptor.get("path"), f"{condition} final path")
    if relative != Path("records") / f"{run_id}.json":
        raise CampaignError(f"pair commit has a noncanonical {condition} final path")
    path = pair_root / relative
    record = mapping(read_json(path, f"{condition} final record"), f"{condition} final record")
    if (
        record.get("run_id") != run_id
        or record.get("pair_id") != pair_id
        or record.get("condition") != condition
        or record.get("paper_id") != target_paper_id()
    ):
        raise CampaignError(f"{condition} final identity is invalid")
    matrix_hash = verify_self_hash(record, "matrix_record_sha256", f"{condition} final")
    digest = file_sha256(path)
    if descriptor.get("sha256") != digest or descriptor.get("matrix_record_sha256") != matrix_hash:
        raise CampaignError(f"pair commit has stale {condition} final hashes")
    return {
        "run_id": run_id,
        "path": relative.as_posix(),
        "sha256": digest,
        "matrix_record_sha256": matrix_hash,
    }


def committed_descriptor(
    campaign_root: Path,
    benchmark_root: Path,
    index: Mapping[str, Any],
    active: Mapping[str, Any],
    *,
    committed_at_utc: str | None = None,
) -> dict[str, Any]:
    if set(active) != ACTIVE_FIELDS:
        raise CampaignError("committed pair identity fields are not exact")
    validate_attempt_identity(active)
    pair_id = string(active.get("pair_id"), "active pair ID")
    pair_root = resolve_below(campaign_root, active.get("path"), "active pair path")
    active_marker = pair_root / run_matrix.ACTIVE_RUN_MARKER
    if active_marker.exists() or active_marker.is_symlink():
        raise CampaignError("complete pair root retains an active-run marker")
    verify_matrix_exit_marker(
        pair_root,
        pair_id,
        string(active.get("slurm_job_id"), "active Slurm job ID"),
        0,
    )
    freeze = mapping(read_json(pair_root / "freeze_check.json", "pair freeze check"), "pair freeze check")
    verify_pair_freeze_against_metadata(benchmark_root, freeze, index)
    assignments = planned_pair_assignments(benchmark_root, pair_id)
    authenticated_finals = run_matrix._authenticate_existing_final_records(
        pair_root, pair_root / "records", assignments, freeze
    )
    if set(authenticated_finals) != {item["run_id"] for item in assignments}:
        raise CampaignError("pair root does not contain exactly two authenticated finals")
    authenticated_incidents = run_matrix._authenticate_existing_incidents(
        pair_root,
        pair_root / "incidents",
        assignments,
        freeze,
        authenticated_finals,
    )
    validate_failed_runner_temporaries(
        pair_root,
        assignments,
        authenticated_incidents=[
            incident
            for per_run in authenticated_incidents.values()
            for incident in per_run.values()
        ],
    )
    if has_failed_runner_temporaries(pair_root):
        raise CampaignError("complete pair root retains a runner write temporary")
    records_directory = pair_root / "records"
    expected_record_names = {
        f"{item['run_id']}.json" for item in assignments
    }
    if {
        path.name
        for path in records_directory.iterdir()
        if path.is_file() and not path.is_symlink()
    } != expected_record_names or any(
        path.is_symlink() or not path.is_file()
        for path in records_directory.iterdir()
    ):
        raise CampaignError("complete pair records directory is not exact")
    commit_path = pair_root / "pair_commit.json"
    if commit_path.is_symlink() or not commit_path.is_file():
        raise CampaignError("pair root lacks a regular immutable pair_commit.json")
    commit = run_matrix.verify_pair_commit(pair_root, assignments, freeze)
    commit_self_hash = hex64(commit.get("pair_commit_sha256"), "pair commit self-hash")
    pair = next(item for item in index["canonical_pairs"] if item["pair_id"] == pair_id)
    if commit.get("condition_order") != pair["condition_order"] or commit.get("run_ids") != pair["run_ids"]:
        raise CampaignError("pair commit changed the canonical condition order")
    finals = mapping(commit.get("final_records"), "pair-commit finals")
    if set(finals) != {"N", "L"}:
        raise CampaignError("pair commit does not contain exact N/L finals")
    final_records = {
        condition: validate_final_descriptor(
            pair_root,
            pair_id,
            condition,
            mapping(finals[condition], f"{condition} final descriptor"),
        )
        for condition in ("N", "L")
    }
    allocation = mapping(commit.get("allocation_hardware"), "pair allocation descriptor")
    allocation_record = run_matrix.verify_allocation_hardware_descriptor(
        pair_root, allocation, freeze
    )
    if (
        allocation.get("job_id") != active.get("slurm_job_id")
        or allocation_record.get("job_id") != active.get("slurm_job_id")
        or allocation_record.get("hostname") != active.get("allocation_node")
    ):
        raise CampaignError("pair allocation does not match its permanent attempt identity")
    if final_records["N"] == final_records["L"]:
        raise CampaignError("pair commit aliases its N and L final records")
    for condition in ("N", "L"):
        record = mapping(
            read_json(pair_root / final_records[condition]["path"], f"{condition} final"),
            f"{condition} final",
        )
        if record.get("allocation_hardware") != allocation:
            raise CampaignError("N/L allocation descriptors are not exactly identical")
    policy_hash = hex64(commit.get("hardware_matching_policy_sha256"), "pair policy hash")
    if policy_hash != index["hardware_matching_policy_sha256"]:
        raise CampaignError("pair commit hardware policy does not match the campaign")
    freeze_hash = hex64(commit.get("freeze_check_sha256"), "pair freeze hash")
    if freeze_hash != run_matrix.canonical_document_digest(freeze):
        raise CampaignError("pair commit does not bind its root freeze check")
    expected_status = {
        "schema_version": 1,
        "kind": "highambench-matrix-chunk-status",
        "status": "stopped_after_requested_pair",
        "pair_id": pair_id,
        "completed_runs": 2,
        "planned_runs": 2,
        "pair_commit": run_matrix.pair_commit_descriptor(pair_root, commit),
    }
    status = mapping(read_json(pair_root / "last_chunk_status.json", "pair status"), "pair status")
    if dict(status) != expected_status:
        raise CampaignError("pair root lacks its exact successful boundary status")
    summary = recursive_tree_summary(pair_root)
    relative = safe_relative_path(active.get("path"), "active pair path")
    committed_at = committed_at_utc or utc_now()
    string(committed_at, "pair commit time")
    return {
        "pair_id": pair_id,
        "attempt_id": string(active.get("attempt_id"), "active attempt ID"),
        "path": relative.as_posix(),
        "slurm_job_id": string(active.get("slurm_job_id"), "active Slurm job ID"),
        "allocation_node": string(active.get("allocation_node"), "active allocation node"),
        "started_at_utc": string(active.get("started_at_utc"), "active start time"),
        "committed_at_utc": committed_at,
        **summary,
        "pair_commit": {
            "path": (relative / "pair_commit.json").as_posix(),
            "sha256": file_sha256(commit_path),
            "pair_commit_sha256": commit_self_hash,
        },
        "final_records": final_records,
        "allocation_hardware": json.loads(json.dumps(allocation)),
        "freeze_check_sha256": freeze_hash,
        "hardware_matching_policy_sha256": policy_hash,
}


def verify_committed_index_descriptor(
    campaign_root: Path,
    benchmark_root: Path,
    index: Mapping[str, Any],
    descriptor: Mapping[str, Any],
) -> None:
    if set(descriptor) != COMMITTED_FIELDS:
        raise CampaignError("committed pair descriptor fields are not exact")
    identity = {field: descriptor[field] for field in ACTIVE_FIELDS}
    expected = committed_descriptor(
        campaign_root,
        benchmark_root,
        index,
        identity,
        committed_at_utc=string(
            descriptor.get("committed_at_utc"), "indexed pair commit time"
        ),
    )
    if dict(descriptor) != expected:
        raise CampaignError(
            f"committed pair descriptor for {descriptor.get('pair_id')!r} is stale"
        )


def commit_attempt(
    campaign_root: Path,
    benchmark_root: Path,
    index: dict[str, Any],
    pair_id: str,
    job_id: str,
) -> dict[str, Any]:
    active = mapping(index.get("active_pair_attempt"), "active pair attempt")
    if active.get("pair_id") != pair_id or active.get("slurm_job_id") != job_id:
        raise CampaignError("active pair attempt does not match commit request")
    descriptor = committed_descriptor(campaign_root, benchmark_root, index, active)
    committed = dict(index["committed_pairs"])
    if pair_id in committed:
        raise CampaignError(f"pair {pair_id} is already committed")
    committed[pair_id] = descriptor
    updated = dict(index)
    updated["committed_pairs"] = committed
    updated["active_pair_attempt"] = None
    return write_index(campaign_root, updated)


def optional_file_descriptor(root: Path, path: Path) -> dict[str, Any] | None:
    if not path.exists() and not path.is_symlink():
        return None
    if path.is_symlink() or not path.is_file():
        raise CampaignError(f"optional attempt artifact is unsafe: {path}")
    value = read_json(path, "optional attempt artifact")
    return {
        "path": path.relative_to(root).as_posix(),
        "sha256": file_sha256(path),
        "value": value,
    }


def validate_zero_work_deadline(
    pair_root: Path,
    pair_id: str,
    expected_next_run_id: str,
    status: Mapping[str, Any],
    *,
    final_count: int,
    incident_count: int,
) -> None:
    exact_fields = {
        "schema_version",
        "kind",
        "status",
        "next_run_id",
        "next_pair_id",
        "unfinished_runs_in_next_pair",
        "allocation_end_epoch",
        "remaining_seconds",
        "required_seconds",
        "prompt_startup_timeout_seconds",
        "startup_timeouts_reserved_per_unfinished_run",
        "post_submission_validation_reserve_seconds",
        "guard_seconds",
    }
    numeric_fields = (
        "allocation_end_epoch",
        "remaining_seconds",
        "required_seconds",
        "prompt_startup_timeout_seconds",
        "post_submission_validation_reserve_seconds",
        "guard_seconds",
    )
    if (
        set(status) != exact_fields
        or status.get("schema_version") != 1
        or status.get("kind") != "highambench-matrix-chunk-status"
        or status.get("status") != "stopped_before_allocation_deadline"
        or status.get("next_pair_id") != pair_id
        or status.get("next_run_id") != expected_next_run_id
        or status.get("unfinished_runs_in_next_pair") != 2
        or status.get("startup_timeouts_reserved_per_unfinished_run") != 2
        or status.get("prompt_startup_timeout_seconds")
        != run_matrix.DEFAULT_PROMPT_STARTUP_TIMEOUT_SECONDS
        or status.get("post_submission_validation_reserve_seconds")
        != run_matrix.DEFAULT_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS
        or any(
            isinstance(status.get(field), bool)
            or not isinstance(status.get(field), (int, float))
            for field in numeric_fields
        )
        or status.get("allocation_end_epoch", 0) <= 0
        or status.get("required_seconds", 0) <= 0
        or status.get("guard_seconds", -1) < 0
        or status.get("remaining_seconds", 0) >= status.get("required_seconds", 0)
        or final_count != 0
        or incident_count != 0
    ):
        raise CampaignError("deadline-before-pair status is not exact and zero-work")
    attempts = pair_root / "attempts"
    if attempts.exists() and (
        attempts.is_symlink()
        or not attempts.is_dir()
        or any(attempts.iterdir())
    ):
        raise CampaignError("deadline-before-pair attempt directory is not empty")
    marker = pair_root / run_matrix.ACTIVE_RUN_MARKER
    if marker.exists() or marker.is_symlink():
        raise CampaignError("deadline-before-pair root has an active-run marker")
    runs = pair_root / "runs.jsonl"
    if runs.exists() or runs.is_symlink():
        if runs.is_symlink() or not runs.is_file() or runs.read_text(encoding="utf-8").strip():
            raise CampaignError("deadline-before-pair run ledger is nonempty or unsafe")


def verify_failed_index_descriptor(
    campaign_root: Path,
    benchmark_root: Path,
    index: Mapping[str, Any],
    descriptor: Mapping[str, Any],
) -> None:
    if set(descriptor) != FAILED_FIELDS:
        raise CampaignError("failed pair-attempt descriptor fields are not exact")
    validate_attempt_identity(descriptor)
    pair_id = string(descriptor.get("pair_id"), "failed pair ID")
    pair_root = resolve_below(campaign_root, descriptor.get("path"), "failed attempt path")
    verify_matrix_exit_marker(
        pair_root,
        pair_id,
        string(descriptor.get("slurm_job_id"), "failed Slurm job ID"),
        descriptor.get("matrix_exit_code"),
    )
    assignments = planned_pair_assignments(benchmark_root, pair_id)
    freeze_path = pair_root / "freeze_check.json"
    freeze: Mapping[str, Any] | None = None
    if freeze_path.exists() or freeze_path.is_symlink():
        freeze = mapping(read_json(freeze_path, "failed-pair freeze"), "failed-pair freeze")
        verify_pair_freeze_against_metadata(benchmark_root, freeze, index)
    authenticated_present_incidents = authenticate_present_incidents(
        pair_root, assignments, freeze
    )
    validate_failed_runner_temporaries(
        pair_root,
        assignments,
        authenticated_incidents=authenticated_present_incidents,
    )
    active_marker_path = pair_root / run_matrix.ACTIVE_RUN_MARKER
    active_marker_exists = active_marker_path.exists() or active_marker_path.is_symlink()
    if active_marker_exists:
        if freeze is None:
            raise CampaignError("failed-pair active-run marker exists without a freeze")
        verify_active_run_marker(pair_root, assignments, freeze)
    incidents = descriptor.get("incidents")
    if not isinstance(incidents, list):
        raise CampaignError("failed pair incident descriptors are invalid")
    expected_incidents: list[dict[str, Any]] = []
    incident_statuses: list[str] = []
    for raw in incidents:
        item = mapping(raw, "failed pair incident descriptor")
        if set(item) != {"path", "sha256", "matrix_incident_sha256"}:
            raise CampaignError("failed pair incident descriptor fields are not exact")
        relative = safe_relative_path(item.get("path"), "failed incident path")
        path = pair_root / relative
        incident = mapping(read_json(path, "failed matrix incident"), "failed matrix incident")
        digest = hex64(incident.get("matrix_incident_sha256"), "matrix incident self-hash")
        if digest != run_matrix.matrix_incident_digest(incident):
            raise CampaignError("failed matrix incident self-hash is stale")
        planned_run_id = string(incident.get("planned_run_id"), "incident planned run ID")
        if planned_run_id not in {item["run_id"] for item in assignments}:
            raise CampaignError("failed matrix incident belongs to another pair")
        if freeze is None:
            raise CampaignError("failed matrix incident exists without a frozen run record")
        assignment = next(
            item for item in assignments if item["run_id"] == planned_run_id
        )
        matrix_attempt = incident.get("matrix_attempt")
        if isinstance(matrix_attempt, bool) or matrix_attempt not in {1, 2}:
            raise CampaignError("failed matrix incident has an invalid attempt number")
        run_matrix._authenticate_matrix_incident(
            pair_root,
            path,
            assignment,
            freeze,
            expected_attempt=matrix_attempt,
        )
        incident_statuses.append(
            string(
                mapping(incident.get("matrix_incident"), "incident control").get(
                    "status"
                ),
                "incident status",
            )
        )
        expected_incidents.append(
            {
                "path": relative.as_posix(),
                "sha256": file_sha256(path),
                "matrix_incident_sha256": digest,
            }
        )
    if incidents != expected_incidents:
        raise CampaignError("failed pair incident descriptor list is stale")
    incident_directory = pair_root / "incidents"
    actual_incident_paths = (
        []
        if not incident_directory.exists()
        else sorted(
            path.relative_to(pair_root).as_posix()
            for path in incident_directory.glob("*.json")
        )
    )
    if actual_incident_paths != [item["path"] for item in expected_incidents]:
        raise CampaignError("failed pair incident descriptor set is incomplete")
    records = pair_root / "records"
    record_paths = [] if not records.exists() else sorted(records.glob("*.json"))
    if records.exists() and (records.is_symlink() or not records.is_dir()):
        raise CampaignError("failed pair records directory is unsafe")
    outcome = descriptor.get("outcome")
    exact_two_final_matrix_error = (
        outcome == "matrix_error"
        and descriptor.get("matrix_exit_code") == 2
        and len(record_paths) == 2
    )
    if (
        descriptor.get("final_record_count") != len(record_paths)
        or len(record_paths) > 2
        or (len(record_paths) == 2 and not exact_two_final_matrix_error)
    ):
        raise CampaignError("failed pair final-record count is invalid")
    for path in record_paths:
        record = mapping(read_json(path, "failed-pair partial final"), "failed-pair partial final")
        if record.get("pair_id") != pair_id or record.get("run_id") not in {
            item["run_id"] for item in assignments
        }:
            raise CampaignError("failed-pair partial final belongs to another pair")
        if run_matrix.matrix_record_digest(record) != record.get("matrix_record_sha256"):
            raise CampaignError("failed-pair partial final self-hash is stale")
        if freeze is None:
            raise CampaignError("partial final exists without a frozen run record")
        assignment = next(
            item for item in assignments if item["run_id"] == record.get("run_id")
        )
        run_matrix._authenticate_final_assignment_record(
            pair_root, path, assignment, freeze
        )
    authenticated_finals: dict[str, Mapping[str, Any]] = {}
    if len(record_paths) == 2:
        if freeze is None:
            raise CampaignError("two failed-pair finals exist without a freeze")
        authenticated_finals = run_matrix._authenticate_existing_final_records(
            pair_root, records, assignments, freeze
        )
        if set(authenticated_finals) != {
            str(item["run_id"]) for item in assignments
        }:
            raise CampaignError(
                "failed two-final pair does not contain exact authenticated N/L finals"
            )
    pair_commit_path = pair_root / "pair_commit.json"
    pair_commit: Mapping[str, Any] | None = None
    if pair_commit_path.exists() or pair_commit_path.is_symlink():
        if len(record_paths) != 2 or freeze is None:
            raise CampaignError("failed partial pair has an impossible pair commit")
        if pair_commit_path.is_symlink() or not pair_commit_path.is_file():
            raise CampaignError("failed pair commit is missing or unsafe")
        pair_commit = run_matrix.verify_pair_commit(
            pair_root, assignments, freeze
        )
    status_descriptor = descriptor.get("last_chunk_status")
    expected_status = optional_file_descriptor(
        pair_root, pair_root / "last_chunk_status.json"
    )
    if status_descriptor != expected_status:
        raise CampaignError("failed pair last-chunk descriptor is stale")
    if len(record_paths) == 2 and expected_status is not None:
        if pair_commit is None:
            raise CampaignError("failed two-final pair status exists without a pair commit")
        exact_pair_status = {
            "schema_version": 1,
            "kind": "highambench-matrix-chunk-status",
            "status": "stopped_after_requested_pair",
            "pair_id": pair_id,
            "completed_runs": 2,
            "planned_runs": 2,
            "pair_commit": run_matrix.pair_commit_descriptor(
                pair_root, pair_commit
            ),
        }
        if expected_status.get("value") != exact_pair_status:
            raise CampaignError("failed two-final pair status is not exact")
    if outcome == "allocation_deadline_before_pair":
        if (
            descriptor.get("matrix_exit_code") != run_matrix.CHUNK_INCOMPLETE_EXIT_CODE
            or not isinstance(expected_status, Mapping)
        ):
            raise CampaignError("deadline-before-pair archive is not exact and zero-work")
        validate_zero_work_deadline(
            pair_root,
            pair_id,
            assignments[0]["run_id"],
            mapping(expected_status.get("value"), "deadline status"),
            final_count=len(record_paths),
            incident_count=len(incidents),
        )
    elif outcome == "matrix_error":
        if descriptor.get("matrix_exit_code") in {0, run_matrix.CHUNK_INCOMPLETE_EXIT_CODE}:
            raise CampaignError("matrix-error archive has a success/deadline exit code")
        terminal = {
            "terminal_pre_prompt_system_error",
            "aborted_after_unscorable_useful_work",
        }
        setup_error = (
            not incident_statuses
            and not record_paths
            and not active_marker_exists
            and exact_setup_error_root(pair_root)
        )
        # A runner-level error may occur after one member of the pair has a
        # fully authenticated final but before the mate completes.  Preserve
        # that final only as failed-attempt evidence; the next permanent root
        # reruns both N and L and never promotes this partial pair.
        partial_pair_matrix_error = (
            descriptor.get("matrix_exit_code") == 2
            and len(record_paths) in {1, 2}
        )
        interrupted_write_matrix_error = (
            descriptor.get("matrix_exit_code") == 2
            and not record_paths
            and has_failed_runner_temporaries(pair_root)
        )
        if not terminal.intersection(incident_statuses) and not (
            active_marker_exists
        ) and not setup_error and not partial_pair_matrix_error and not interrupted_write_matrix_error:
            raise CampaignError(
                "matrix-error archive is neither an exact setup error nor a "
                "terminal/unscorable/active/partial-pair attempt"
            )
    elif outcome == "interrupted_job":
        if descriptor.get("matrix_exit_code") is not None:
            raise CampaignError("interrupted-job archive has a non-null matrix exit code")
    else:
        raise CampaignError(f"failed pair outcome is invalid: {outcome!r}")
    if utc_instant(
        descriptor.get("started_at_utc"), "failed pair start time"
    ) > utc_instant(
        descriptor.get("archived_at_utc"), "failed pair archive time"
    ):
        raise CampaignError("failed pair starts after its archive time")
    summary = recursive_tree_summary(pair_root)
    for key in ("file_count", "total_bytes", "tree_sha256"):
        if descriptor.get(key) != summary[key]:
            raise CampaignError(f"failed pair descriptor has stale {key}")


def archive_failed_attempt(
    campaign_root: Path,
    benchmark_root: Path,
    index: dict[str, Any],
    pair_id: str,
    job_id: str,
    matrix_exit_code: int | None,
    outcome: str,
) -> dict[str, Any]:
    if matrix_exit_code == 0:
        raise CampaignError("a successful matrix exit must be committed, not archived")
    active = mapping(index.get("active_pair_attempt"), "active pair attempt")
    if active.get("pair_id") != pair_id or active.get("slurm_job_id") != job_id:
        raise CampaignError("active pair attempt does not match archive request")
    pair_root = resolve_below(campaign_root, active.get("path"), "active pair path")
    exit_marker = verify_matrix_exit_marker(
        pair_root, pair_id, job_id, matrix_exit_code
    )
    assignments = planned_pair_assignments(benchmark_root, pair_id)
    freeze_path = pair_root / "freeze_check.json"
    archive_freeze: Mapping[str, Any] | None = None
    if freeze_path.exists() or freeze_path.is_symlink():
        archive_freeze = mapping(
            read_json(freeze_path, "failed-pair freeze"), "failed-pair freeze"
        )
    validate_failed_runner_temporaries(
        pair_root,
        assignments,
        authenticated_incidents=authenticate_present_incidents(
            pair_root, assignments, archive_freeze
        ),
    )
    incident_descriptors: list[dict[str, Any]] = []
    incidents = pair_root / "incidents"
    if incidents.exists() or incidents.is_symlink():
        if incidents.is_symlink() or not incidents.is_dir():
            raise CampaignError("pair incident directory is unsafe")
        for path in sorted(incidents.glob("*.json")):
            incident = mapping(read_json(path, "matrix incident"), "matrix incident")
            incident_digest = hex64(
                incident.get("matrix_incident_sha256"), "matrix incident self-hash"
            )
            if incident_digest != run_matrix.matrix_incident_digest(incident):
                raise CampaignError("matrix incident self-hash is stale")
            incident_descriptors.append(
                {
                    "path": path.relative_to(pair_root).as_posix(),
                    "sha256": file_sha256(path),
                    "matrix_incident_sha256": incident_digest,
                }
            )
    records = pair_root / "records"
    final_count = 0
    if records.exists() or records.is_symlink():
        if records.is_symlink() or not records.is_dir():
            raise CampaignError("pair records directory is unsafe")
        final_count = len(list(records.glob("*.json")))
    if final_count > 2:
        raise CampaignError("failed pair attempt unexpectedly has two final records")
    status = optional_file_descriptor(pair_root, pair_root / "last_chunk_status.json")
    if outcome == "allocation_deadline_before_pair":
        status_value = None if status is None else mapping(status.get("value"), "deadline status")
        if (
            matrix_exit_code != run_matrix.CHUNK_INCOMPLETE_EXIT_CODE
            or status_value is None
        ):
            raise CampaignError("deadline-before-pair attempt is not exact and zero-work")
        validate_zero_work_deadline(
            pair_root,
            pair_id,
            assignments[0]["run_id"],
            status_value,
            final_count=final_count,
            incident_count=len(incident_descriptors),
        )
    elif outcome == "matrix_error":
        if matrix_exit_code in {0, run_matrix.CHUNK_INCOMPLETE_EXIT_CODE}:
            raise CampaignError("matrix-error archive has a success/deadline exit code")
        terminal = False
        for item in incident_descriptors:
            incident = mapping(
                read_json(pair_root / item["path"], "matrix incident"),
                "matrix incident",
            )
            status_value = mapping(
                incident.get("matrix_incident"), "matrix incident control"
            ).get("status")
            terminal = terminal or status_value in {
                "terminal_pre_prompt_system_error",
                "aborted_after_unscorable_useful_work",
            }
        setup_error = (
            not incident_descriptors
            and final_count == 0
            and not (pair_root / run_matrix.ACTIVE_RUN_MARKER).exists()
            and not (pair_root / run_matrix.ACTIVE_RUN_MARKER).is_symlink()
            and exact_setup_error_root(pair_root)
        )
        partial_pair_matrix_error = matrix_exit_code == 2 and final_count in {1, 2}
        interrupted_write_matrix_error = (
            matrix_exit_code == 2
            and final_count == 0
            and has_failed_runner_temporaries(pair_root)
        )
        if (
            not terminal
            and not (pair_root / run_matrix.ACTIVE_RUN_MARKER).is_file()
            and not setup_error
            and not partial_pair_matrix_error
            and not interrupted_write_matrix_error
        ):
            raise CampaignError(
                "matrix-error archive is neither an exact setup error nor a "
                "terminal/unscorable/active/partial-pair attempt"
            )
    elif outcome == "interrupted_job":
        if matrix_exit_code is not None:
            raise CampaignError("interrupted-job archive must have a null matrix exit code")
        if exit_marker.get("matrix_exit_code") is not None:
            raise CampaignError("interrupted-job exit marker must record null")
    else:
        raise CampaignError(f"invalid failed-pair outcome: {outcome!r}")
    summary = recursive_tree_summary(pair_root)
    relative = safe_relative_path(active.get("path"), "active pair path")
    descriptor = {
        "pair_id": pair_id,
        "attempt_id": string(active.get("attempt_id"), "active attempt ID"),
        "path": relative.as_posix(),
        "slurm_job_id": job_id,
        "allocation_node": string(active.get("allocation_node"), "active allocation node"),
        "started_at_utc": string(active.get("started_at_utc"), "active start time"),
        "archived_at_utc": utc_now(),
        "outcome": outcome,
        "matrix_exit_code": matrix_exit_code,
        "final_record_count": final_count,
        "incidents": incident_descriptors,
        "last_chunk_status": status,
        **summary,
    }
    verify_failed_index_descriptor(
        campaign_root, benchmark_root, index, descriptor
    )
    failed = list(index["failed_pair_attempts"])
    failed.append(descriptor)
    updated = dict(index)
    updated["failed_pair_attempts"] = failed
    updated["active_pair_attempt"] = None
    return write_index(campaign_root, updated)


def recover_active_attempt(
    campaign_root: Path,
    benchmark_root: Path,
    index: dict[str, Any],
) -> dict[str, Any]:
    """Recover a path-stable attempt left active by cancellation or preemption."""

    active = mapping(index.get("active_pair_attempt"), "active pair attempt")
    validate_attempt_identity(active)
    pair_id = string(active.get("pair_id"), "active pair ID")
    job_id = string(active.get("slurm_job_id"), "active Slurm job ID")
    relative = safe_relative_path(active.get("path"), "active pair path")
    pair_root = campaign_root / relative
    if not pair_root.exists() and not pair_root.is_symlink():
        pair_root.mkdir(parents=True, exist_ok=False)
        fsync_directory(pair_root.parent)
    pair_root = resolve_below(campaign_root, relative.as_posix(), "active pair path")
    records = pair_root / "records"
    assignments = planned_pair_assignments(benchmark_root, pair_id)
    freeze_path = pair_root / "freeze_check.json"
    recovery_freeze: Mapping[str, Any] | None = None
    if freeze_path.exists() or freeze_path.is_symlink():
        recovery_freeze = mapping(
            read_json(freeze_path, "recoverable pair freeze"),
            "recoverable pair freeze",
        )
    validate_failed_runner_temporaries(
        pair_root,
        assignments,
        authenticated_incidents=authenticate_present_incidents(
            pair_root, assignments, recovery_freeze
        ),
    )
    record_paths = [] if not records.exists() else sorted(records.glob("*.json"))
    active_marker = pair_root / run_matrix.ACTIVE_RUN_MARKER
    commit_path = pair_root / "pair_commit.json"
    exit_marker_path = pair_root / MATRIX_EXIT_MARKER
    has_exit_marker = exit_marker_path.exists() or exit_marker_path.is_symlink()
    recovered_exit_code: int | None = None
    if has_exit_marker:
        raw_marker = mapping(
            read_json(exit_marker_path, "campaign matrix-exit marker"),
            "campaign matrix-exit marker",
        )
        recovered_exit_code = validate_matrix_exit_code(
            raw_marker.get("matrix_exit_code"),
            "recovered campaign matrix-exit code",
        )
        verify_matrix_exit_marker(
            pair_root, pair_id, job_id, recovered_exit_code
        )
    if len(record_paths) == 2 and has_exit_marker:
        if recovered_exit_code == 2:
            # The runner itself reported failure after sealing both finals.
            # Authenticate and archive the root without creating/clearing any
            # commit, status, or marker; neither final enters the measured set.
            return archive_failed_attempt(
                campaign_root,
                benchmark_root,
                index,
                pair_id,
                job_id,
                2,
                "matrix_error",
            )
        if recovered_exit_code != 0:
            raise CampaignError(
                "two-final interrupted pair has a non-success/non-matrix-error "
                "exit marker; manual audit is required"
            )
    if len(record_paths) == 2:
        freeze = mapping(
            read_json(pair_root / "freeze_check.json", "pair freeze"), "pair freeze"
        )
        verify_pair_freeze_against_metadata(benchmark_root, freeze, index)
        expected_record_names = {
            f"{assignment['run_id']}.json" for assignment in assignments
        }
        if {path.name for path in record_paths} != expected_record_names:
            raise CampaignError("recoverable complete pair has foreign final records")
        authenticated_finals = run_matrix._authenticate_existing_final_records(
            pair_root, records, assignments, freeze
        )
        if set(authenticated_finals) != {
            str(assignment["run_id"]) for assignment in assignments
        }:
            raise CampaignError("recoverable complete pair lacks exact final records")
        run_matrix._authenticate_existing_incidents(
            pair_root,
            pair_root / "incidents",
            assignments,
            freeze,
            authenticated_finals,
        )
        if active_marker.exists() or active_marker.is_symlink():
            run_matrix._clear_or_reject_interrupted_run(
                active_marker, records, pair_root, assignments, freeze
            )
        if active_marker.exists() or active_marker.is_symlink():
            raise CampaignError("recoverable complete pair retained its active marker")
        commit = run_matrix.create_or_verify_pair_commit(pair_root, assignments, freeze)
        expected_status = {
            "schema_version": 1,
            "kind": "highambench-matrix-chunk-status",
            "status": "stopped_after_requested_pair",
            "pair_id": pair_id,
            "completed_runs": 2,
            "planned_runs": 2,
            "pair_commit": run_matrix.pair_commit_descriptor(pair_root, commit),
        }
        status_path = pair_root / "last_chunk_status.json"
        if status_path.exists() or status_path.is_symlink():
            status = mapping(
                read_json(status_path, "recoverable pair status"),
                "recoverable pair status",
            )
            if dict(status) != expected_status:
                raise CampaignError("recoverable complete pair has a stale status")
        else:
            run_matrix._write_pair_complete_status(pair_root, pair_id, commit)
        if has_exit_marker:
            verify_matrix_exit_marker(pair_root, pair_id, job_id, 0)
        else:
            write_matrix_exit_marker(pair_root, pair_id, job_id, 0)
        return commit_attempt(campaign_root, benchmark_root, index, pair_id, job_id)
    if commit_path.exists() or commit_path.is_symlink() or len(record_paths) >= 2:
        raise CampaignError(
            "interrupted pair has a commit or two finals but cannot be authenticated as "
            "complete; manual audit is required"
        )
    if has_exit_marker:
        if recovered_exit_code == 0:
            raise CampaignError(
                "interrupted incomplete pair records a successful matrix exit; "
                "manual audit is required"
            )
        if recovered_exit_code == run_matrix.CHUNK_INCOMPLETE_EXIT_CODE:
            return archive_failed_attempt(
                campaign_root,
                benchmark_root,
                index,
                pair_id,
                job_id,
                recovered_exit_code,
                "allocation_deadline_before_pair",
            )
        if recovered_exit_code is not None:
            return archive_failed_attempt(
                campaign_root,
                benchmark_root,
                index,
                pair_id,
                job_id,
                recovered_exit_code,
                "matrix_error",
            )
    else:
        write_matrix_exit_marker(pair_root, pair_id, job_id, None)
    return archive_failed_attempt(
        campaign_root,
        benchmark_root,
        index,
        pair_id,
        job_id,
        None,
        "interrupted_job",
    )


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(description=__doc__)
    result.add_argument("--paper-id", choices=SUPPORTED_PAPER_IDS, required=True)
    result.add_argument("--target-pair-id", required=True)
    result.add_argument("--campaign-root", type=Path, required=True)
    result.add_argument("--benchmark-root", type=Path, required=True)
    subparsers = result.add_subparsers(dest="command", required=True)
    subparsers.add_parser("initialize")
    subparsers.add_parser("status")
    subparsers.add_parser("verify")
    subparsers.add_parser("recover-active")
    recover_staging = subparsers.add_parser("recover-staging")
    recover_staging.add_argument("--slurm-job-id", required=True)
    begin = subparsers.add_parser("begin")
    begin.add_argument("--pair-id", required=True)
    begin.add_argument("--slurm-job-id", required=True)
    begin.add_argument("--allocation-node", required=True)
    commit = subparsers.add_parser("commit")
    commit.add_argument("--pair-id", required=True)
    commit.add_argument("--slurm-job-id", required=True)
    record_exit = subparsers.add_parser("record-exit")
    record_exit.add_argument("--pair-id", required=True)
    record_exit.add_argument("--slurm-job-id", required=True)
    record_exit.add_argument("--matrix-exit-code", required=True, type=int)
    archive = subparsers.add_parser("archive-failed")
    archive.add_argument("--pair-id", required=True)
    archive.add_argument("--slurm-job-id", required=True)
    archive.add_argument("--matrix-exit-code", required=True, type=int)
    archive.add_argument(
        "--outcome",
        required=True,
        choices=("matrix_error", "allocation_deadline_before_pair"),
    )
    return result


def main(argv: Sequence[str] | None = None) -> int:
    args = parser().parse_args(argv)
    # Preserve the final path component for the explicit no-symlink check in
    # ``campaign_lock``; resolving it here would silently turn an alias into an
    # accepted permanent campaign path.
    campaign_root = args.campaign_root.absolute()
    benchmark_root = args.benchmark_root.resolve()
    try:
        configure_target(args.paper_id, args.target_pair_id)
        with campaign_lock(campaign_root):
            if args.command == "recover-staging":
                print(
                    json.dumps(
                        recover_launcher_staging(
                            campaign_root, args.slurm_job_id
                        ),
                        sort_keys=True,
                    )
                )
                return 0
            if args.command == "initialize":
                index = initialize(campaign_root, benchmark_root)
                print(json.dumps(status_payload(index), sort_keys=True))
                return 0
            index = load_and_verify_index(campaign_root, benchmark_root)
            if args.command in {"status", "verify"}:
                print(json.dumps(status_payload(index), sort_keys=True))
                return 0
            if args.command == "recover-active":
                index = recover_active_attempt(
                    campaign_root, benchmark_root, index
                )
                print(json.dumps(status_payload(index), sort_keys=True))
                return 0
            if args.command == "begin":
                index, root = begin_attempt(
                    campaign_root,
                    index,
                    args.pair_id,
                    args.slurm_job_id,
                    args.allocation_node,
                )
                print(root)
                return 0
            if args.command == "commit":
                index = commit_attempt(
                    campaign_root,
                    benchmark_root,
                    index,
                    args.pair_id,
                    args.slurm_job_id,
                )
                print(json.dumps(status_payload(index), sort_keys=True))
                return 0
            if args.command == "record-exit":
                active = mapping(index.get("active_pair_attempt"), "active pair attempt")
                if (
                    active.get("pair_id") != args.pair_id
                    or active.get("slurm_job_id") != args.slurm_job_id
                ):
                    raise CampaignError("active attempt does not match exit marker request")
                pair_root = resolve_below(
                    campaign_root, active.get("path"), "active pair path"
                )
                write_matrix_exit_marker(
                    pair_root,
                    args.pair_id,
                    args.slurm_job_id,
                    args.matrix_exit_code,
                )
                print(pair_root / MATRIX_EXIT_MARKER)
                return 0
            if args.command == "archive-failed":
                index = archive_failed_attempt(
                    campaign_root,
                    benchmark_root,
                    index,
                    args.pair_id,
                    args.slurm_job_id,
                    args.matrix_exit_code,
                    args.outcome,
                )
                print(json.dumps(status_payload(index), sort_keys=True))
                return 0
            raise CampaignError(f"unknown command {args.command!r}")
    except (CampaignError, run_matrix.BenchmarkToolError, OSError, ValueError) as error:
        print(f"pair-shard campaign error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
