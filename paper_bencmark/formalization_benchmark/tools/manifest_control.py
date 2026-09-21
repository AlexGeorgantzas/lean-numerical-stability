from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path
from typing import Any

from common import BenchmarkError, load_json, sha256_file


ROOT = Path(__file__).resolve().parents[1]
REPOSITORY_ROOT = ROOT.parents[1]
MANIFEST_PATH = ROOT / "manifest.json"
EXPECTED_BASE_COMMIT = "d6672677b57a04ba457cd0689fd878bf6abfc6ee"


def manifest_payload_sha256(value: dict[str, Any]) -> str:
    unsigned = dict(value)
    unsigned.pop("manifest_payload_sha256", None)
    payload = json.dumps(
        unsigned, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def verify_file_ref(record: Any, *, label: str) -> Path:
    if not isinstance(record, dict):
        raise BenchmarkError(f"manifest {label} is not an object")
    relative = record.get("relative_path")
    expected = record.get("sha256")
    if (
        not isinstance(relative, str)
        or not relative
        or Path(relative).is_absolute()
        or ".." in Path(relative).parts
        or not isinstance(expected, str)
        or re.fullmatch(r"[0-9a-f]{64}", expected) is None
    ):
        raise BenchmarkError(f"manifest {label} has an invalid file reference")
    path = (ROOT / relative).resolve()
    try:
        path.relative_to(ROOT.resolve())
    except ValueError as error:
        raise BenchmarkError(f"manifest {label} escapes the pilot root") from error
    if not path.is_file() or path.is_symlink():
        raise BenchmarkError(f"manifest {label} file is missing or unsafe: {path}")
    actual = sha256_file(path)
    if actual != expected:
        raise BenchmarkError(
            f"manifest {label} hash mismatch: expected {expected}, got {actual}"
        )
    return path


def verify_manifest() -> tuple[dict[str, Any], dict[str, Any]]:
    manifest = load_json(MANIFEST_PATH)
    if manifest.get("schema_version") != "formalization-benchmark-manifest-1":
        raise BenchmarkError("unsupported formalization manifest")
    if manifest.get("base_commit") != EXPECTED_BASE_COMMIT:
        raise BenchmarkError("formalization release is not bound to the frozen benchmark base")
    digest = manifest.get("manifest_payload_sha256")
    if not isinstance(digest, str) or manifest_payload_sha256(manifest) != digest:
        raise BenchmarkError("manifest payload self-hash mismatch")
    config_path = verify_file_ref(manifest.get("config"), label="config")
    config = load_json(config_path)
    pilot_id = config.get("pilot_id")
    if (
        not isinstance(pilot_id, str)
        or not pilot_id
        or pilot_id != manifest.get("pilot_id")
    ):
        raise BenchmarkError("manifest/config pilot identities disagree")
    task_ids = config.get("task_ids")
    if task_ids != manifest.get("task_ids") or manifest.get("task_count") != len(task_ids or []):
        raise BenchmarkError("manifest/config task sets disagree")
    if config.get("runs_per_task_per_condition") != 1:
        raise BenchmarkError("pilot requires exactly one run per task and condition")
    if config.get("submission_limit") != 4:
        raise BenchmarkError("pilot requires exactly four submissions")
    if config.get("contestant_active_time_limit_seconds") != 18_000:
        raise BenchmarkError("pilot requires a five-hour contestant-active limit")
    if config.get("token_cap") is not None:
        raise BenchmarkError("pilot must not have a benchmark token cap")
    if config.get("candidate") != {
        "file": "Candidate.lean",
        "root_declaration": "HighamBenchCandidate.target",
        "root_proof": "complete-kernel-checked-no-holes",
    }:
        raise BenchmarkError("pilot requires a complete kernel-checked target proof")
    if config.get("library_retrieval") != {
        "condition": "L",
        "atlas_schema_version": "numstability-library-atlas-2",
        "guide_workspace_file": "LIBRARY_GUIDE.md",
        "atlas_mount": "/library-index",
        "source_mount": "/library/NumStability",
        "reuse_first": True,
        "whole_source_scan_fallback_only": True,
        "record_uptake_telemetry": True,
    }:
        raise BenchmarkError("pilot library retrieval contract changed")
    if config.get("evaluation_gate") != {
        "primary_task_ids": ["H5-5", "H7-12", "H10-7", "H23-6"],
        "minimum_time_positive_pairs": 3,
        "minimum_median_time_reduction_fraction": 0.2,
        "minimum_median_net_new_token_reduction_fraction": 0.2,
        "require_both_conditions_faithful": True,
        "forbid_incident_pairs": True,
        "canary_task_id": "H00-00",
        "canary_excluded_from_scientific_results": True,
    }:
        raise BenchmarkError("pilot evaluation gate changed")
    hardware = config.get("hardware")
    if not isinstance(hardware, dict) or hardware.get("tasks_max") != 512:
        raise BenchmarkError("pilot requires the frozen 512-task cgroup ceiling")
    if config.get("workspace_limits") != {
        "maximum_entries": 10_000,
        "maximum_total_bytes": 1024 * 1024 * 1024,
        "maximum_written_file_bytes": 256 * 1024 * 1024,
    }:
        raise BenchmarkError("pilot workspace resource ceilings changed")
    if config.get("command_resource_envelope") != {
        "memory_bytes": 24 * 1024 * 1024 * 1024,
        "tasks_max": 384,
        "swap_enabled": False,
        "control_memory_low_bytes": 8 * 1024 * 1024 * 1024,
        "control_cpu_weight": 10_000,
        "command_cpu_weight": 100,
    }:
        raise BenchmarkError("pilot generated-command cgroup envelope changed")
    if config.get("artifact_limits") != {
        "maximum_protocol_line_bytes": 2 * 1024 * 1024,
        "maximum_event_trace_bytes": 16 * 1024 * 1024,
        "maximum_event_count": 50_000,
        "maximum_stderr_archive_bytes": 8 * 1024 * 1024,
    }:
        raise BenchmarkError("pilot artifact resource ceilings changed")
    for index, schema in enumerate(manifest.get("schemas", [])):
        verify_file_ref(schema, label=f"schema[{index}]")
    tasks = manifest.get("tasks")
    if not isinstance(tasks, list) or len(tasks) != 19:
        raise BenchmarkError("manifest must contain exactly nineteen task records")
    observed: list[str] = []
    for index, task in enumerate(tasks):
        if not isinstance(task, dict) or not isinstance(task.get("task_id"), str):
            raise BenchmarkError(f"manifest task[{index}] is malformed")
        task_id = task["task_id"]
        observed.append(task_id)
        packet_path = verify_file_ref(task.get("source_packet"), label=f"{task_id} packet")
        packet = load_json(packet_path)
        if packet.get("task_id") != task_id:
            raise BenchmarkError(f"source packet ID mismatch for {task_id}")
        paper = task.get("source_pdf")
        packet_paper = packet.get("paper_pdf")
        if not isinstance(paper, dict) or paper != packet_paper:
            raise BenchmarkError(f"paper identity mismatch inside {task_id} packet")
    if observed != manifest.get("task_ids"):
        raise BenchmarkError("manifest task records are not in frozen task order")
    release_files = manifest.get("release_files", [])
    if not isinstance(release_files, list) or not release_files:
        raise BenchmarkError("manifest has no complete release file closure")
    for index, record in enumerate(release_files):
        verify_file_ref(record, label=f"release_files[{index}]")
    recorded_release_paths = {record["relative_path"] for record in release_files}
    actual_release_paths = {
        path.relative_to(ROOT).as_posix()
        for path in ROOT.rglob("*")
        if path.is_file()
        and path != MANIFEST_PATH
        and "__pycache__" not in path.parts
        and path.suffix != ".pyc"
    }
    if recorded_release_paths != actual_release_paths:
        missing = sorted(actual_release_paths - recorded_release_paths)
        stale = sorted(recorded_release_paths - actual_release_paths)
        raise BenchmarkError(
            f"release closure mismatch; unrecorded={missing}, missing={stale}"
        )
    repository_files = manifest.get("repository_files")
    if not isinstance(repository_files, list) or not repository_files:
        raise BenchmarkError("manifest has no repository-level dependency closure")
    for index, record in enumerate(repository_files):
        if not isinstance(record, dict):
            raise BenchmarkError(f"repository_files[{index}] is malformed")
        relative = record.get("repository_relative_path")
        expected = record.get("sha256")
        if (
            not isinstance(relative, str)
            or not relative
            or Path(relative).is_absolute()
            or ".." in Path(relative).parts
            or not isinstance(expected, str)
            or re.fullmatch(r"[0-9a-f]{64}", expected) is None
        ):
            raise BenchmarkError(f"repository_files[{index}] has an invalid reference")
        path = (REPOSITORY_ROOT / relative).resolve()
        try:
            path.relative_to(REPOSITORY_ROOT.resolve())
        except ValueError as error:
            raise BenchmarkError("repository dependency escapes checkout") from error
        if not path.is_file() or path.is_symlink() or sha256_file(path) != expected:
            raise BenchmarkError(f"repository dependency hash mismatch: {relative}")
    return manifest, config


def task_record(manifest: dict[str, Any], task_id: str) -> dict[str, Any]:
    matches = [task for task in manifest["tasks"] if task.get("task_id") == task_id]
    if len(matches) != 1:
        raise BenchmarkError(f"task is not uniquely allowlisted: {task_id}")
    return matches[0]
