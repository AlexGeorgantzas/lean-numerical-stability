#!/usr/bin/env python3
"""Measure the clean NumStability build used by the Titan deployment."""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
from typing import Any, Callable, Mapping

from common import (
    BenchmarkError,
    file_tree_fingerprint,
    sha256_bytes,
    sha256_file,
    stable_regular_bytes,
    utc_now,
    write_bytes_atomic,
    write_json_atomic,
)
from formalization_validator import run_bounded_command
from hardware import snapshot_hardware


SCHEMA_VERSION = "numstability-setup-build-1"
BUILD_TIMEOUT_SECONDS = 18_000.0
MAX_BUILD_OUTPUT_BYTES = 64 * 1024 * 1024
DEPENDENCY_CACHE_TIMEOUT_SECONDS = 1_800.0
MAX_DEPENDENCY_CACHE_OUTPUT_BYTES = 64 * 1024 * 1024
DEPENDENCY_MANIFEST_MAX_BYTES = 4 * 1024 * 1024
GIT_BINARY = "/usr/bin/git"
REQUIRED_CPU_STAT_KEYS = ("usage_usec", "user_usec", "system_usec")
REQUIRED_MEMORY_EVENT_KEYS = ("max", "oom", "oom_kill")
REQUIRED_PIDS_EVENT_KEYS = ("max",)


def _is_sha256(value: Any) -> bool:
    return isinstance(value, str) and re.fullmatch(r"[0-9a-f]{64}", value) is not None


def _line_count(payload: bytes) -> int:
    if not payload:
        return 0
    return payload.count(b"\n") + (0 if payload.endswith(b"\n") else 1)


def _parse_integer(value: str) -> int:
    return int(value)


def _parse_float(value: str) -> float:
    return float(value)


def _parse_percent(value: str) -> float:
    if not value.endswith("%"):
        raise ValueError("missing percent suffix")
    return float(value[:-1])


def _parse_kib_as_bytes(value: str) -> int:
    return int(value) * 1024


def parse_gnu_time_verbose(payload: str) -> dict[str, Any]:
    """Extract stable resource fields while retaining the complete raw record."""

    fields: tuple[tuple[str, str, Callable[[str], Any]], ...] = (
        ("User time (seconds):", "user_cpu_seconds", _parse_float),
        ("System time (seconds):", "system_cpu_seconds", _parse_float),
        ("Percent of CPU this job got:", "cpu_percent", _parse_percent),
        (
            "Elapsed (wall clock) time (h:mm:ss or m:ss):",
            "elapsed_wall_clock_text",
            str,
        ),
        (
            "Maximum resident set size (kbytes):",
            "maximum_resident_set_bytes",
            _parse_kib_as_bytes,
        ),
        ("Major (requiring I/O) page faults:", "major_page_faults", _parse_integer),
        ("Minor (reclaiming a frame) page faults:", "minor_page_faults", _parse_integer),
        ("Voluntary context switches:", "voluntary_context_switches", _parse_integer),
        (
            "Involuntary context switches:",
            "involuntary_context_switches",
            _parse_integer,
        ),
        ("Swaps:", "swaps", _parse_integer),
        ("File system inputs:", "filesystem_inputs", _parse_integer),
        ("File system outputs:", "filesystem_outputs", _parse_integer),
        ("Socket messages sent:", "socket_messages_sent", _parse_integer),
        ("Socket messages received:", "socket_messages_received", _parse_integer),
        ("Signals delivered:", "signals_delivered", _parse_integer),
        ("Exit status:", "exit_status", _parse_integer),
    )
    parsed: dict[str, Any] = {}
    for line in payload.splitlines():
        stripped = line.strip()
        for prefix, key, parser in fields:
            if stripped.startswith(prefix):
                raw = stripped[len(prefix) :].strip()
                try:
                    parsed[key] = parser(raw)
                except (TypeError, ValueError) as error:
                    raise BenchmarkError(f"malformed GNU time field: {prefix}") from error
                break
    required = {
        "user_cpu_seconds",
        "system_cpu_seconds",
        "elapsed_wall_clock_text",
        "maximum_resident_set_bytes",
        "exit_status",
    }
    missing = sorted(required - set(parsed))
    if missing:
        raise BenchmarkError("GNU time output is missing fields: " + ", ".join(missing))
    return parsed


def _small_command(
    command: list[str], *, cwd: Path, environment: Mapping[str, str] | None = None
) -> str:
    completed = subprocess.run(
        command,
        cwd=cwd,
        env=dict(environment) if environment is not None else None,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=60,
        check=False,
    )
    if completed.returncode != 0:
        raise BenchmarkError(
            f"build metadata command failed ({completed.returncode}): "
            f"{' '.join(command)}\n{completed.stdout[-4000:]}"
        )
    return completed.stdout.strip()


def _sanitized_build_environment(
    source: Mapping[str, str], *, toolchain_root: Path
) -> dict[str, str]:
    """Construct the complete environment visible to clean/build subprocesses."""

    result = {
        "PATH": os.pathsep.join(
            (
                str(toolchain_root / "bin"),
                "/usr/local/sbin",
                "/usr/local/bin",
                "/usr/sbin",
                "/usr/bin",
                "/sbin",
                "/bin",
            )
        ),
        # Do not expose user Git configuration, credentials, or mutable dotfiles.
        "HOME": "/nonexistent",
        "TMPDIR": source.get("TMPDIR", "/tmp"),
        "LANG": "C",
        "LC_ALL": "C",
        "TZ": "UTC",
        "CC": "/usr/bin/cc",
    }
    for key in ("XDG_CACHE_HOME", "ELAN_HOME"):
        value = source.get(key)
        if value:
            result[key] = value
    for key, value in result.items():
        if not value or len(value) > 4096 or "\x00" in value or "\n" in value:
            raise BenchmarkError(f"unsafe measured-build environment value: {key}")
    for key in ("HOME", "TMPDIR", "XDG_CACHE_HOME", "ELAN_HOME"):
        value = result.get(key)
        if value is not None and not Path(value).is_absolute():
            raise BenchmarkError(f"measured-build environment path is not absolute: {key}")
    return dict(sorted(result.items()))


def _key_value_file(path: Path, *, required_keys: tuple[str, ...]) -> dict[str, int]:
    try:
        lines = path.read_text(encoding="ascii").splitlines()
    except OSError as error:
        raise BenchmarkError(f"cannot read cgroup counter file: {path.name}") from error
    result: dict[str, int] = {}
    for line in lines:
        fields = line.split()
        if (
            len(fields) != 2
            or not fields[0]
            or not fields[1].isdigit()
            or fields[0] in result
        ):
            raise BenchmarkError(f"malformed cgroup counter file: {path.name}")
        result[fields[0]] = int(fields[1])
    missing = [key for key in required_keys if key not in result]
    if missing:
        raise BenchmarkError(
            f"cgroup counter file {path.name} is missing: {', '.join(missing)}"
        )
    return result


def _scalar_file(path: Path, *, required: bool = True) -> int | None:
    try:
        value = path.read_text(encoding="ascii").strip()
    except OSError as error:
        if not required and isinstance(error, FileNotFoundError):
            return None
        raise BenchmarkError(f"cannot read cgroup scalar file: {path.name}") from error
    if not value.isdigit():
        raise BenchmarkError(f"malformed cgroup scalar file: {path.name}")
    return int(value)


def cgroup_statistics(hardware: dict[str, Any]) -> dict[str, Any]:
    raw_root = hardware.get("cgroup_v2_path")
    if not isinstance(raw_root, str) or not raw_root:
        raise BenchmarkError("measured build has no cgroup-v2 path")
    root = Path(raw_root)
    return {
        "cpu_stat": _key_value_file(
            root / "cpu.stat", required_keys=REQUIRED_CPU_STAT_KEYS
        ),
        "memory_current_bytes": _scalar_file(root / "memory.current"),
        "memory_peak_bytes": _scalar_file(root / "memory.peak", required=False),
        "memory_events": _key_value_file(
            root / "memory.events", required_keys=REQUIRED_MEMORY_EVENT_KEYS
        ),
        "memory_swap_current_bytes": _scalar_file(root / "memory.swap.current"),
        "pids_current": _scalar_file(root / "pids.current"),
        "pids_events": _key_value_file(
            root / "pids.events", required_keys=REQUIRED_PIDS_EVENT_KEYS
        ),
    }


def _counter_delta(before: dict[str, int], after: dict[str, int]) -> dict[str, int]:
    if set(before) != set(after):
        raise BenchmarkError("cgroup counter keys changed during measured build")
    result: dict[str, int] = {}
    for key, prior in before.items():
        value = after[key]
        if value < prior:
            raise BenchmarkError("cgroup counters regressed during measured build")
        result[key] = value - prior
    return result


def _optional_file_tree_fingerprint(
    root: Path, *, suffix: str | None = None
) -> dict[str, Any]:
    if not os.path.lexists(root):
        return {
            "present": False,
            "file_count": 0,
            "bytes": 0,
            "tree_sha256": sha256_bytes(b"[]"),
        }
    if not root.is_dir() or root.is_symlink():
        raise BenchmarkError(f"build input/output tree is unsafe: {root.name}")
    return {"present": True, **file_tree_fingerprint(root, suffix=suffix)}


def _git_state(cwd: Path, *, environment: Mapping[str, str]) -> dict[str, Any]:
    head = _small_command(
        [GIT_BINARY, "rev-parse", "HEAD"], cwd=cwd, environment=environment
    )
    status = _small_command(
        [
            GIT_BINARY,
            "status",
            "--porcelain=v1",
            "--untracked-files=all",
            "--ignore-submodules=none",
        ],
        cwd=cwd,
        environment=environment,
    )
    if status:
        raise BenchmarkError(f"measured build Git tree is dirty: {cwd.name}")
    return {"head_commit": head, "clean": True}


def _source_input_fingerprint(checkout: Path) -> dict[str, Any]:
    source_root = checkout / "NumStability"
    root_module = checkout / "NumStability.lean"
    if (
        not source_root.is_dir()
        or source_root.is_symlink()
        or not root_module.is_file()
        or root_module.is_symlink()
    ):
        raise BenchmarkError("NumStability source input is missing or unsafe")
    source_tree = file_tree_fingerprint(source_root, suffix=".lean")
    root_record = {
        "bytes": root_module.stat().st_size,
        "sha256": sha256_file(root_module),
    }
    payload = json.dumps(
        {"source_tree": source_tree, "root_module": root_record},
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    return {
        "source_tree": source_tree,
        "root_module": root_record,
        "combined_sha256": sha256_bytes(payload),
    }


def _project_configuration_fingerprint(checkout: Path) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for name in ("lakefile.toml", "lake-manifest.json", "lean-toolchain"):
        payload = stable_regular_bytes(
            checkout / name, maximum_bytes=DEPENDENCY_MANIFEST_MAX_BYTES
        )
        item: dict[str, Any] = {
            "bytes": len(payload),
            "sha256": sha256_bytes(payload),
        }
        if name == "lean-toolchain":
            try:
                item["value"] = payload.decode("utf-8").strip()
            except UnicodeDecodeError as error:
                raise BenchmarkError("lean-toolchain is not UTF-8") from error
        result[name] = item
    return result


def _dependency_closure(
    checkout: Path, *, environment: Mapping[str, str]
) -> dict[str, Any]:
    manifest_path = checkout / "lake-manifest.json"
    manifest_bytes = stable_regular_bytes(
        manifest_path, maximum_bytes=DEPENDENCY_MANIFEST_MAX_BYTES
    )
    try:
        manifest = json.loads(manifest_bytes.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise BenchmarkError("lake-manifest.json is malformed") from error
    raw_packages = manifest.get("packages") if isinstance(manifest, dict) else None
    if not isinstance(raw_packages, list) or not raw_packages:
        raise BenchmarkError("lake-manifest.json has no dependency package closure")
    packages_root = checkout / ".lake" / "packages"
    records: list[dict[str, Any]] = []
    seen: set[str] = set()
    for raw in raw_packages:
        if not isinstance(raw, dict):
            raise BenchmarkError("lake-manifest.json contains a malformed package")
        name = raw.get("name")
        revision = raw.get("rev")
        if (
            not isinstance(name, str)
            or not re.fullmatch(r"[A-Za-z0-9_.-]+", name)
            or name in seen
            or not isinstance(revision, str)
            or not re.fullmatch(r"[0-9a-f]{40,64}", revision)
        ):
            raise BenchmarkError("lake-manifest.json contains an unsafe package identity")
        seen.add(name)
        package_root = packages_root / name
        if not package_root.is_dir() or package_root.is_symlink():
            raise BenchmarkError(f"dependency package is missing or unsafe: {name}")
        state = _git_state(package_root, environment=environment)
        if state["head_commit"] != revision:
            raise BenchmarkError(f"dependency package commit mismatch: {name}")
        olean = _optional_file_tree_fingerprint(
            package_root / ".lake" / "build" / "lib" / "lean", suffix=".olean"
        )
        records.append(
            {
                "name": name,
                "manifest_revision": revision,
                "head_commit": state["head_commit"],
                "git_clean": state["clean"],
                "olean": olean,
            }
        )
    records.sort(key=lambda record: record["name"])
    total_count = sum(int(record["olean"]["file_count"]) for record in records)
    total_bytes = sum(int(record["olean"]["bytes"]) for record in records)
    payload = json.dumps(records, sort_keys=True, separators=(",", ":")).encode(
        "utf-8"
    )
    return {
        "lake_manifest_sha256": sha256_bytes(manifest_bytes),
        "package_count": len(records),
        "dependency_olean_file_count": total_count,
        "dependency_olean_bytes": total_bytes,
        "closure_sha256": sha256_bytes(payload),
        "packages": records,
    }


def validate_build_record(
    record: Mapping[str, Any],
    *,
    expected_source_commit: str,
    expected_mathlib_commit: str,
    expected_toolchain: str,
    expected_tool_hashes: Mapping[str, str],
) -> None:
    """Fail closed on the provenance and resource claims in a build record."""

    if (
        record.get("schema_version") != SCHEMA_VERSION
        or record.get("benchmark_charged") is not False
        or record.get("source_commit") != expected_source_commit
        or record.get("mathlib_commit") != expected_mathlib_commit
        or record.get("lean_toolchain") != expected_toolchain
        or record.get("logical_command") != ["lake", "build", "NumStability"]
        or record.get("returncode") != 0
        or record.get("timed_out") is not False
        or record.get("output_limit_exceeded") is not False
        or record.get("resource_limit_exceeded") is not False
    ):
        raise BenchmarkError("NumStability build status or identity is not admissible")

    tool_versions = record.get("tool_versions")
    tool_hashes = record.get("tool_hashes")
    if (
        not isinstance(tool_versions, Mapping)
        or set(tool_versions) != {"lake", "lean", "gnu_time"}
        or any(not isinstance(value, str) or not value for value in tool_versions.values())
        or not isinstance(tool_hashes, Mapping)
        or dict(tool_hashes) != dict(expected_tool_hashes)
    ):
        raise BenchmarkError("NumStability build tool identity is not admissible")

    environment = record.get("build_environment")
    required_environment = {
        "CC": "/usr/bin/cc",
        "HOME": "/nonexistent",
        "LANG": "C",
        "LC_ALL": "C",
        "TZ": "UTC",
    }
    allowed_environment = set(required_environment) | {
        "PATH",
        "TMPDIR",
        "XDG_CACHE_HOME",
        "ELAN_HOME",
    }
    if (
        not isinstance(environment, Mapping)
        or set(environment) - allowed_environment
        or any(environment.get(key) != value for key, value in required_environment.items())
        or not isinstance(environment.get("PATH"), str)
        or not isinstance(environment.get("TMPDIR"), str)
    ):
        raise BenchmarkError("NumStability build environment is not controlled")

    cache = record.get("cache_state")
    if not isinstance(cache, Mapping):
        raise BenchmarkError("NumStability build cache provenance is missing")
    before = cache.get("dependency_closure_before")
    after = cache.get("dependency_closure_after")
    prebuild = cache.get("prebuild_project_tree")
    post_clean = cache.get("post_clean_project_tree")
    preparation = cache.get("dependency_cache_preparation")
    if (
        cache.get("dependency_cache_prepared_before_measurement") is not True
        or cache.get("project_cleaned_before_cache_preparation") is not True
        or cache.get("root_project_empty_immediately_before_measurement") is not True
        or cache.get("dependency_closure_unchanged") is not True
        or not isinstance(before, Mapping)
        or before != after
        or not isinstance(prebuild, Mapping)
        or prebuild.get("file_count") != 0
        or prebuild.get("bytes") != 0
        or not isinstance(post_clean, Mapping)
        or post_clean.get("file_count") != 0
        or post_clean.get("bytes") != 0
        or not isinstance(preparation, Mapping)
        or preparation.get("logical_command") != ["lake", "exe", "cache", "get"]
        or preparation.get("returncode") != 0
        or preparation.get("timed_out") is not False
        or preparation.get("output_limit_exceeded") is not False
        or preparation.get("resource_limit_exceeded") is not False
    ):
        raise BenchmarkError("NumStability build cache provenance is not admissible")
    packages = before.get("packages")
    if not isinstance(packages, list) or before.get("package_count") != len(packages):
        raise BenchmarkError("NumStability dependency closure is malformed")
    if any(
        not isinstance(package, Mapping)
        or package.get("git_clean") is not True
        or package.get("head_commit") != package.get("manifest_revision")
        or not isinstance(package.get("olean"), Mapping)
        or not isinstance(package["olean"].get("file_count"), int)
        or package["olean"].get("file_count", -1) < 0
        or not isinstance(package["olean"].get("bytes"), int)
        or package["olean"].get("bytes", -1) < 0
        or not _is_sha256(package["olean"].get("tree_sha256"))
        for package in packages
    ):
        raise BenchmarkError("NumStability dependency identity is malformed")
    closure_payload = json.dumps(
        packages, sort_keys=True, separators=(",", ":")
    ).encode("utf-8")
    if (
        not _is_sha256(before.get("lake_manifest_sha256"))
        or before.get("closure_sha256") != sha256_bytes(closure_payload)
        or before.get("dependency_olean_file_count")
        != sum(int(package["olean"].get("file_count", -1)) for package in packages)
        or before.get("dependency_olean_bytes")
        != sum(int(package["olean"].get("bytes", -1)) for package in packages)
        or before.get("dependency_olean_file_count", 0) <= 0
        or len(
            [package for package in packages if package.get("name") == "mathlib"]
        )
        != 1
        or next(
            package for package in packages if package.get("name") == "mathlib"
        ).get("head_commit")
        != expected_mathlib_commit
    ):
        raise BenchmarkError("NumStability dependency closure digest is invalid")

    source = record.get("source_inputs")
    project = record.get("project_configuration")
    if (
        not isinstance(source, Mapping)
        or source.get("unchanged") is not True
        or source.get("git_before") != source.get("git_after")
        or source.get("fingerprint_before") != source.get("fingerprint_after")
        or not isinstance(source.get("git_before"), Mapping)
        or source["git_before"].get("clean") is not True
        or source["git_before"].get("head_commit") != expected_source_commit
        or not isinstance(project, Mapping)
        or project.get("unchanged") is not True
        or project.get("before") != project.get("after")
    ):
        raise BenchmarkError("NumStability source provenance is not admissible")
    fingerprint = source["fingerprint_before"]
    if not isinstance(fingerprint, Mapping):
        raise BenchmarkError("NumStability source fingerprint is malformed")
    source_tree = fingerprint.get("source_tree")
    root_module = fingerprint.get("root_module")
    if not isinstance(source_tree, Mapping) or not isinstance(root_module, Mapping):
        raise BenchmarkError("NumStability source fingerprint is malformed")
    source_payload = json.dumps(
        {"source_tree": source_tree, "root_module": root_module},
        sort_keys=True,
        separators=(",", ":"),
    ).encode("utf-8")
    if (
        not _is_sha256(source_tree.get("tree_sha256"))
        or not _is_sha256(root_module.get("sha256"))
        or fingerprint.get("combined_sha256") != sha256_bytes(source_payload)
    ):
        raise BenchmarkError("NumStability source fingerprint digest is invalid")
    configuration = project["before"]
    if (
        not isinstance(configuration, Mapping)
        or set(configuration) != {"lakefile.toml", "lake-manifest.json", "lean-toolchain"}
        or not all(
            isinstance(item, Mapping)
            and isinstance(item.get("bytes"), int)
            and item.get("bytes", -1) >= 0
            and _is_sha256(item.get("sha256"))
            for item in configuration.values()
        )
        or before.get("lake_manifest_sha256")
        != configuration["lake-manifest.json"].get("sha256")
        or configuration["lean-toolchain"].get("value") != expected_toolchain
    ):
        raise BenchmarkError("NumStability project configuration provenance is malformed")

    generated_output = record.get("generated_output_tree")
    generated_olean = record.get("generated_olean")
    if (
        not isinstance(generated_output, Mapping)
        or generated_output.get("present") is not True
        or generated_output.get("file_count", 0) <= 0
        or not isinstance(generated_olean, Mapping)
        or generated_olean.get("present") is not True
        or generated_olean.get("file_count", 0) <= 0
    ):
        raise BenchmarkError("NumStability generated build inventory is empty")

    before_cgroup = record.get("cgroup_before")
    after_cgroup = record.get("cgroup_after")
    delta = record.get("cgroup_counter_delta")
    hardware_before = record.get("hardware_before")
    hardware_after = record.get("hardware_after")
    if (
        not isinstance(before_cgroup, Mapping)
        or not isinstance(after_cgroup, Mapping)
        or not isinstance(delta, Mapping)
        or not isinstance(hardware_before, Mapping)
        or not isinstance(hardware_after, Mapping)
        or hardware_before.get("admitted") is not True
        or hardware_after.get("admitted") is not True
        or hardware_before.get("cgroup_v2_path")
        != hardware_after.get("cgroup_v2_path")
        or before_cgroup.get("memory_swap_current_bytes") != 0
        or after_cgroup.get("memory_swap_current_bytes") != 0
    ):
        raise BenchmarkError("NumStability build cgroup evidence is not admissible")
    for snapshot in (before_cgroup, after_cgroup):
        for field in ("memory_current_bytes", "pids_current"):
            value = snapshot.get(field)
            if isinstance(value, bool) or not isinstance(value, int) or value < 0:
                raise BenchmarkError("NumStability build cgroup scalar is malformed")
        peak = snapshot.get("memory_peak_bytes")
        if peak is not None and (
            isinstance(peak, bool) or not isinstance(peak, int) or peak < 0
        ):
            raise BenchmarkError("NumStability build cgroup scalar is malformed")
    expected_delta: dict[str, dict[str, int]] = {}
    for field, required_keys in (
        ("cpu_stat", REQUIRED_CPU_STAT_KEYS),
        ("memory_events", REQUIRED_MEMORY_EVENT_KEYS),
        ("pids_events", REQUIRED_PIDS_EVENT_KEYS),
    ):
        raw_before = before_cgroup.get(field)
        raw_after = after_cgroup.get(field)
        if (
            not isinstance(raw_before, Mapping)
            or not isinstance(raw_after, Mapping)
            or any(
                key not in raw_before
                or key not in raw_after
                or isinstance(raw_before[key], bool)
                or not isinstance(raw_before[key], int)
                or isinstance(raw_after[key], bool)
                or not isinstance(raw_after[key], int)
                for key in required_keys
            )
            or any(
                isinstance(value, bool) or not isinstance(value, int) or value < 0
                for value in (*raw_before.values(), *raw_after.values())
            )
        ):
            raise BenchmarkError("NumStability build resource counters are malformed")
        expected_delta[field] = _counter_delta(
            dict(raw_before), dict(raw_after)
        )
    if dict(delta) != expected_delta:
        raise BenchmarkError("NumStability build resource counter delta is invalid")
    memory_delta = expected_delta["memory_events"]
    pids_delta = expected_delta["pids_events"]
    cpu_delta = expected_delta["cpu_stat"]
    if (
        not isinstance(memory_delta, Mapping)
        or not all(key in memory_delta for key in REQUIRED_MEMORY_EVENT_KEYS)
        or any(memory_delta[key] != 0 for key in REQUIRED_MEMORY_EVENT_KEYS)
        or not isinstance(pids_delta, Mapping)
        or not all(key in pids_delta for key in REQUIRED_PIDS_EVENT_KEYS)
        or any(pids_delta[key] != 0 for key in REQUIRED_PIDS_EVENT_KEYS)
        or not isinstance(cpu_delta, Mapping)
        or not all(key in cpu_delta for key in REQUIRED_CPU_STAT_KEYS)
    ):
        raise BenchmarkError("NumStability build resource counters are not admissible")


def _filesystem_snapshot(path: Path) -> dict[str, int]:
    value = os.statvfs(path)
    return {
        "block_size_bytes": value.f_frsize,
        "total_bytes": value.f_blocks * value.f_frsize,
        "free_bytes": value.f_bavail * value.f_frsize,
        "total_inodes": value.f_files,
        "free_inodes": value.f_favail,
    }


def measure_build(args: argparse.Namespace) -> Path:
    checkout = Path(args.checkout).resolve()
    artifact_root = Path(args.artifact_root).resolve()
    toolchain_root = Path(args.toolchain_root).resolve()
    if not checkout.is_dir() or checkout.is_symlink():
        raise BenchmarkError("NumStability build checkout is missing or unsafe")
    if artifact_root.exists() or artifact_root.is_symlink():
        raise BenchmarkError("NumStability build artifact directory already exists")
    artifact_root.mkdir(parents=True, mode=0o700)
    lake = toolchain_root / "bin" / "lake"
    lean = toolchain_root / "bin" / "lean"
    gnu_time = Path("/usr/bin/time")
    if not lake.is_file() or not lean.is_file() or not gnu_time.is_file():
        raise BenchmarkError("measured build toolchain is incomplete")
    if not Path(GIT_BINARY).is_file():
        raise BenchmarkError("measured build requires /usr/bin/git")
    environment = _sanitized_build_environment(
        os.environ, toolchain_root=toolchain_root
    )

    root_git_before = _git_state(checkout, environment=environment)
    actual_commit = root_git_before["head_commit"]
    if actual_commit != args.expected_commit:
        raise BenchmarkError("measured NumStability checkout commit mismatch")

    clean = run_bounded_command(
        [str(lake), "clean"],
        cwd=checkout,
        environment=environment,
        timeout_seconds=300,
        maximum_output_bytes=8 * 1024 * 1024,
    )
    if clean["returncode"] != 0 or clean["timed_out"] or clean["output_limit_exceeded"]:
        raise BenchmarkError("could not clean the NumStability project before measurement")
    post_clean_project_tree = _optional_file_tree_fingerprint(
        checkout / ".lake" / "build"
    )
    if post_clean_project_tree["file_count"] != 0:
        raise BenchmarkError("NumStability project build tree remained after lake clean")
    cache_command = [str(lake), "exe", "cache", "get"]
    cache_preparation = run_bounded_command(
        cache_command,
        cwd=checkout,
        environment=environment,
        timeout_seconds=DEPENDENCY_CACHE_TIMEOUT_SECONDS,
        maximum_output_bytes=MAX_DEPENDENCY_CACHE_OUTPUT_BYTES,
    )
    if (
        cache_preparation["returncode"] != 0
        or cache_preparation["timed_out"]
        or cache_preparation["output_limit_exceeded"]
        or cache_preparation["resource_limit_exceeded"]
    ):
        raise BenchmarkError("could not prepare dependency cache before measured build")
    prebuild_project_tree = _optional_file_tree_fingerprint(
        checkout / ".lake" / "build"
    )
    if prebuild_project_tree["file_count"] != 0:
        raise BenchmarkError("dependency cache preparation populated root build outputs")
    root_git_before = _git_state(checkout, environment=environment)
    source_inputs_before = _source_input_fingerprint(checkout)
    project_configuration_before = _project_configuration_fingerprint(checkout)
    if project_configuration_before["lean-toolchain"]["value"] != args.lean_toolchain:
        raise BenchmarkError("measured build lean-toolchain file mismatch")
    dependency_closure_before = _dependency_closure(
        checkout, environment=environment
    )
    if dependency_closure_before["dependency_olean_file_count"] <= 0:
        raise BenchmarkError("compiled dependency cache is empty before measured build")
    mathlib_records = [
        record
        for record in dependency_closure_before["packages"]
        if record["name"] == "mathlib"
    ]
    if (
        len(mathlib_records) != 1
        or mathlib_records[0]["head_commit"] != args.mathlib_commit
    ):
        raise BenchmarkError("measured build Mathlib commit mismatch")
    actual_mathlib_commit = mathlib_records[0]["head_commit"]

    output_path = artifact_root / "build-output.log"
    time_path = artifact_root / "gnu-time.txt"
    report_path = artifact_root / "build-record.json"

    tool_versions = {
        "lake": _small_command(
            [str(lake), "--version"], cwd=checkout, environment=environment
        ),
        "lean": _small_command(
            [str(lean), "--version"], cwd=checkout, environment=environment
        ),
        "gnu_time": _small_command(
            [str(gnu_time), "--version"], cwd=checkout, environment=environment
        ),
    }
    if "GNU Time" not in tool_versions["gnu_time"]:
        raise BenchmarkError("measured build requires GNU time")
    hardware_before = snapshot_hardware(strict=True)
    cgroup_before = cgroup_statistics(hardware_before)
    filesystem_before = _filesystem_snapshot(checkout)
    started_at_utc = utc_now()
    started_ns = time.perf_counter_ns()
    command = [
        str(gnu_time),
        "-v",
        "-o",
        str(time_path),
        str(lake),
        "build",
        "NumStability",
    ]
    completed = run_bounded_command(
        command,
        cwd=checkout,
        environment=environment,
        timeout_seconds=BUILD_TIMEOUT_SECONDS,
        maximum_output_bytes=MAX_BUILD_OUTPUT_BYTES,
    )
    finished_ns = time.perf_counter_ns()
    finished_at_utc = utc_now()
    hardware_after = snapshot_hardware(strict=True)
    if hardware_after.get("cgroup_v2_path") != hardware_before.get("cgroup_v2_path"):
        raise BenchmarkError("measured build cgroup identity changed")
    cgroup_after = cgroup_statistics(hardware_after)
    if (
        cgroup_before["memory_swap_current_bytes"] != 0
        or cgroup_after["memory_swap_current_bytes"] != 0
    ):
        raise BenchmarkError("measured build observed nonzero swap usage")
    filesystem_after = _filesystem_snapshot(checkout)

    root_git_after = _git_state(checkout, environment=environment)
    source_inputs_after = _source_input_fingerprint(checkout)
    project_configuration_after = _project_configuration_fingerprint(checkout)
    dependency_closure_after = _dependency_closure(
        checkout, environment=environment
    )
    if root_git_after != root_git_before:
        raise BenchmarkError("NumStability Git identity changed during measured build")
    if source_inputs_after != source_inputs_before:
        raise BenchmarkError("NumStability source inputs changed during measured build")
    if project_configuration_after != project_configuration_before:
        raise BenchmarkError("NumStability project configuration changed during measured build")
    if dependency_closure_after != dependency_closure_before:
        raise BenchmarkError("dependency cache closure changed during measured build")

    output = completed["output"].encode("utf-8")
    if sha256_bytes(output) != completed["output_sha256"]:
        raise BenchmarkError("NumStability build output was not round-trippable UTF-8")
    write_bytes_atomic(output_path, output, mode=0o400)
    time_payload = stable_regular_bytes(time_path, maximum_bytes=1024 * 1024)
    os.chmod(time_path, 0o400)
    parsed_time = parse_gnu_time_verbose(time_payload.decode("utf-8"))
    if parsed_time["exit_status"] != completed["returncode"]:
        raise BenchmarkError("GNU time and measured build exit statuses disagree")

    generated_root = checkout / ".lake" / "build" / "lib" / "lean"
    generated_output_tree = _optional_file_tree_fingerprint(generated_root)
    generated_olean = _optional_file_tree_fingerprint(
        generated_root, suffix=".olean"
    )
    cgroup_counter_delta = {
        "cpu_stat": _counter_delta(
            cgroup_before.get("cpu_stat", {}), cgroup_after.get("cpu_stat", {})
        ),
        "memory_events": _counter_delta(
            cgroup_before.get("memory_events", {}),
            cgroup_after.get("memory_events", {}),
        ),
        "pids_events": _counter_delta(
            cgroup_before.get("pids_events", {}), cgroup_after.get("pids_events", {})
        ),
    }
    cgroup_limit_exceeded = any(
        cgroup_counter_delta["memory_events"].get(key, 0) > 0
        for key in ("max", "oom", "oom_kill")
    ) or cgroup_counter_delta["pids_events"].get("max", 0) > 0
    resource_limit_exceeded = (
        completed["resource_limit_exceeded"] or cgroup_limit_exceeded
    )
    tool_hashes = {
        "lake_sha256": sha256_file(lake),
        "lean_sha256": sha256_file(lean),
        "gnu_time_sha256": sha256_file(gnu_time),
    }
    record = {
        "schema_version": SCHEMA_VERSION,
        "purpose": "one-time clean NumStability deployment build",
        "benchmark_charged": False,
        "cache_state": {
            "dependency_cache_prepared_before_measurement": True,
            "project_cleaned_before_cache_preparation": True,
            "root_project_empty_immediately_before_measurement": True,
            "post_clean_project_tree": post_clean_project_tree,
            "prebuild_project_tree": prebuild_project_tree,
            "dependency_cache_preparation": {
                "logical_command": ["lake", "exe", "cache", "get"],
                "returncode": cache_preparation["returncode"],
                "timed_out": cache_preparation["timed_out"],
                "timeout_seconds": DEPENDENCY_CACHE_TIMEOUT_SECONDS,
                "output_limit_exceeded": cache_preparation[
                    "output_limit_exceeded"
                ],
                "output_limit_bytes": MAX_DEPENDENCY_CACHE_OUTPUT_BYTES,
                "resource_limit_exceeded": cache_preparation[
                    "resource_limit_exceeded"
                ],
                "output_sha256": cache_preparation["output_sha256"],
                "output_bytes_observed": cache_preparation["output_bytes_observed"],
            },
            "dependency_closure_before": dependency_closure_before,
            "dependency_closure_after": dependency_closure_after,
            "dependency_closure_unchanged": True,
        },
        "source_commit": actual_commit,
        "mathlib_commit": actual_mathlib_commit,
        "lean_toolchain": args.lean_toolchain,
        "logical_command": ["lake", "build", "NumStability"],
        "build_environment": environment,
        "started_at_utc": started_at_utc,
        "finished_at_utc": finished_at_utc,
        "elapsed_monotonic_nanoseconds": finished_ns - started_ns,
        "elapsed_monotonic_seconds": (finished_ns - started_ns) / 1_000_000_000,
        "returncode": completed["returncode"],
        "timed_out": completed["timed_out"],
        "timeout_seconds": BUILD_TIMEOUT_SECONDS,
        "output_limit_exceeded": completed["output_limit_exceeded"],
        "output_limit_bytes": MAX_BUILD_OUTPUT_BYTES,
        "resource_limit_exceeded": resource_limit_exceeded,
        "tool_versions": tool_versions,
        "tool_hashes": tool_hashes,
        "source_inputs": {
            "git_before": root_git_before,
            "git_after": root_git_after,
            "fingerprint_before": source_inputs_before,
            "fingerprint_after": source_inputs_after,
            "unchanged": True,
        },
        "project_configuration": {
            "before": project_configuration_before,
            "after": project_configuration_after,
            "unchanged": True,
        },
        "hardware_before": hardware_before,
        "hardware_after": hardware_after,
        "cgroup_before": cgroup_before,
        "cgroup_after": cgroup_after,
        "cgroup_counter_delta": cgroup_counter_delta,
        "filesystem_before": filesystem_before,
        "filesystem_after": filesystem_after,
        "generated_output_tree": generated_output_tree,
        "generated_olean": generated_olean,
        "build_output": {
            "relative_path": output_path.name,
            "bytes": len(output),
            "line_count": _line_count(output),
            "sha256": sha256_file(output_path),
            "observed_bytes": completed["output_bytes_observed"],
        },
        "gnu_time": {
            "relative_path": time_path.name,
            "bytes": len(time_payload),
            "line_count": _line_count(time_payload),
            "sha256": sha256_file(time_path),
            "metrics": parsed_time,
        },
    }
    failed = (
        completed["returncode"] != 0
        or completed["timed_out"]
        or completed["output_limit_exceeded"]
        or resource_limit_exceeded
        or generated_olean["file_count"] == 0
    )
    if not failed:
        validate_build_record(
            record,
            expected_source_commit=args.expected_commit,
            expected_mathlib_commit=args.mathlib_commit,
            expected_toolchain=args.lean_toolchain,
            expected_tool_hashes=tool_hashes,
        )
    write_json_atomic(report_path, record, mode=0o400)
    if failed:
        tail = completed["output"][-8000:]
        raise BenchmarkError(f"measured NumStability build failed:\n{tail}")
    return report_path


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkout", required=True)
    parser.add_argument("--artifact-root", required=True)
    parser.add_argument("--toolchain-root", required=True)
    parser.add_argument("--expected-commit", required=True)
    parser.add_argument("--mathlib-commit", required=True)
    parser.add_argument("--lean-toolchain", required=True)
    return parser


if __name__ == "__main__":
    try:
        result = measure_build(make_parser().parse_args())
    except (BenchmarkError, OSError, subprocess.SubprocessError) as error:
        print(f"NumStability build measurement error: {error}", file=sys.stderr)
        raise SystemExit(2)
    print(json.dumps({"build_record": result.name}, sort_keys=True))
