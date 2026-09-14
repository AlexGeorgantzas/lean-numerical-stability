from __future__ import annotations

import os
import shutil
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any

from common import BenchmarkError, load_json, sha256_file


DEFAULT_DEPLOYMENT = Path.home() / ".local" / "share" / "highambench-formalization" / "deployment.json"


@dataclass(frozen=True)
class Deployment:
    path: Path
    run_root: Path
    pdf_root: Path
    codex_binary: Path
    auth_file: Path
    bwrap_binary: Path
    offline_shell: Path
    toolchain_root: Path
    packages_root: Path
    library_source: Path
    library_olean: Path
    library_snapshot_record: Path
    runtime_snapshot_record: Path
    strict_hardware: bool


def deployment_path(explicit: Path | None = None) -> Path:
    if explicit is not None:
        return explicit.expanduser().resolve()
    raw = os.environ.get("HIGHAMBENCH_FORMALIZATION_DEPLOYMENT")
    return Path(raw).expanduser().resolve() if raw else DEFAULT_DEPLOYMENT


def _required_path(value: dict[str, Any], key: str, *, directory: bool = False) -> Path:
    raw = value.get(key)
    if not isinstance(raw, str) or not raw:
        raise BenchmarkError(f"deployment field {key} is missing")
    path = Path(raw).expanduser().resolve()
    exists = path.is_dir() if directory else path.is_file()
    if not exists:
        kind = "directory" if directory else "file"
        raise BenchmarkError(f"deployment {kind} is missing for {key}: {path}")
    if path.is_symlink():
        raise BenchmarkError(f"deployment path may not be a symlink: {path}")
    return path


def load_deployment(explicit: Path | None = None) -> Deployment:
    path = deployment_path(explicit)
    value = load_json(path)
    if value.get("schema_version") != "formalization-deployment-1":
        raise BenchmarkError("unsupported deployment record")
    run_root_raw = value.get("run_root")
    if not isinstance(run_root_raw, str) or not run_root_raw:
        raise BenchmarkError("deployment run_root is missing")
    run_root = Path(run_root_raw).expanduser().resolve()
    run_root.mkdir(parents=True, exist_ok=True, mode=0o700)
    if run_root.is_symlink():
        raise BenchmarkError("deployment run_root may not be a symlink")
    return Deployment(
        path=path,
        run_root=run_root,
        pdf_root=_required_path(value, "pdf_root", directory=True),
        codex_binary=_required_path(value, "codex_binary"),
        auth_file=_required_path(value, "auth_file"),
        bwrap_binary=_required_path(value, "bwrap_binary"),
        offline_shell=_required_path(value, "offline_shell"),
        toolchain_root=_required_path(value, "toolchain_root", directory=True),
        packages_root=_required_path(value, "packages_root", directory=True),
        library_source=_required_path(value, "library_source", directory=True),
        library_olean=_required_path(value, "library_olean", directory=True),
        library_snapshot_record=_required_path(value, "library_snapshot_record"),
        runtime_snapshot_record=_required_path(value, "runtime_snapshot_record"),
        strict_hardware=value.get("strict_hardware") is not False,
    )


def executable_identity(path: Path) -> dict[str, Any]:
    completed = subprocess.run(
        [str(path), "--version"],
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        timeout=20,
        check=False,
    )
    return {
        "path": str(path),
        "sha256": sha256_file(path),
        "version": completed.stdout.strip(),
        "version_exit_code": completed.returncode,
    }
