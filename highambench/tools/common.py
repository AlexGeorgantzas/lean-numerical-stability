"""Shared, dependency-free helpers for HighamBench tooling."""

from __future__ import annotations

import contextlib
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile
import time
from typing import Any, Iterable, Iterator, Mapping, Sequence


SCHEMA_VERSION = 1
FAILURE_CODES = (
    "TIME_LIMIT",
    "TOKEN_LIMIT",
    "NO_SUBMISSION",
    "RULE_VIOLATION",
    "SYNTAX_OR_ELAB",
    "PROOF_ERROR",
    "SYSTEM_ERROR",
)


class BenchmarkToolError(RuntimeError):
    """A deterministic benchmark configuration or validation error."""


def utc_now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def safe_relative_path(raw: str | Path) -> Path:
    path = Path(raw)
    if path.is_absolute() or not path.parts:
        raise BenchmarkToolError(f"path must be nonempty and relative: {raw}")
    if any(part in ("", ".", "..") for part in path.parts):
        raise BenchmarkToolError(f"path contains an unsafe component: {raw}")
    return path


def resolve_below(root: Path, relative: str | Path) -> Path:
    root = root.resolve()
    path = (root / safe_relative_path(relative)).resolve()
    try:
        path.relative_to(root)
    except ValueError as error:
        raise BenchmarkToolError(f"path escapes root {root}: {relative}") from error
    return path


def read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise BenchmarkToolError(f"cannot read JSON {path}: {error}") from error


def write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(value, indent=2, sort_keys=True) + "\n"
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}")
    temporary.write_text(payload, encoding="utf-8")
    os.replace(temporary, path)


def append_jsonl(path: Path, value: Mapping[str, Any]) -> None:
    """Append one complete JSON record while holding an advisory file lock."""

    path.parent.mkdir(parents=True, exist_ok=True)
    payload = json.dumps(value, sort_keys=True, separators=(",", ":")) + "\n"
    with path.open("a", encoding="utf-8") as stream:
        fcntl.flock(stream.fileno(), fcntl.LOCK_EX)
        try:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        finally:
            fcntl.flock(stream.fileno(), fcntl.LOCK_UN)


def parse_command_json(raw: str | None, *, option: str) -> list[str] | None:
    if raw is None:
        return None
    try:
        value = json.loads(raw)
    except json.JSONDecodeError as error:
        raise BenchmarkToolError(f"{option} must be a JSON array: {error}") from error
    if not isinstance(value, list) or not value or not all(
        isinstance(item, str) and item for item in value
    ):
        raise BenchmarkToolError(f"{option} must be a nonempty JSON array of strings")
    return value


class _StrictFormat(dict[str, str]):
    def __missing__(self, key: str) -> str:
        raise BenchmarkToolError(f"unknown command placeholder: {{{key}}}")


def render_command(command: Sequence[str], values: Mapping[str, str | Path | int]) -> list[str]:
    rendered_values = _StrictFormat({key: str(value) for key, value in values.items()})
    try:
        return [item.format_map(rendered_values) for item in command]
    except (ValueError, KeyError) as error:
        raise BenchmarkToolError(f"invalid command template: {error}") from error


def command_display(command: Sequence[str]) -> str:
    import shlex

    return shlex.join(command)


def terminate_process(process: subprocess.Popen[Any], grace_seconds: float = 2.0) -> None:
    if process.poll() is not None:
        return
    try:
        os.killpg(process.pid, signal.SIGTERM)
        process.wait(timeout=grace_seconds)
    except (ProcessLookupError, subprocess.TimeoutExpired):
        if process.poll() is None:
            with contextlib.suppress(ProcessLookupError):
                os.killpg(process.pid, signal.SIGKILL)
            with contextlib.suppress(subprocess.TimeoutExpired):
                process.wait(timeout=grace_seconds)


def run_captured(
    command: Sequence[str],
    *,
    cwd: Path,
    timeout_seconds: float,
    env: Mapping[str, str] | None = None,
) -> dict[str, Any]:
    started = time.perf_counter()
    try:
        completed = subprocess.run(
            list(command),
            cwd=cwd,
            env=None if env is None else dict(env),
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
            timeout=timeout_seconds,
        )
    except FileNotFoundError as error:
        return {
            "command": list(command),
            "seconds": round(time.perf_counter() - started, 6),
            "exit_code": None,
            "timed_out": False,
            "system_error": str(error),
            "output": "",
        }
    except subprocess.TimeoutExpired as error:
        output = error.stdout or ""
        if isinstance(output, bytes):
            output = output.decode("utf-8", errors="replace")
        return {
            "command": list(command),
            "seconds": round(time.perf_counter() - started, 6),
            "exit_code": None,
            "timed_out": True,
            "system_error": None,
            "output": output,
        }
    return {
        "command": list(command),
        "seconds": round(time.perf_counter() - started, 6),
        "exit_code": completed.returncode,
        "timed_out": False,
        "system_error": None,
        "output": completed.stdout,
    }


DEFAULT_COPY_EXCLUDES = {
    ".git",
    "__pycache__",
    ".DS_Store",
    "private_gold",
    "benchmark-results",
    "results",
}


def copytree_fresh(
    source: Path,
    destination: Path,
    *,
    excluded_names: Iterable[str] = DEFAULT_COPY_EXCLUDES,
) -> None:
    source = source.resolve()
    if not source.is_dir():
        raise BenchmarkToolError(f"workspace source is not a directory: {source}")
    if destination.exists():
        raise BenchmarkToolError(f"fresh workspace already exists: {destination}")
    excluded = set(excluded_names)

    def ignore(_directory: str, names: list[str]) -> set[str]:
        return {name for name in names if name in excluded}

    shutil.copytree(source, destination, symlinks=False, ignore=ignore)


@contextlib.contextmanager
def temporary_directory(parent: Path | None, prefix: str) -> Iterator[Path]:
    if parent is not None:
        parent.mkdir(parents=True, exist_ok=True)
    path = Path(tempfile.mkdtemp(prefix=prefix, dir=parent))
    try:
        yield path
    finally:
        shutil.rmtree(path, ignore_errors=True)


def truncate_text(value: str, limit: int = 200_000) -> tuple[str, bool]:
    if len(value) <= limit:
        return value, False
    return value[:limit] + "\n...[truncated by HighamBench]...\n", True
