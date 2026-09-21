from __future__ import annotations

import ctypes
import fcntl
import hashlib
import json
import os
import queue
import select
import signal
import shutil
import stat
import subprocess
import sys
import tempfile
import threading
import time
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping, TextIO

from common import (
    BenchmarkError,
    bounded_tree_usage,
    credential_needles,
    load_json,
    minimal_system_mount_args,
    redact_credentials,
    sha256_file,
    stable_regular_bytes,
    utc_now,
    write_bytes_atomic,
    write_json_atomic,
)


INITIALIZE_REQUEST_ID = 1
THREAD_REQUEST_ID = 2
TURN_REQUEST_ID = 3
PROTOCOL_ERROR_EXIT_CODE = 70
NETWORK_VIOLATION_EXIT_CODE = 77
TIMEOUT_EXIT_CODE = 124
POST_TERMINAL_TELEMETRY_TIMEOUT_SECONDS = 5.0
POST_TERMINAL_QUIET_SECONDS = 0.25
MAX_WORKSPACE_ENTRIES = 10_000
MAX_WORKSPACE_BYTES = 1024 * 1024 * 1024
MAX_PROTOCOL_LINE_CHARACTERS = 2 * 1024 * 1024
MAX_EVENT_TRACE_BYTES = 16 * 1024 * 1024
MAX_EVENT_TRACE_COUNT = 50_000
MAX_STDERR_ARCHIVE_BYTES = 8 * 1024 * 1024
COMMAND_CGROUP_VARIABLE = "HIGHAMBENCH_COMMAND_CGROUP_PROCS"
APP_SERVER_CLIENT_NAME = "highambench-formalization"
APP_SERVER_CLIENT_VERSION = "1"
SINGLE_AGENT_FEATURES = ("multi_agent", "multi_agent_v2")
COLLABORATION_TOOL_NAMES = {
    "spawnagent", "sendinput", "resumeagent", "waitagent", "closeagent",
            "sendmessage", "followuptask", "interruptagent", "listagents",
}
CONTROL_PROTECTED_TOP_LEVEL = {
    ".mcp.json",
    "agents.md",
    "config.toml",
    "hooks",
    "mcp",
    "mcp.json",
    "plugins",
    "rules",
    "skills",
}


class ProviderCapabilityError(BenchmarkError):
    """The provider-visible single-agent boundary could not be established."""


ProviderCapabilityViolation = ProviderCapabilityError


def _normalized_identifier(value: Any) -> str:
    return (
        "".join(character for character in value.casefold() if character.isalnum())
        if isinstance(value, str)
        else ""
    )


def _reject_collaboration_item(item: Any) -> None:
    if not isinstance(item, Mapping):
        return
    kind = _normalized_identifier(item.get("type"))
    if "collabagent" in kind or "subagent" in kind:
        raise ProviderCapabilityViolation("Codex emitted a collaboration item")
    if kind in ("functioncall", "customtoolcall"):
        namespace = _normalized_identifier(item.get("namespace"))
        name = item.get("name")
        if isinstance(name, str):
            parts = name.replace("::", ".").replace("/", ".").split(".")
            normalized_name = _normalized_identifier(parts[-1])
        else:
            normalized_name = ""
        if (
            normalized_name in COLLABORATION_TOOL_NAMES
            or ("collaboration" in namespace or "multiagent" in namespace)
        ):
            raise ProviderCapabilityViolation("Codex emitted a collaboration tool call")


def _linux_filesystem_type(path: Path) -> str | None:
    """Return the Linux mount type containing ``path`` without shelling out."""

    if not sys.platform.startswith("linux"):
        return None
    try:
        resolved = path.resolve(strict=True)
        lines = Path("/proc/self/mountinfo").read_text(encoding="utf-8").splitlines()
    except OSError:
        return None
    best: tuple[int, str] | None = None
    for line in lines:
        fields = line.split()
        try:
            separator = fields.index("-")
            mount_text = (
                fields[4]
                .replace(r"\040", " ")
                .replace(r"\011", "\t")
                .replace(r"\012", "\n")
                .replace(r"\134", "\\")
            )
            mount = Path(mount_text).resolve(strict=True)
            resolved.relative_to(mount)
            filesystem = fields[separator + 1]
        except (ValueError, IndexError, OSError):
            continue
        depth = len(mount.parts)
        if best is None or depth > best[0]:
            best = (depth, filesystem)
    return None if best is None else best[1]


def command_cgroup_snapshot(*, required: bool = False) -> dict[str, Any] | None:
    raw = os.environ.get(COMMAND_CGROUP_VARIABLE)
    if not raw:
        if required:
            raise BenchmarkError("generated-command cgroup is missing")
        return None
    procs = Path(raw)
    if not procs.is_file() or procs.is_symlink() or procs.name != "cgroup.procs":
        raise BenchmarkError("generated-command cgroup endpoint is unsafe")
    root = procs.parent

    def scalar(name: str) -> str:
        try:
            return (root / name).read_text(encoding="ascii").strip()
        except OSError as error:
            raise BenchmarkError(f"cannot read generated-command cgroup {name}") from error

    def counters(name: str) -> dict[str, int]:
        result: dict[str, int] = {}
        for line in scalar(name).splitlines():
            fields = line.split()
            if len(fields) != 2 or not fields[1].isdigit():
                raise BenchmarkError(f"malformed generated-command cgroup {name}")
            result[fields[0]] = int(fields[1])
        return result

    return {
        "path": str(root.resolve()),
        "memory_max": scalar("memory.max"),
        "memory_swap_max": scalar("memory.swap.max"),
        "pids_max": scalar("pids.max"),
        "cpu_weight": scalar("cpu.weight"),
        "memory_events": counters("memory.events"),
        "pids_events": counters("pids.events"),
    }


def command_cgroup_limit_delta(
    before: Mapping[str, Any] | None, after: Mapping[str, Any] | None
) -> dict[str, int]:
    if before is None or after is None:
        return {}
    if any(before.get(key) != after.get(key) for key in ("path", "memory_max", "memory_swap_max", "pids_max", "cpu_weight")):
        raise BenchmarkError("generated-command cgroup identity changed during a turn")
    result: dict[str, int] = {}
    for section, keys in (("memory_events", ("max", "oom", "oom_kill")), ("pids_events", ("max",))):
        old = before.get(section)
        new = after.get(section)
        if not isinstance(old, Mapping) or not isinstance(new, Mapping):
            raise BenchmarkError("generated-command cgroup event record is malformed")
        for key in keys:
            prior = old.get(key, 0)
            current = new.get(key, 0)
            if not isinstance(prior, int) or not isinstance(current, int) or current < prior:
                raise BenchmarkError("generated-command cgroup counters regressed")
            result[f"{section}.{key}"] = current - prior
    return result

_SENSITIVE_PROTOCOL_KEYS = {
    "accesstoken",
    "apikey",
    "auth",
    "authorization",
    "cookie",
    "cookies",
    "developerprompt",
    "encryptedcontent",
    "idtoken",
    "password",
    "reasoningcontent",
    "refreshtoken",
    "secret",
    "systemprompt",
}


def _sanitize_protocol_event(value: Any) -> tuple[Any, int]:
    """Remove restricted provider/auth payloads from the persisted JSONL trace."""

    redactions = 0

    def normalized(value: str) -> str:
        return "".join(character for character in value.casefold() if character.isalnum())

    def visit(item: Any, *, parent_type: str = "") -> Any:
        nonlocal redactions
        if isinstance(item, Mapping):
            item_type_value = item.get("type")
            item_type = (
                normalized(item_type_value)
                if isinstance(item_type_value, str)
                else parent_type
            )
            restricted_reasoning = "reasoning" in item_type
            restricted_instruction = item_type in {
                "developer",
                "developermessage",
                "system",
                "systemmessage",
            }
            rendered: dict[str, Any] = {}
            for key, child in item.items():
                key_text = str(key)
                key_normalized = normalized(key_text)
                if key_normalized in _SENSITIVE_PROTOCOL_KEYS:
                    redactions += 1
                    continue
                if (
                    (restricted_reasoning or restricted_instruction)
                    and key_normalized in {"content", "text"}
                ):
                    redactions += 1
                    continue
                rendered[key_text] = visit(
                    child,
                    parent_type="summary" if key_normalized == "summary" else item_type,
                )
            return rendered
        if isinstance(item, list):
            return [visit(child, parent_type=parent_type) for child in item]
        return item

    return visit(value), redactions


def _sanitized_protocol_line(message: Mapping[str, Any]) -> tuple[str, int]:
    value, redactions = _sanitize_protocol_event(message)
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n",
        redactions,
    )


class _BoundedEventArchive:
    """Stream a protocol trace to disk without retaining an unbounded list."""

    def __init__(self, path: Path) -> None:
        self.path = path
        self.temporary = path.parent / f".{path.name}.partial"
        flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        self._descriptor = os.open(self.temporary, flags, 0o600)
        self.count = 0
        self.bytes = 0
        self.violated = False

    def append(self, rendered: str) -> None:
        payload = rendered.encode("utf-8")
        if (
            self.count >= MAX_EVENT_TRACE_COUNT
            or self.bytes + len(payload) > MAX_EVENT_TRACE_BYTES
        ):
            self.violated = True
            raise BenchmarkError("Codex observable event archive ceiling exceeded")
        offset = 0
        while offset < len(payload):
            written = os.write(self._descriptor, payload[offset:])
            if written <= 0:
                raise BenchmarkError("short write to Codex event archive")
            offset += written
        self.count += 1
        self.bytes += len(payload)

    def seal(self) -> None:
        if self._descriptor < 0:
            return
        os.fsync(self._descriptor)
        os.close(self._descriptor)
        self._descriptor = -1
        os.replace(self.temporary, self.path)
        os.chmod(self.path, 0o400, follow_symlinks=False)
        directory = os.open(self.path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)

    def abort(self) -> None:
        if self._descriptor >= 0:
            os.close(self._descriptor)
            self._descriptor = -1
        self.temporary.unlink(missing_ok=True)


class _BoundedStderrCapture:
    """Drain all stderr while retaining only a fixed prefix and full digest."""

    def __init__(self) -> None:
        self._read_fd, self._write_fd = os.pipe()
        self._archive = tempfile.TemporaryFile(mode="w+b")
        self._lock = threading.Lock()
        self._digest = hashlib.sha256()
        self._total_bytes = 0
        self._archived_bytes = 0
        self._error: str | None = None
        self._parent_write_open = True
        self._thread = threading.Thread(target=self._drain, daemon=True)
        self._thread.start()

    def fileno(self) -> int:
        return self._write_fd

    def parent_after_spawn(self) -> None:
        if self._parent_write_open:
            os.close(self._write_fd)
            self._parent_write_open = False

    def _drain(self) -> None:
        try:
            while True:
                payload = os.read(self._read_fd, 64 * 1024)
                if not payload:
                    return
                with self._lock:
                    self._digest.update(payload)
                    self._total_bytes += len(payload)
                    retained = payload[: max(0, MAX_STDERR_ARCHIVE_BYTES - self._archived_bytes)]
                    if retained:
                        self._archive.write(retained)
                        self._archive.flush()
                        self._archived_bytes += len(retained)
        except OSError as error:  # pragma: no cover - OS pipe failure
            self._error = str(error)
        finally:
            try:
                os.close(self._read_fd)
            except OSError:
                pass

    def snapshot(self) -> bytes:
        with self._lock:
            if self._error is not None:
                raise OSError(self._error)
            return os.pread(self._archive.fileno(), self._archived_bytes, 0)

    def metadata(self) -> dict[str, Any]:
        with self._lock:
            return {
                "total_bytes": self._total_bytes,
                "archived_bytes": self._archived_bytes,
                "archive_limit_bytes": MAX_STDERR_ARCHIVE_BYTES,
                "truncated": self._total_bytes > self._archived_bytes,
                "full_stream_sha256": self._digest.hexdigest(),
            }

    def close(self) -> None:
        self.finish()
        self._archive.close()

    def finish(self) -> None:
        self.parent_after_spawn()
        self._thread.join(timeout=2)
        if self._thread.is_alive():
            try:
                os.close(self._read_fd)
            except OSError:
                pass
            self._thread.join(timeout=2)


@dataclass(frozen=True)
class TurnResult:
    thread_id: str | None
    exit_code: int
    timed_out: bool
    wall_seconds: float
    usage: dict[str, int]
    usage_complete: bool
    final_message: str
    event_count: int
    command: list[str]
    active_started_perf_ns: int | None
    active_ended_perf_ns: int | None
    failure_kind: str | None
    thread_cumulative_usage: dict[str, int] | None = None


def _zero_usage() -> dict[str, int]:
    return {
        "input_tokens": 0,
        "cached_input_tokens": 0,
        "cache_write_input_tokens": 0,
        "output_tokens": 0,
        "reasoning_output_tokens": 0,
        "total_tokens": 0,
    }


def _normalize_usage_breakdown(value: Any) -> dict[str, int] | None:
    if not isinstance(value, Mapping):
        return None
    aliases = {
        "input_tokens": ("inputTokens", "input_tokens"),
        "cached_input_tokens": ("cachedInputTokens", "cached_input_tokens"),
        "cache_write_input_tokens": (
            "cacheWriteInputTokens",
            "cache_write_input_tokens",
        ),
        "output_tokens": ("outputTokens", "output_tokens"),
        "reasoning_output_tokens": (
            "reasoningOutputTokens",
            "reasoning_output_tokens",
        ),
        "total_tokens": ("totalTokens", "total_tokens"),
    }
    normalized: dict[str, int] = {}
    for target, names in aliases.items():
        candidate: Any = None
        for name in names:
            if name in value:
                candidate = value[name]
                break
        if candidate is None and target == "cache_write_input_tokens":
            candidate = 0
        if not isinstance(candidate, int) or isinstance(candidate, bool) or candidate < 0:
            return None
        normalized[target] = candidate
    if (
        normalized["cached_input_tokens"]
        + normalized["cache_write_input_tokens"]
        > normalized["input_tokens"]
    ):
        return None
    if normalized["reasoning_output_tokens"] > normalized["output_tokens"]:
        return None
    if normalized["total_tokens"] != (
        normalized["input_tokens"] + normalized["output_tokens"]
    ):
        return None
    return normalized


def _normalize_raw_usage(value: Any) -> dict[str, int] | None:
    """Normalize exact usage from one rawResponse/completed notification."""

    if not isinstance(value, Mapping):
        return None
    required = {
        "input_tokens": "inputTokens",
        "cached_input_tokens": "cachedInputTokens",
        "output_tokens": "outputTokens",
        "reasoning_output_tokens": "reasoningOutputTokens",
        "total_tokens": "totalTokens",
    }
    normalized: dict[str, int] = {}
    for target, source in required.items():
        candidate = value.get(source)
        if not isinstance(candidate, int) or isinstance(candidate, bool) or candidate < 0:
            return None
        normalized[target] = candidate
    cache_write = value.get("cacheWriteInputTokens", 0)
    if not isinstance(cache_write, int) or isinstance(cache_write, bool) or cache_write < 0:
        return None
    normalized["cache_write_input_tokens"] = cache_write
    if (
        normalized["cached_input_tokens"]
        + normalized["cache_write_input_tokens"]
        > normalized["input_tokens"]
        or normalized["reasoning_output_tokens"] > normalized["output_tokens"]
        or normalized["total_tokens"]
        != normalized["input_tokens"] + normalized["output_tokens"]
    ):
        return None
    return normalized


def _usage_sum(values: list[Mapping[str, int]]) -> dict[str, int]:
    result = _zero_usage()
    for value in values:
        for field in result:
            result[field] += int(value[field])
    return result


def _usage_delta(
    cumulative: Mapping[str, int], baseline: Mapping[str, int]
) -> dict[str, int]:
    fields = tuple(_zero_usage())
    if any(cumulative[field] < baseline[field] for field in fields):
        raise BenchmarkError("Codex cumulative token usage moved backwards")
    result = {field: cumulative[field] - baseline[field] for field in fields}
    if (
        result["cached_input_tokens"] + result["cache_write_input_tokens"]
        > result["input_tokens"]
    ):
        raise BenchmarkError("Codex per-turn cache usage exceeds input usage")
    if result["reasoning_output_tokens"] > result["output_tokens"]:
        raise BenchmarkError("Codex per-turn reasoning usage exceeds output usage")
    if result["total_tokens"] != result["input_tokens"] + result["output_tokens"]:
        raise BenchmarkError("Codex per-turn token usage is inconsistent")
    return result


class _ProtocolEOF:
    pass


class _ProtocolReader:
    def __init__(self, stream: TextIO) -> None:
        # A small queue applies pipe backpressure if the app-server emits
        # events faster than the trusted consumer can validate/archive them.
        self._messages: queue.Queue[str | BaseException | _ProtocolEOF] = queue.Queue(
            maxsize=64
        )
        self._thread = threading.Thread(target=self._read, args=(stream,), daemon=True)
        self._thread.start()

    def _read(self, stream: TextIO) -> None:
        try:
            while True:
                line = stream.readline(MAX_PROTOCOL_LINE_CHARACTERS + 1)
                if not line:
                    break
                if len(line) > MAX_PROTOCOL_LINE_CHARACTERS:
                    self._messages.put(
                        BenchmarkError("Codex app-server protocol line ceiling exceeded")
                    )
                    return
                self._messages.put(line)
        except BaseException as error:  # pragma: no cover - OS stream failure
            self._messages.put(error)
        finally:
            self._messages.put(_ProtocolEOF())

    def get(self, timeout: float) -> str:
        try:
            item = self._messages.get(timeout=max(timeout, 0.001))
        except queue.Empty as error:
            raise TimeoutError("timed out waiting for Codex app-server") from error
        if isinstance(item, BaseException):
            raise BenchmarkError(f"Codex app-server output reader failed: {item}") from item
        if isinstance(item, _ProtocolEOF):
            raise BenchmarkError("Codex app-server ended before the turn was terminal")
        return item

    def drain_until_eof(self, timeout: float) -> dict[str, Any]:
        """Count/hash unread lines after process exit without retaining them."""

        deadline = time.monotonic() + timeout
        line_count = 0
        byte_count = 0
        digest = hashlib.sha256()
        while True:
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise BenchmarkError("Codex app-server stdout did not reach EOF")
            try:
                item = self._messages.get(timeout=max(remaining, 0.001))
            except queue.Empty as error:
                raise BenchmarkError("Codex app-server stdout did not reach EOF") from error
            if isinstance(item, BaseException):
                raise BenchmarkError(f"Codex app-server output reader failed: {item}") from item
            if isinstance(item, _ProtocolEOF):
                return {
                    "line_count": line_count,
                    "bytes": byte_count,
                    "sha256": digest.hexdigest(),
                }
            payload = item.encode("utf-8")
            line_count += 1
            byte_count += len(payload)
            digest.update(payload)


class _NetworkViolationMonitor:
    """Retain same-UID-resistant evidence that the offline shell touched its marker.

    Generated commands can edit the marker's final bytes because they run under
    the benchmark uid. A parent-owned inotify queue records inode mutations
    outside the sandbox. After the sandbox stops, the driver seals a nonempty
    marker whenever such an event was observed.
    """

    _IN_MODIFY = 0x00000002
    _IN_ATTRIB = 0x00000004
    _IN_DELETE_SELF = 0x00000400
    _IN_MOVE_SELF = 0x00000800
    _MAX_EVENTS = 4096
    # Do not watch IN_CLOSE_WRITE: the supervisor legitimately opens the
    # marker O_WRONLY for every shell invocation even when no denied syscall
    # occurs. IN_MODIFY is raised for the violation byte and for truncation.
    _MASK = _IN_MODIFY | _IN_ATTRIB | _IN_DELETE_SELF | _IN_MOVE_SELF

    def __init__(self, marker: Path) -> None:
        self.marker = marker
        self.event_count = 0
        self._fd: int | None = None
        self._stop = threading.Event()
        self._thread: threading.Thread | None = None
        self._drain_lock = threading.Lock()

    def start(self) -> None:
        if os.name != "posix" or not Path("/proc").is_dir():
            # Strict benchmark execution is Linux-only. Keep local unit tests
            # usable; no non-Linux result is accepted by the hardware doctor.
            return
        libc = ctypes.CDLL(None, use_errno=True)
        init = libc.inotify_init1
        init.argtypes = [ctypes.c_int]
        init.restype = ctypes.c_int
        fd = init(os.O_NONBLOCK | os.O_CLOEXEC)
        if fd < 0:
            error = ctypes.get_errno()
            raise BenchmarkError(f"could not initialize network-marker monitor: errno {error}")
        add_watch = libc.inotify_add_watch
        add_watch.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_uint32]
        add_watch.restype = ctypes.c_int
        watch = add_watch(fd, os.fsencode(self.marker), self._MASK)
        if watch < 0:
            error = ctypes.get_errno()
            os.close(fd)
            raise BenchmarkError(f"could not watch network-violation marker: errno {error}")
        self._fd = fd
        self._thread = threading.Thread(target=self._watch, daemon=True)
        self._thread.start()

    def _drain(self) -> None:
        with self._drain_lock:
            if self._fd is None:
                return
            while True:
                try:
                    payload = os.read(self._fd, 65536)
                except BlockingIOError:
                    return
                except OSError:
                    return
                if not payload:
                    return
                offset = 0
                while offset + 16 <= len(payload):
                    name_length = int.from_bytes(payload[offset + 12 : offset + 16], "little")
                    self.event_count = min(self.event_count + 1, self._MAX_EVENTS)
                    offset += 16 + name_length

    def checkpoint(self) -> int:
        """Drain queued events without ending a persistent app-server session."""

        self._drain()
        return self.event_count

    def _watch(self) -> None:
        assert self._fd is not None
        while not self._stop.is_set():
            try:
                readable, _, _ = select.select([self._fd], [], [], 0.05)
            except (OSError, ValueError):
                return
            if readable:
                self._drain()
        self._drain()

    def stop_and_seal(self) -> int:
        if self._fd is not None:
            self._stop.set()
            if self._thread is not None:
                self._thread.join(timeout=2)
            self._drain()
            os.close(self._fd)
            self._fd = None
        if self.event_count:
            # Generated code is dead before this trusted reconstruction occurs.
            write_bytes_atomic(self.marker, b"!" * self.event_count, mode=0o600)
        return self.event_count


@dataclass
class _LiveSession:
    process: subprocess.Popen[str]
    reader: _ProtocolReader
    stderr_capture: Any
    command: list[str]
    inner: list[str]
    workspace: Path
    thread_id: str
    cumulative_usage: dict[str, int]
    network_marker: Path
    network_monitor: _NetworkViolationMonitor | None
    network_checkpoint: int
    stderr_checkpoint: int
    auth_path: Path
    workspace_safe_to_scan: bool = True


class CodexDriver:
    """Drive one persisted Codex thread through the app-server JSONL protocol."""

    def __init__(
        self,
        *,
        codex_binary: Path,
        model: str,
        reasoning_effort: str,
        state_root: Path | None,
        auth_file: Path,
        disable_features: list[str] | None = None,
        bwrap_binary: Path | None = None,
        code_mode_host_sha256: str | None = None,
        offline_shell: Path | None = None,
        toolchain_root: Path | None = None,
        packages_root: Path | None = None,
        library_source: Path | None = None,
        library_olean: Path | None = None,
        library_atlas: Path | None = None,
        workspace_writable: bool = True,
        protected_workspace_paths: list[Path] | None = None,
        fork_source_thread_id: str | None = None,
        fork_source_last_turn_id: str | None = None,
        fork_source_cumulative_usage: Mapping[str, int] | None = None,
    ) -> None:
        self.codex_binary = codex_binary
        self.model = model
        self.reasoning_effort = reasoning_effort
        self._owned_control_root: Path | None = None
        self._private_runtime_is_tmpfs = False
        if state_root is None:
            runtime_parent: Path | None = None
            configured_runtime = os.environ.get("XDG_RUNTIME_DIR")
            if configured_runtime:
                candidate = Path(configured_runtime)
                try:
                    status = candidate.stat(follow_symlinks=False)
                except OSError:
                    status = None
                if (
                    status is not None
                    and stat.S_ISDIR(status.st_mode)
                    and not candidate.is_symlink()
                    and status.st_uid == os.getuid()
                    and status.st_mode & 0o077 == 0
                    and _linux_filesystem_type(candidate) == "tmpfs"
                ):
                    runtime_parent = candidate
            shared_memory = Path("/dev/shm")
            if (
                runtime_parent is None
                and shared_memory.is_dir()
                and _linux_filesystem_type(shared_memory) == "tmpfs"
            ):
                runtime_parent = shared_memory
            if runtime_parent is None and sys.platform.startswith("linux") and bwrap_binary:
                raise BenchmarkError(
                    "a private tmpfs runtime is required for refreshable Codex credentials"
                )
            owned = Path(
                tempfile.mkdtemp(
                    prefix=f"highambench-control-{os.getpid()}-",
                    dir=str(runtime_parent) if runtime_parent is not None else None,
                )
            )
            os.chmod(owned, 0o700)
            self._owned_control_root = owned
            self._private_runtime_is_tmpfs = (
                _linux_filesystem_type(owned) == "tmpfs"
            )
            state_root = owned / "state"
        self.state_root = state_root
        self.auth_file = auth_file
        self._credential_needles = credential_needles(auth_file)
        self.disable_features = disable_features or [
            "apps",
            "browser_use",
            "computer_use",
            "external_agent_memory_import",
            "goals",
            "image_generation",
            "in_app_browser",
            "memories",
            "multi_agent",
            "multi_agent_v2",
            "plugins",
            "remote_plugin",
            "skill_search",
            "standalone_web_search",
        ]
        self.disable_features = list(dict.fromkeys([*self.disable_features, *SINGLE_AGENT_FEATURES]))
        self.bwrap_binary = bwrap_binary
        self.code_mode_host_sha256 = code_mode_host_sha256
        self.code_mode_host: Path | None = None
        self.offline_shell = offline_shell
        self.toolchain_root = toolchain_root
        self.packages_root = packages_root
        self.library_source = library_source
        self.library_olean = library_olean
        self.library_atlas = library_atlas
        self.workspace_writable = workspace_writable
        self.protected_workspace_paths = protected_workspace_paths or []
        self.fork_source_thread_id = fork_source_thread_id
        self.fork_source_last_turn_id = fork_source_last_turn_id
        self.fork_source_cumulative_usage = (
            _normalize_usage_breakdown(fork_source_cumulative_usage)
            if fork_source_cumulative_usage is not None
            else None
        )
        fork_fields = (
            self.fork_source_thread_id,
            self.fork_source_last_turn_id,
            self.fork_source_cumulative_usage,
        )
        if any(value is not None for value in fork_fields) and not all(
            value is not None for value in fork_fields
        ):
            raise BenchmarkError("a Codex fork requires source thread, turn, and usage")
        for label, value in (
            ("source thread", self.fork_source_thread_id),
            ("source turn", self.fork_source_last_turn_id),
        ):
            if value is not None and (not isinstance(value, str) or not value):
                raise BenchmarkError(f"Codex fork {label} is malformed")
        if (bwrap_binary is None) != (offline_shell is None):
            raise BenchmarkError("bwrap and offline shell must be configured together")
        if bwrap_binary is not None and (toolchain_root is None or packages_root is None):
            raise BenchmarkError("external sandbox requires frozen Lean and package roots")
        self._identity_root = self.state_root.parent / f".{self.state_root.name}-identity"
        self._usage_record = self.state_root.parent / f".{self.state_root.name}-usage.json"
        self._control_baseline = (
            self.state_root.parent / f".{self.state_root.name}-control-baseline.json"
        )
        self._session_marker = (
            self.state_root.parent / f".{self.state_root.name}-network-violations.bin"
        )
        self._live_session: _LiveSession | None = None
        self._next_turn_request_id = TURN_REQUEST_ID
        try:
            if bwrap_binary is not None:
                self.code_mode_host = self._authenticated_code_mode_host()
            self._prepare_state()
            self._prepare_identity_files()
        except BaseException:
            if self._owned_control_root is not None:
                shutil.rmtree(self._owned_control_root, ignore_errors=True)
                self._owned_control_root = None
            raise

    def _redact_artifact_bytes(self, payload: bytes) -> tuple[bytes, int]:
        return redact_credentials(payload, self._credential_needles)

    def _assert_private_auth_file(self) -> Path:
        path = self.state_root / "auth.json"
        try:
            metadata = path.lstat()
        except OSError as error:
            raise BenchmarkError("private Codex authentication is unavailable") from error
        if (
            stat.S_ISLNK(metadata.st_mode)
            or not stat.S_ISREG(metadata.st_mode)
            or metadata.st_uid != os.getuid()
            or metadata.st_mode & 0o077
            or metadata.st_size > 4 * 1024 * 1024
        ):
            raise BenchmarkError("private Codex authentication file is unsafe")
        if path.parent.resolve() != self.state_root.resolve():
            raise BenchmarkError("private Codex authentication escaped its state root")
        return path

    def _auth_storage_lock(self) -> tuple[int, Path]:
        lock_path = self.auth_file.parent / f".{self.auth_file.name}.highambench.lock"
        flags = os.O_RDWR | os.O_CREAT | os.O_CLOEXEC
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        descriptor = os.open(lock_path, flags, 0o600)
        os.fchmod(descriptor, 0o600)
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        return descriptor, lock_path

    @staticmethod
    def _release_auth_storage_lock(descriptor: int) -> None:
        try:
            fcntl.flock(descriptor, fcntl.LOCK_UN)
        finally:
            os.close(descriptor)

    def _sync_private_auth_to_storage(self) -> None:
        """Persist refresh-token rotation to the benchmark-private auth store."""

        private = self._assert_private_auth_file()
        payload = stable_regular_bytes(private, maximum_bytes=4 * 1024 * 1024)
        if not payload or len(payload) > 4 * 1024 * 1024:
            raise BenchmarkError("private Codex authentication payload is unsafe")
        descriptor, _lock_path = self._auth_storage_lock()
        try:
            write_bytes_atomic(self.auth_file, payload, mode=0o600)
            self._credential_needles.update(credential_needles(self.auth_file))
        finally:
            self._release_auth_storage_lock(descriptor)

    def _refresh_private_auth_from_storage(self) -> None:
        """Give an idle persistent app-server the newest rotated credential."""

        self._assert_private_auth_file()
        descriptor, _lock_path = self._auth_storage_lock()
        try:
            if not self.auth_file.is_file() or self.auth_file.is_symlink():
                raise BenchmarkError("benchmark-private Codex auth store is unsafe")
            payload = stable_regular_bytes(
                self.auth_file, maximum_bytes=4 * 1024 * 1024
            )
            if not payload or len(payload) > 4 * 1024 * 1024:
                raise BenchmarkError("benchmark-private Codex auth payload is unsafe")
            write_bytes_atomic(self.state_root / "auth.json", payload, mode=0o600)
            self._credential_needles.update(credential_needles(self.auth_file))
        finally:
            self._release_auth_storage_lock(descriptor)

    def _control_security_manifest(self) -> dict[str, Any]:
        entries: list[dict[str, Any]] = []
        for path in sorted(
            self.state_root.rglob("*"),
            key=lambda item: item.relative_to(self.state_root).as_posix(),
        ):
            relative = path.relative_to(self.state_root)
            if relative.parts[0].casefold() not in CONTROL_PROTECTED_TOP_LEVEL:
                continue
            if path.is_symlink():
                raise BenchmarkError(f"symlink in Codex control state: {relative}")
            try:
                mode = path.stat(follow_symlinks=False).st_mode
            except OSError as error:
                raise BenchmarkError(f"unreadable Codex control state: {relative}") from error
            if not (stat.S_ISREG(mode) or stat.S_ISDIR(mode)):
                raise BenchmarkError(f"special file in Codex control state: {relative}")
            if stat.S_ISDIR(mode):
                entries.append(
                    {"relative_path": relative.as_posix(), "kind": "directory", "mode": mode}
                )
            else:
                entries.append(
                    {
                        "relative_path": relative.as_posix(),
                        "kind": "file",
                        "mode": mode,
                        "bytes": path.stat().st_size,
                        "sha256": sha256_file(path),
                    }
                )
        return {"schema_version": 1, "entries": entries}

    def seal_control_baseline(self) -> None:
        """Seal normal Codex-generated configuration before any model turn."""

        if (self.state_root / "auth.json").exists() or (self.state_root / "auth.json").is_symlink():
            self._assert_private_auth_file()
        current = self._control_security_manifest()
        if self._control_baseline.exists() or self._control_baseline.is_symlink():
            if self._control_baseline.is_symlink() or not self._control_baseline.is_file():
                raise BenchmarkError("unsafe Codex control baseline")
            if load_json(self._control_baseline) != current:
                raise BenchmarkError("Codex security-sensitive control state changed")
            return
        write_json_atomic(self._control_baseline, current, mode=0o400)

    def assert_safe_control_surfaces(
        self, workspace: Path, *, scan_workspace: bool = True
    ) -> None:
        """Verify the sealed control baseline and reject workspace control files."""

        if not self.state_root.is_dir() or self.state_root.is_symlink():
            raise BenchmarkError("unsafe Codex control root")
        if (self.state_root / "auth.json").exists() or (self.state_root / "auth.json").is_symlink():
            self._assert_private_auth_file()
        if not self._control_baseline.is_file() or self._control_baseline.is_symlink():
            raise BenchmarkError("Codex control state has no trusted baseline")
        if load_json(self._control_baseline) != self._control_security_manifest():
            raise BenchmarkError("Codex security-sensitive control state changed")
        if scan_workspace:
            self._assert_safe_workspace(workspace)

    @staticmethod
    def _assert_safe_workspace(workspace: Path) -> None:
        if not workspace.is_dir() or workspace.is_symlink():
            raise BenchmarkError("unsafe Codex workspace root")
        for path in workspace.rglob("*"):
            relative = path.relative_to(workspace)
            lowered = {part.casefold() for part in relative.parts}
            if path.is_symlink():
                raise BenchmarkError(f"symlink in contestant workspace: {relative}")
            mode = path.stat(follow_symlinks=False).st_mode
            if not (stat.S_ISREG(mode) or stat.S_ISDIR(mode)):
                raise BenchmarkError(f"special file in contestant workspace: {relative}")
            if ".codex" in lowered or relative.name.casefold() in CONTROL_PROTECTED_TOP_LEVEL:
                raise BenchmarkError(f"forbidden workspace control surface: {relative}")

    def _prepare_state(self) -> None:
        if not self.auth_file.is_file() or self.auth_file.is_symlink():
            raise BenchmarkError(f"Codex auth file is missing or unsafe: {self.auth_file}")
        if self.state_root.exists():
            if not self.state_root.is_dir() or self.state_root.is_symlink():
                raise BenchmarkError(f"unsafe existing Codex state root: {self.state_root}")
        else:
            self.state_root.mkdir(parents=True, exist_ok=False)
            os.chmod(self.state_root, 0o700)
        if not self._control_baseline.exists() and any(self.state_root.iterdir()):
            raise BenchmarkError("refusing an existing unsealed Codex state")
        if self._control_baseline.exists() and (
            self._control_baseline.is_symlink() or not self._control_baseline.is_file()
        ):
            raise BenchmarkError("unsafe Codex control baseline")
        staged_auth = self.state_root / "auth.json"
        if staged_auth.exists() or staged_auth.is_symlink():
            raise BenchmarkError("Codex state contains a stale authentication file")

    def _prepare_identity_files(self) -> None:
        expected = {
            "passwd": (
                f"bench:x:{os.getuid()}:{os.getgid()}:Benchmark User:/home/bench:/offline-bash\n"
            ).encode("utf-8"),
            "group": f"bench:x:{os.getgid()}:\n".encode("utf-8"),
        }
        if self._identity_root.exists():
            if not self._identity_root.is_dir() or self._identity_root.is_symlink():
                raise BenchmarkError("unsafe sandbox identity directory")
        else:
            self._identity_root.mkdir(mode=0o700)
        for name, payload in expected.items():
            path = self._identity_root / name
            if path.exists() or path.is_symlink():
                if path.is_symlink() or not path.is_file() or path.read_bytes() != payload:
                    raise BenchmarkError(f"unsafe existing sandbox identity file: {path}")
            else:
                write_bytes_atomic(path, payload, mode=0o400)
            os.chmod(path, 0o400)

    def _stage_auth(self) -> Path:
        destination = self.state_root / "auth.json"
        flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
        if hasattr(os, "O_NOFOLLOW"):
            flags |= os.O_NOFOLLOW
        lock_descriptor, _lock_path = self._auth_storage_lock()
        try:
            try:
                descriptor = os.open(destination, flags, 0o600)
            except FileExistsError as error:
                raise BenchmarkError(
                    "refusing to replace a stale Codex authentication file"
                ) from error
            try:
                try:
                    payload = stable_regular_bytes(
                        self.auth_file, maximum_bytes=4 * 1024 * 1024
                    )
                    offset = 0
                    while offset < len(payload):
                        offset += os.write(descriptor, payload[offset:])
                    os.fsync(descriptor)
                finally:
                    os.close(descriptor)
            except BaseException:
                destination.unlink(missing_ok=True)
                raise
        finally:
            self._release_auth_storage_lock(lock_descriptor)
        os.chmod(destination, 0o600)
        return destination

    @staticmethod
    def _remove_auth(path: Path) -> None:
        path.unlink(missing_ok=True)
        if path.exists() or path.is_symlink():
            raise BenchmarkError("could not remove temporary Codex authentication")

    def _app_server_command(self, command_codex: str) -> list[str]:
        command = [
            command_codex,
            "app-server",
            "--stdio",
            "--strict-config",
            "--config",
            f'model="{self.model}"',
            "--config",
            f'model_reasoning_effort="{self.reasoning_effort}"',
            "--config",
            'approval_policy="never"',
            "--config",
            'sandbox_mode="workspace-write"',
            "--config",
            "mcp_servers={}",
            "--config",
            "notify=[]",
            "--config",
            "project_doc_max_bytes=0",
            "--config",
            "project_doc_fallback_filenames=[]",
            "--config",
            'web_search="disabled"',
            "--config",
            "memories.use_memories=false",
            "--config",
            "memories.generate_memories=false",
            "--config",
            "agents.enabled=false",
        ]
        for feature in self.disable_features:
            command.extend(["--disable", feature])
        return command

    @property
    def externally_sandboxed(self) -> bool:
        return self.bwrap_binary is not None

    def _authenticated_code_mode_host(self) -> Path:
        """Authenticate the helper packaged beside the real Codex executable."""

        expected = self.code_mode_host_sha256
        if (
            not isinstance(expected, str)
            or len(expected) != 64
            or any(character not in "0123456789abcdef" for character in expected)
        ):
            raise BenchmarkError("external sandbox requires a pinned code-mode host SHA-256")
        try:
            codex = self.codex_binary.resolve(strict=True)
            codex_metadata = codex.stat(follow_symlinks=False)
        except OSError as error:
            raise BenchmarkError("Codex executable is missing or unsafe") from error
        if not stat.S_ISREG(codex_metadata.st_mode):
            raise BenchmarkError("Codex executable is not a regular file")
        # Resolve the installed Codex target first so a PATH symlink cannot
        # select a helper from a different package/version directory.
        host = codex.with_name("codex-code-mode-host")
        try:
            before = host.lstat()
            flags = os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW
            descriptor = os.open(host, flags)
        except OSError as error:
            raise BenchmarkError(f"code-mode host is missing or unsafe: {host}") from error
        try:
            opened = os.fstat(descriptor)
            if (
                not stat.S_ISREG(before.st_mode)
                or not stat.S_ISREG(opened.st_mode)
                or before.st_dev != opened.st_dev
                or before.st_ino != opened.st_ino
                or not opened.st_mode & 0o111
            ):
                raise BenchmarkError(f"code-mode host is not a safe executable: {host}")
            digest = hashlib.sha256()
            for chunk in iter(lambda: os.read(descriptor, 1024 * 1024), b""):
                digest.update(chunk)
            after_open = os.fstat(descriptor)
        except OSError as error:
            raise BenchmarkError(f"could not authenticate code-mode host: {host}") from error
        finally:
            os.close(descriptor)
        try:
            after_path = host.lstat()
        except OSError as error:
            raise BenchmarkError(f"code-mode host changed during authentication: {host}") from error
        identity_fields = ("st_dev", "st_ino", "st_mode", "st_size", "st_mtime_ns", "st_ctime_ns")
        if any(
            getattr(before, field) != getattr(opened, field)
            or getattr(opened, field) != getattr(after_open, field)
            or getattr(after_open, field) != getattr(after_path, field)
            for field in identity_fields
        ):
            raise BenchmarkError(f"code-mode host changed during authentication: {host}")
        if not os.access(host, os.X_OK):
            raise BenchmarkError(f"code-mode host is not executable by this account: {host}")
        if digest.hexdigest() != expected:
            raise BenchmarkError(f"code-mode host SHA-256 does not match deployment: {host}")
        return host

    def _bwrap_command(
        self,
        inner: list[str],
        *,
        workspace: Path,
        artifact_dir: Path,
        output_schema: Path | None,
        network_marker: Path | None = None,
    ) -> list[str]:
        del output_schema  # The parsed schema travels in the turn/start RPC.
        assert self.bwrap_binary is not None
        assert self.offline_shell is not None
        assert self.toolchain_root is not None
        assert self.packages_root is not None
        host = self._authenticated_code_mode_host()
        if host != self.code_mode_host:
            raise BenchmarkError("code-mode host path changed after preflight")
        command = [
            str(self.bwrap_binary.resolve()),
            "--unshare-all",
            "--share-net",
            "--die-with-parent",
            "--new-session",
            "--clearenv",
        ]
        command.extend(minimal_system_mount_args())
        # Codex resolves the command shell with getpwuid(3), not $SHELL. These
        # later file mounts override the host records and force the offline shell.
        command.extend(
            [
                "--ro-bind",
                str((self._identity_root / "passwd").resolve()),
                "/etc/passwd",
                "--ro-bind",
                str((self._identity_root / "group").resolve()),
                "/etc/group",
                "--proc",
                "/proc",
                "--dev",
                "/dev",
                "--tmpfs",
                "/tmp",
                "--dir",
                "/home",
                "--dir",
                "/home/bench",
                "--dir",
                "/control",
                "--bind",
                str(self.state_root.resolve()),
                "/control/codex",
                "--bind" if self.workspace_writable else "--ro-bind",
                str(workspace.resolve()),
                "/workspace",
                "--ro-bind",
                str(self.codex_binary.resolve()),
                "/codex",
                "--ro-bind",
                str(host),
                "/codex-code-mode-host",
                "--ro-bind",
                str(self.offline_shell.resolve()),
                "/offline-bash",
                "--ro-bind",
                str(self.toolchain_root.resolve()),
                "/lean",
                "--ro-bind",
                str(self.packages_root.resolve()),
                "/packages",
            ]
        )
        if self._control_baseline.is_file():
            for path in sorted(self.state_root.iterdir(), key=lambda item: item.name):
                if path.name.casefold() in CONTROL_PROTECTED_TOP_LEVEL:
                    if path.is_symlink() or not (path.is_file() or path.is_dir()):
                        raise BenchmarkError(f"unsafe protected Codex control path: {path}")
                    command.extend(
                        ["--ro-bind", str(path.resolve()), f"/control/codex/{path.name}"]
                    )
        if self.workspace_writable:
            for protected in self.protected_workspace_paths:
                resolved = protected.resolve()
                try:
                    relative = resolved.relative_to(workspace.resolve())
                except ValueError as error:
                    raise BenchmarkError(f"protected path escapes workspace: {protected}") from error
                if not resolved.exists() or resolved.is_symlink():
                    raise BenchmarkError(f"protected workspace path is unsafe: {protected}")
                command.extend(["--ro-bind", str(resolved), "/workspace/" + relative.as_posix()])
        marker = network_marker or (artifact_dir / "network_violations.bin")
        if marker.exists() or marker.is_symlink():
            if marker.is_symlink() or not marker.is_file():
                raise BenchmarkError(f"unsafe network-violation marker: {marker}")
        else:
            write_bytes_atomic(marker, b"", mode=0o600)
        os.chmod(marker, 0o600)
        command.extend(
            [
                "--dir",
                "/run",
                "--dir",
                "/run/highambench",
                "--bind",
                str(marker.resolve()),
                "/run/highambench/network-violations",
            ]
        )
        command_cgroup = os.environ.get(COMMAND_CGROUP_VARIABLE)
        if command_cgroup:
            command_cgroup_path = Path(command_cgroup)
            if (
                not command_cgroup_path.is_file()
                or command_cgroup_path.is_symlink()
                or command_cgroup_path.name != "cgroup.procs"
            ):
                raise BenchmarkError("generated-command cgroup endpoint is unsafe")
            command.extend(
                [
                    "--bind",
                    str(command_cgroup_path.resolve()),
                    "/run/highambench/command-cgroup.procs",
                ]
            )
        lean_paths: list[str] = []
        if (
            self.library_source is not None
            or self.library_olean is not None
            or self.library_atlas is not None
        ):
            if (
                self.library_source is None
                or self.library_olean is None
                or self.library_atlas is None
            ):
                raise BenchmarkError("library source, olean, and atlas roots must be paired")
            command.extend(
                [
                    "--dir",
                    "/library",
                    "--ro-bind",
                    str(self.library_source.resolve()),
                    "/library/NumStability",
                    "--ro-bind",
                    str(self.library_olean.resolve()),
                    "/library-olean",
                    "--ro-bind",
                    str(self.library_atlas.resolve()),
                    "/library-index",
                ]
            )
            root_file = self.library_source.parent / "NumStability.lean"
            if root_file.is_file():
                command.extend(["--ro-bind", str(root_file.resolve()), "/library/NumStability.lean"])
            lean_paths.append("/library-olean")
        mathlib_olean = self.packages_root / "mathlib" / ".lake" / "build" / "lib" / "lean"
        if not mathlib_olean.is_dir():
            raise BenchmarkError(f"Mathlib olean root is missing: {mathlib_olean}")
        lean_paths.append("/packages/mathlib/.lake/build/lib/lean")
        for package in sorted(self.packages_root.iterdir(), key=lambda path: path.name):
            compiled = package / ".lake" / "build" / "lib" / "lean"
            if package.name != "mathlib" and compiled.is_dir():
                lean_paths.append(f"/packages/{package.name}/.lake/build/lib/lean")
        lean_paths.extend(["/lean/lib/lean", "/workspace"])
        command.extend(
            [
                "--setenv",
                "HOME",
                "/home/bench",
                "--setenv",
                "CODEX_HOME",
                "/control/codex",
                "--setenv",
                "USER",
                "bench",
                "--setenv",
                "LOGNAME",
                "bench",
                "--setenv",
                "LANG",
                "C.UTF-8",
                "--setenv",
                "TZ",
                "UTC",
                "--setenv",
                "PATH",
                "/lean/bin:/usr/bin",
                "--setenv",
                "LEAN_PATH",
                ":".join(lean_paths),
                "--setenv",
                "SHELL",
                "/offline-bash",
                "--setenv",
                "HIGHAMBENCH_NETWORK_VIOLATION_MARKER",
                "/run/highambench/network-violations",
                "--setenv",
                "HIGHAMBENCH_COMMAND_CGROUP_PROCS",
                (
                    "/run/highambench/command-cgroup.procs"
                    if command_cgroup
                    else ""
                ),
                "--setenv",
                "NO_COLOR",
                "1",
                "--chdir",
                "/workspace",
                *inner,
            ]
        )
        return command

    def _load_usage_baseline(self, thread_id: str | None) -> dict[str, int]:
        if thread_id is None:
            if self._usage_record.exists() or self._usage_record.is_symlink():
                raise BenchmarkError("new Codex thread has a stale usage baseline")
            return _zero_usage()
        if not self._usage_record.is_file() or self._usage_record.is_symlink():
            raise BenchmarkError("resumed Codex thread lacks a trusted usage baseline")
        try:
            record = json.loads(self._usage_record.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            raise BenchmarkError("Codex usage baseline is unreadable") from error
        if not isinstance(record, Mapping) or record.get("thread_id") != thread_id:
            raise BenchmarkError("Codex usage baseline belongs to another thread")
        usage = _normalize_usage_breakdown(record.get("cumulative"))
        if usage is None:
            raise BenchmarkError("Codex usage baseline is malformed")
        return usage

    def _store_usage_baseline(self, thread_id: str, cumulative: Mapping[str, int]) -> None:
        write_json_atomic(
            self._usage_record,
            {"schema_version": 1, "thread_id": thread_id, "cumulative": dict(cumulative)},
            mode=0o400,
        )

    @staticmethod
    def _write_rpc(stream: TextIO, message: Mapping[str, Any]) -> None:
        wire = json.dumps(message, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        stream.write(wire + "\n")
        stream.flush()

    @staticmethod
    def _response_result(message: Mapping[str, Any], request_id: int, method: str) -> Any:
        if message.get("id") != request_id or "method" in message:
            raise BenchmarkError(f"Codex app-server returned an unexpected response to {method}")
        if "error" in message:
            raise BenchmarkError(f"Codex app-server rejected {method}: {message['error']!r}")
        if "result" not in message:
            raise BenchmarkError(f"Codex app-server omitted the {method} result")
        return message["result"]

    @staticmethod
    def _thread_from_result(
        result: Any, *, expected: str | None, expected_ephemeral: bool
    ) -> tuple[str, Mapping[str, Any]]:
        if not isinstance(result, Mapping) or not isinstance(result.get("thread"), Mapping):
            raise BenchmarkError("Codex app-server returned a malformed thread result")
        thread = result["thread"]
        candidate = thread.get("id")
        if not isinstance(candidate, str) or not candidate:
            raise BenchmarkError("Codex app-server returned no thread id")
        if expected is not None and candidate != expected:
            raise BenchmarkError("Codex app-server resumed a different thread")
        if thread.get("ephemeral") is not expected_ephemeral:
            raise BenchmarkError("Codex app-server returned the wrong thread persistence mode")
        return candidate, thread

    @staticmethod
    def _turn_from_result(result: Any) -> str:
        if not isinstance(result, Mapping) or not isinstance(result.get("turn"), Mapping):
            raise BenchmarkError("Codex app-server returned a malformed turn result")
        candidate = result["turn"].get("id")
        if not isinstance(candidate, str) or not candidate:
            raise BenchmarkError("Codex app-server returned no turn id")
        return candidate

    @staticmethod
    def _thread_config() -> dict[str, Any]:
        return {
            "agents": {"enabled": False},
            "features": {"multi_agent": False, "multi_agent_v2": False},
        }

    @staticmethod
    def _attest_config_read(result: Any) -> dict[str, Any]:
        if not isinstance(result, Mapping):
            raise ProviderCapabilityViolation("Codex config/read returned no configuration")
        config = result.get("config")
        origins = result.get("origins")
        layers = result.get("layers")
        if not isinstance(config, Mapping) or not isinstance(origins, Mapping) or not isinstance(layers, list):
            raise ProviderCapabilityViolation("Codex config/read omitted layered configuration")
        agents = config.get("agents")
        features = config.get("features")
        if (
            not isinstance(agents, Mapping)
            or agents.get("enabled") is not False
            or not isinstance(features, Mapping)
            or any(features.get(name) is not False for name in SINGLE_AGENT_FEATURES)
        ):
            raise ProviderCapabilityViolation("Codex single-agent configuration is not disabled")
        expected_keys = ("agents.enabled", "features.multi_agent", "features.multi_agent_v2")
        for key in expected_keys:
            origin = origins.get(key)
            # The v2 feature is represented as a nested .enabled origin by
            # app-server 0.154, while its effective config is a plain bool.
            if origin is None and key == "features.multi_agent_v2":
                origin = origins.get(f"{key}.enabled")
            name = origin.get("name") if isinstance(origin, Mapping) else None
            if not isinstance(name, Mapping) or name.get("type") != "sessionFlags":
                raise ProviderCapabilityViolation(
                    f"Codex single-agent config origin is not session flags: {key}"
                )
        session_layers = [
            layer.get("config") for layer in layers
            if isinstance(layer, Mapping)
            and isinstance(layer.get("name"), Mapping)
            and layer["name"].get("type") == "sessionFlags"
        ]
        if len(session_layers) != 1 or not isinstance(session_layers[0], Mapping):
            raise ProviderCapabilityViolation("Codex session-flags layer is ambiguous")
        session_config = session_layers[0]
        session_agents = session_config.get("agents")
        session_features = session_config.get("features")
        if (
            not isinstance(session_agents, Mapping)
            or session_agents.get("enabled") is not False
            or not isinstance(session_features, Mapping)
            or any(session_features.get(name) is not False for name in SINGLE_AGENT_FEATURES)
        ):
            raise ProviderCapabilityViolation("Codex session flags omitted the single-agent gates")
        return {
            "effective_config": CodexDriver._thread_config(),
            "session_flag_origins": list(expected_keys),
            "session_flags_layer": CodexDriver._thread_config(),
        }

    @staticmethod
    def _attest_feature_list(
        request: Callable[[str, dict[str, Any]], Any], *, thread_id: str | None
    ) -> dict[str, Any]:
        features: dict[str, dict[str, Any]] = {}
        cursor: str | None = None
        seen_cursors: set[str] = set()
        for _ in range(16):
            params: dict[str, Any] = {"limit": 1000}
            if thread_id is not None:
                params["threadId"] = thread_id
            if cursor is not None:
                params["cursor"] = cursor
            result = request("experimentalFeature/list", params)
            if not isinstance(result, Mapping) or not isinstance(result.get("data"), list):
                raise ProviderCapabilityViolation("Codex feature list is malformed")
            for entry in result["data"]:
                if not isinstance(entry, Mapping):
                    raise ProviderCapabilityViolation("Codex feature list contains a malformed item")
                name = entry.get("name")
                if name in SINGLE_AGENT_FEATURES:
                    if (
                        name in features
                        or entry.get("enabled") is not False
                        or not isinstance(entry.get("defaultEnabled"), bool)
                        or not isinstance(entry.get("stage"), str)
                    ):
                        raise ProviderCapabilityViolation(
                            f"Codex collaboration feature is enabled or duplicated: {name}"
                        )
                    features[name] = {
                        "enabled": False,
                        "default_enabled": entry.get("defaultEnabled"),
                        "stage": entry.get("stage"),
                    }
            next_cursor = result.get("nextCursor")
            if next_cursor is None:
                break
            if not isinstance(next_cursor, str) or not next_cursor or next_cursor in seen_cursors:
                raise ProviderCapabilityViolation("Codex feature pagination is malformed")
            seen_cursors.add(next_cursor)
            cursor = next_cursor
        else:
            raise ProviderCapabilityViolation("Codex feature list exceeded the pagination limit")
        if set(features) != set(SINGLE_AGENT_FEATURES):
            raise ProviderCapabilityViolation("Codex collaboration feature attestations are missing")
        return {"request_thread_id": thread_id, "features": features}

    def preflight(
        self,
        *,
        workspace: Path,
        artifact_dir: Path,
        timeout_seconds: float = 60,
    ) -> dict[str, Any]:
        """Provider-free app-server compatibility and credential-boundary canary.

        This exercises the exact benchmark command through initialize and either
        an ephemeral ``thread/start`` or the configured warm ``thread/fork``,
        then removes auth and shuts down. It deliberately never sends
        ``turn/start``, so it cannot launch a model inference.
        """

        if not workspace.is_dir() or workspace.is_symlink():
            raise BenchmarkError(f"unsafe Codex preflight workspace: {workspace}")
        if self._control_baseline.is_file():
            self.assert_safe_control_surfaces(workspace)
        else:
            if any(self.state_root.iterdir()):
                raise BenchmarkError("Codex preflight state is nonempty and unsealed")
            self._assert_safe_workspace(workspace)
        if timeout_seconds <= 0:
            raise BenchmarkError("Codex preflight timeout must be positive")
        artifact_dir.mkdir(parents=True, exist_ok=False)
        command_codex = "/codex" if self.externally_sandboxed else str(self.codex_binary)
        inner = self._app_server_command(command_codex)
        command = (
            self._bwrap_command(
                inner,
                workspace=workspace,
                artifact_dir=artifact_dir,
                output_schema=None,
            )
            if self.externally_sandboxed
            else inner
        )
        environment = (
            {"PATH": "/usr/bin"}
            if self.externally_sandboxed
            else {
                "CODEX_HOME": str(self.state_root),
                "HOME": str(self.state_root.parent),
                "LANG": "C.UTF-8",
                "LC_ALL": "C.UTF-8",
                "LOGNAME": "bench",
                "NO_COLOR": "1",
                "PATH": "/lean/bin:/usr/bin",
                "SHELL": str(self.offline_shell) if self.offline_shell else "/bin/sh",
                "TZ": "UTC",
                "USER": "bench",
            }
        )
        marker = artifact_dir / "network_violations.bin"
        monitor: _NetworkViolationMonitor | None = None
        if self.externally_sandboxed:
            monitor = _NetworkViolationMonitor(marker)
            monitor.start()
        # App-server bootstrap is an off-clock admission step. Bound it
        # independently so a wedged local startup cannot consume contestant
        # time or wait for the full five-hour remaining allowance.
        deadline = time.monotonic() + min(timeout_seconds, 60.0)
        event_archive = _BoundedEventArchive(artifact_dir / "events.jsonl")
        protocol_redactions = 0
        staged_auth: Path | None = None
        process: subprocess.Popen[str] | None = None
        observed_thread_id: str | None = None
        auth_removed = False
        background_terminal_methods_canary = False
        failure: str | None = None
        capability_attestation: dict[str, Any] = {
            "schema_version": 1,
            "thread_start_config": self._thread_config(),
            "off_contestant_clock": True,
            "fork_baseline_usage_notification": None,
        }
        capability_violation = False
        stderr_capture = _BoundedStderrCapture()

        def next_message(reader: _ProtocolReader) -> dict[str, Any]:
            nonlocal protocol_redactions
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                raise TimeoutError("Codex app-server preflight timed out")
            raw = reader.get(remaining)
            try:
                message = json.loads(raw)
            except json.JSONDecodeError as error:
                raise BenchmarkError("Codex app-server emitted malformed preflight JSONL") from error
            if not isinstance(message, dict):
                raise BenchmarkError("Codex app-server emitted a non-object preflight message")
            if "method" in message and "id" in message:
                raise BenchmarkError("Codex app-server requested a client action during preflight")
            rendered, redactions = _sanitized_protocol_line(message)
            safe_rendered, credential_redactions = self._redact_artifact_bytes(
                rendered.encode("utf-8")
            )
            event_archive.append(safe_rendered.decode("utf-8"))
            protocol_redactions += redactions + credential_redactions
            return message

        def await_result(reader: _ProtocolReader, request_id: int, method: str) -> Any:
            nonlocal observed_thread_id
            while True:
                message = next_message(reader)
                if "id" in message:
                    return self._response_result(message, request_id, method)
                notification_method = message.get("method")
                if not isinstance(notification_method, str):
                    raise BenchmarkError("Codex app-server emitted malformed preflight notification")
                params = message.get("params")
                if isinstance(params, Mapping):
                    if "threadId" in params and observed_thread_id is not None and params["threadId"] != observed_thread_id:
                        raise ProviderCapabilityViolation("Codex preflight emitted a foreign-thread notification")
                    if notification_method.startswith("item/") or notification_method.startswith("rawResponseItem/"):
                        _reject_collaboration_item(params.get("item"))
                if notification_method == "model/rerouted":
                    raise BenchmarkError("Codex preflight rerouted the frozen model")
                if (
                    notification_method == "thread/tokenUsage/updated"
                    and self.fork_source_thread_id is not None
                ):
                    if not isinstance(params, Mapping):
                        raise ProviderCapabilityViolation(
                            "Codex preflight fork baseline usage is malformed"
                        )
                    token_usage = params.get("tokenUsage")
                    total_payload = (
                        token_usage.get("total")
                        if isinstance(token_usage, Mapping)
                        else None
                    )
                    cumulative = (
                        _normalize_usage_breakdown(total_payload)
                        if isinstance(total_payload, Mapping)
                        else None
                    )
                    last_payload = (
                        token_usage.get("last")
                        if isinstance(token_usage, Mapping)
                        else None
                    )
                    last_usage = (
                        _normalize_usage_breakdown(last_payload)
                        if isinstance(last_payload, Mapping)
                        else None
                    )
                    if (
                        observed_thread_id is None
                        or params.get("threadId") != observed_thread_id
                        or params.get("turnId") != self.fork_source_last_turn_id
                        or cumulative != self.fork_source_cumulative_usage
                        or last_usage is None
                        or capability_attestation[
                            "fork_baseline_usage_notification"
                        ]
                        is not None
                    ):
                        raise ProviderCapabilityViolation(
                            "Codex preflight fork baseline does not match the frozen source"
                        )
                    capability_attestation[
                        "fork_baseline_usage_notification"
                    ] = {
                        "accepted": True,
                        "child_thread_id": observed_thread_id,
                        "source_turn_id": self.fork_source_last_turn_id,
                        "source_cumulative_usage": cumulative,
                        "source_last_usage": last_usage,
                        "excluded_from_contestant_usage": True,
                        "excluded_from_contestant_time": True,
                    }
                    continue
                if notification_method.startswith("turn/") or notification_method in (
                    "item/started", "item/updated", "item/completed",
                    "rawResponse/completed", "rawResponseItem/completed",
                    "thread/tokenUsage/updated",
                ):
                    raise BenchmarkError(
                        f"Codex app-server began model activity during preflight: {notification_method}"
                    )
                if notification_method == "thread/started":
                    params = message.get("params")
                    thread = params.get("thread") if isinstance(params, Mapping) else None
                    candidate = thread.get("id") if isinstance(thread, Mapping) else None
                    if not isinstance(candidate, str) or not candidate:
                        raise BenchmarkError("Codex app-server emitted malformed thread/started")
                    if observed_thread_id is not None and observed_thread_id != candidate:
                        raise ProviderCapabilityViolation("Codex preflight emitted a foreign thread")
                    observed_thread_id = candidate

        next_request_id = TURN_REQUEST_ID

        def request_capability(reader: _ProtocolReader, method: str, params: dict[str, Any]) -> Any:
            nonlocal next_request_id
            request_id = next_request_id
            next_request_id += 1
            assert process is not None and process.stdin is not None
            try:
                self._write_rpc(
                    process.stdin, {"id": request_id, "method": method, "params": params}
                )
                return await_result(reader, request_id, method)
            except (BenchmarkError, TimeoutError, BrokenPipeError, OSError) as error:
                raise ProviderCapabilityViolation(
                    f"Codex capability attestation failed at {method}: {error}"
                ) from error

        try:
            staged_auth = self._stage_auth()
            process = subprocess.Popen(
                command,
                cwd=workspace,
                env=environment,
                stdin=subprocess.PIPE,
                stdout=subprocess.PIPE,
                stderr=stderr_capture,
                text=True,
                bufsize=1,
                start_new_session=True,
            )
            stderr_capture.parent_after_spawn()
            assert process.stdin is not None and process.stdout is not None
            reader = _ProtocolReader(process.stdout)
            self._write_rpc(
                process.stdin,
                {
                    "id": INITIALIZE_REQUEST_ID,
                    "method": "initialize",
                    "params": {
                        "clientInfo": {
                            "name": APP_SERVER_CLIENT_NAME,
                            "version": APP_SERVER_CLIENT_VERSION,
                        },
                        "capabilities": {"experimentalApi": True},
                    },
                },
            )
            initialized = await_result(reader, INITIALIZE_REQUEST_ID, "initialize")
            if not isinstance(initialized, Mapping):
                raise BenchmarkError("Codex app-server returned malformed initialize result")
            self._write_rpc(process.stdin, {"method": "initialized"})
            cwd = "/workspace" if self.externally_sandboxed else str(workspace)
            capability_attestation["process_config"] = self._attest_config_read(
                request_capability(
                    reader, "config/read", {"cwd": cwd, "includeLayers": True}
                )
            )
            capability_attestation["global_features"] = self._attest_feature_list(
                lambda method, params: request_capability(reader, method, params),
                thread_id=None,
            )
            if self.fork_source_thread_id is None:
                thread_method = "thread/start"
                thread_params: dict[str, Any] = {
                    "approvalPolicy": "never",
                    "config": self._thread_config(),
                    "cwd": cwd,
                    "ephemeral": True,
                    "experimentalRawEvents": True,
                    "historyMode": "legacy",
                    "model": self.model,
                    "sandbox": (
                        "workspace-write" if self.workspace_writable else "read-only"
                    ),
                }
                expected_ephemeral = True
            else:
                expected_source_usage = self._load_usage_baseline(
                    self.fork_source_thread_id
                )
                if expected_source_usage != self.fork_source_cumulative_usage:
                    raise BenchmarkError(
                        "fork preflight checkpoint usage does not match its source"
                    )
                thread_method = "thread/fork"
                thread_params = {
                    "threadId": self.fork_source_thread_id,
                    "lastTurnId": self.fork_source_last_turn_id,
                    "ephemeral": False,
                }
                expected_ephemeral = False
            self._write_rpc(
                process.stdin,
                {
                    "id": THREAD_REQUEST_ID,
                    "method": thread_method,
                    "params": thread_params,
                },
            )
            thread_result = await_result(reader, THREAD_REQUEST_ID, thread_method)
            resolved_thread_id, thread_record = self._thread_from_result(
                thread_result, expected=None, expected_ephemeral=expected_ephemeral
            )
            if observed_thread_id is not None and observed_thread_id != resolved_thread_id:
                raise ProviderCapabilityViolation("Codex preflight thread notification/result mismatch")
            observed_thread_id = resolved_thread_id
            returned_model = thread_record.get("model")
            if returned_model is not None and returned_model != self.model:
                raise BenchmarkError("Codex preflight selected the wrong model")
            capability_attestation["thread_features"] = self._attest_feature_list(
                lambda method, params: request_capability(reader, method, params),
                thread_id=observed_thread_id,
            )
            capability_attestation["thread_creation"] = {
                "method": thread_method,
                "fork_source_thread_id": self.fork_source_thread_id,
                "fork_source_last_turn_id": self.fork_source_last_turn_id,
                "fork_source_cumulative_usage": self.fork_source_cumulative_usage,
            }
            capability_attestation["passed"] = True
            self._sync_private_auth_to_storage()
            self._remove_auth(staged_auth)
            staged_auth = None
            auth_removed = True
            self.seal_control_baseline()
            self._write_rpc(
                process.stdin,
                {
                    "id": next_request_id,
                    "method": "thread/backgroundTerminals/clean",
                    "params": {"threadId": observed_thread_id},
                },
            )
            cleanup_result = await_result(
                reader,
                next_request_id,
                "thread/backgroundTerminals/clean",
            )
            if not isinstance(cleanup_result, Mapping):
                raise BenchmarkError("Codex preflight returned malformed terminal cleanup")
            self._write_rpc(
                process.stdin,
                {
                    "id": next_request_id + 1,
                    "method": "thread/backgroundTerminals/list",
                    "params": {"threadId": observed_thread_id, "limit": 100},
                },
            )
            list_result = await_result(
                reader,
                next_request_id + 1,
                "thread/backgroundTerminals/list",
            )
            if (
                not isinstance(list_result, Mapping)
                or list_result.get("data") != []
                or list_result.get("nextCursor") not in (None, "")
            ):
                raise BenchmarkError("Codex preflight background terminals were not empty")
            background_terminal_methods_canary = True
        except ProviderCapabilityViolation as error:
            capability_violation = True
            failure = str(error)
        except (BenchmarkError, BrokenPipeError, OSError, TimeoutError) as error:
            failure = str(error)
        finally:
            if staged_auth is not None:
                try:
                    self._remove_auth(staged_auth)
                except BenchmarkError as error:
                    failure = failure or str(error)
            if process is not None:
                if process.stdin is not None:
                    try:
                        process.stdin.close()
                    except OSError:
                        pass
                try:
                    process.wait(timeout=2)
                except subprocess.TimeoutExpired:
                    try:
                        os.killpg(process.pid, signal.SIGTERM)
                    except ProcessLookupError:
                        pass
                    try:
                        process.wait(timeout=5)
                    except subprocess.TimeoutExpired:
                        try:
                            os.killpg(process.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        process.wait()
                if process.stdout is not None:
                    process.stdout.close()

        stderr_capture.finish()
        stderr_bytes = stderr_capture.snapshot()
        stderr_metadata = stderr_capture.metadata()
        stderr_capture.close()
        stderr_bytes, stderr_credential_redactions = self._redact_artifact_bytes(
            stderr_bytes
        )
        if failure is not None:
            safe_failure, failure_credential_redactions = self._redact_artifact_bytes(
                failure.encode("utf-8", errors="replace")
            )
            failure = safe_failure.decode("utf-8", errors="replace")
        else:
            failure_credential_redactions = 0
        event_archive.seal()
        write_bytes_atomic(artifact_dir / "stderr.log", stderr_bytes, mode=0o400)
        network_events = monitor.stop_and_seal() if monitor is not None else 0
        if network_events:
            failure = failure or "offline shell marker changed during provider-free preflight"
        if process is None:
            failure = failure or "Codex app-server preflight did not start"
        elif process.returncode not in (0, -signal.SIGTERM):
            failure = failure or f"Codex app-server preflight exited {process.returncode}"
        if auth_removed:
            try:
                self.assert_safe_control_surfaces(workspace)
            except BenchmarkError as error:
                failure = failure or str(error)
        record = {
            "schema_version": 1,
            "transport": "codex-app-server-stdio",
            "provider_call_permitted": False,
            "turn_start_sent": False,
            "background_terminal_methods_canary": background_terminal_methods_canary,
            "capability_attestation": capability_attestation,
            "failure_kind": "provider_capability_violation" if capability_violation else None,
            "command": command,
            "app_server_command": inner,
            "thread_id": observed_thread_id,
            "temporary_auth_removed_after_thread_start": auth_removed,
            "private_auth_runtime_tmpfs": self._private_runtime_is_tmpfs,
            "network_marker_inotify_events": network_events,
            "event_count": event_archive.count,
            "event_archive_bytes": event_archive.bytes,
            "event_archive_limit_bytes": MAX_EVENT_TRACE_BYTES,
            "event_archive_limit_count": MAX_EVENT_TRACE_COUNT,
            "event_trace_redactions": protocol_redactions,
            "event_trace_policy": "sanitized observable app-server events only",
            "events_sha256": sha256_file(artifact_dir / "events.jsonl"),
            "stderr_sha256": sha256_file(artifact_dir / "stderr.log"),
            "stderr_stream": stderr_metadata,
            "credential_redactions_before_publication": (
                stderr_credential_redactions + failure_credential_redactions
            ),
            "failure": failure,
        }
        if marker.is_file():
            record["network_violation_attempts"] = marker.stat().st_size
            os.chmod(marker, 0o400)
        write_json_atomic(artifact_dir / "preflight.json", record, mode=0o400)
        if failure is not None or not auth_removed or observed_thread_id is None:
            message = f"Codex app-server preflight failed: {failure or 'incomplete'}"
            if capability_violation:
                raise ProviderCapabilityViolation(message)
            raise BenchmarkError(message)
        return record

    @staticmethod
    def _stop_process(process: subprocess.Popen[str]) -> dict[str, Any]:
        """Close app-server stdio and report whether forced termination was needed."""

        returncode_before_close = process.poll()
        forced_signal: str | None = None
        if process.stdin is not None:
            try:
                process.stdin.close()
            except OSError:
                pass
        try:
            process.wait(timeout=2)
        except subprocess.TimeoutExpired:
            forced_signal = "SIGTERM"
            try:
                os.killpg(process.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                forced_signal = "SIGKILL"
                try:
                    os.killpg(process.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                process.wait()
        return {
            "returncode_before_close": returncode_before_close,
            "returncode": process.returncode,
            "forced_signal": forced_signal,
            "graceful": forced_signal is None and process.returncode == 0,
        }

    def close(self, *, artifact_dir: Path | None = None) -> None:
        """End the one live measured conversation and validate its idle boundary."""

        session = self._live_session
        self._live_session = None
        errors: list[str] = []
        staged_auth = session.auth_path if session is not None else self.state_root / "auth.json"
        if session is not None:
            shutdown = self._stop_process(session.process)
            try:
                self._sync_private_auth_to_storage()
            except (OSError, BenchmarkError) as error:
                errors.append(f"could not persist refreshed Codex authentication: {error}")
            stdout_drained_to_eof = False
            late_stdout = {"line_count": 0, "bytes": 0, "sha256": hashlib.sha256(b"").hexdigest()}
            try:
                late_stdout = session.reader.drain_until_eof(2.0)
                stdout_drained_to_eof = True
            except BenchmarkError as error:
                errors.append(str(error))
            finally:
                if session.process.stdout is not None:
                    session.process.stdout.close()
            if late_stdout["line_count"]:
                errors.append(
                    "Codex app-server emitted protocol messages after the final telemetry boundary"
                )
            try:
                session.stderr_capture.finish()
                final_stderr = session.stderr_capture.snapshot()
                stderr_stream = session.stderr_capture.metadata()
            except OSError as error:
                final_stderr = f"could not read final Codex stderr capture: {error}\n".encode(
                    "utf-8"
                )
                stderr_stream = None
                errors.append("could not read final Codex stderr capture")
            late_stderr, late_stderr_credential_redactions = self._redact_artifact_bytes(
                final_stderr[session.stderr_checkpoint :]
            )
            if artifact_dir is not None:
                try:
                    artifact_dir.mkdir(parents=True, exist_ok=False, mode=0o700)
                    write_bytes_atomic(
                        artifact_dir / "stderr-after-last-turn.log", late_stderr, mode=0o400
                    )
                    write_json_atomic(
                        artifact_dir / "shutdown.json",
                        {
                            "schema_version": 1,
                            "thread_id": session.thread_id,
                            "returncode_before_close": shutdown["returncode_before_close"],
                            "returncode": shutdown["returncode"],
                            "forced_signal": shutdown["forced_signal"],
                            "graceful": shutdown["graceful"],
                            "stdout_drained_to_eof": stdout_drained_to_eof,
                            "late_stdout_line_count": late_stdout["line_count"],
                            "late_stdout_bytes": late_stdout["bytes"],
                            "late_stdout_sha256": late_stdout["sha256"],
                            "stderr_scope": "bytes emitted after the last turn artifact snapshot",
                            "stderr_bytes": len(late_stderr),
                            "stderr_stream": stderr_stream,
                            "credential_redactions_before_publication": (
                                late_stderr_credential_redactions
                            ),
                            "stderr_sha256": sha256_file(
                                artifact_dir / "stderr-after-last-turn.log"
                            ),
                        },
                        mode=0o400,
                    )
                except (OSError, BenchmarkError) as error:
                    errors.append(f"could not archive Codex shutdown: {error}")
            if not shutdown["graceful"]:
                errors.append(
                    "Codex app-server did not exit cleanly at the conversation boundary "
                    f"(returncode={shutdown['returncode']}, forced={shutdown['forced_signal']})"
                )
            total_network_events = (
                session.network_monitor.stop_and_seal()
                if session.network_monitor is not None
                else 0
            )
            if total_network_events != session.network_checkpoint:
                errors.append("offline shell marker changed outside a measured turn")
            try:
                session.stderr_capture.close()
            except OSError as error:
                errors.append(f"could not close Codex stderr capture: {error}")
            try:
                self.assert_safe_control_surfaces(
                    session.workspace,
                    scan_workspace=session.workspace_safe_to_scan,
                )
            except BenchmarkError as error:
                errors.append(str(error))
        if staged_auth.exists() or staged_auth.is_symlink():
            try:
                self._remove_auth(staged_auth)
            except BenchmarkError as error:
                errors.append(str(error))
        if self._owned_control_root is not None:
            owned = self._owned_control_root
            self._owned_control_root = None
            try:
                shutil.rmtree(owned)
            except OSError as error:
                errors.append(f"could not remove private Codex runtime state: {error}")
        if errors:
            safe_error, _ = self._redact_artifact_bytes(
                "; ".join(errors).encode("utf-8", errors="replace")
            )
            raise BenchmarkError(safe_error.decode("utf-8", errors="replace"))

    def __enter__(self) -> "CodexDriver":
        return self

    def __exit__(self, exc_type: Any, exc: Any, traceback: Any) -> None:
        self.close()

    def run_turn(
        self,
        *,
        prompt: str,
        workspace: Path,
        artifact_dir: Path,
        timeout_seconds: float,
        thread_id: str | None = None,
        output_schema: Path | None = None,
        ephemeral: bool = False,
        sandbox: str = "workspace-write",
    ) -> TurnResult:
        del sandbox  # App-server policy is fixed; bwrap is the security boundary.
        workspace = workspace.resolve()
        if not workspace.is_dir() or workspace.is_symlink():
            raise BenchmarkError(f"unsafe Codex workspace: {workspace}")
        if timeout_seconds <= 0:
            raise BenchmarkError("Codex turn timeout must be positive")
        if ephemeral and (thread_id is not None or self._live_session is not None):
            raise BenchmarkError("an ephemeral Codex turn cannot reuse a conversation")
        if self._live_session is not None:
            session = self._live_session
            if workspace != session.workspace:
                raise BenchmarkError("live Codex conversation belongs to another workspace")
            if thread_id != session.thread_id:
                raise BenchmarkError("repair turn did not name the live Codex conversation")
            if session.process.poll() is not None:
                raise BenchmarkError("live Codex app-server ended between repair turns")
            self.assert_safe_control_surfaces(workspace)
        else:
            if thread_id is not None:
                raise BenchmarkError(
                    "cold thread/resume cannot preserve exact raw usage; the condition is nonresumable"
                )
            if self.fork_source_thread_id is None:
                if self._usage_record.exists() or self._usage_record.is_symlink():
                    raise BenchmarkError("completed Codex conversation cannot be restarted")
            else:
                expected_source_usage = self._load_usage_baseline(
                    self.fork_source_thread_id
                )
                if expected_source_usage != self.fork_source_cumulative_usage:
                    raise BenchmarkError("fork checkpoint usage does not match its source")
            if self._control_baseline.is_file():
                self.assert_safe_control_surfaces(workspace)
            else:
                if any(self.state_root.iterdir()):
                    raise BenchmarkError("Codex state is nonempty and unsealed")
                self._assert_safe_workspace(workspace)

        artifact_dir.mkdir(parents=True, exist_ok=False)
        # Seed and seal Codex-generated control files without launching a model.
        # The measured app-server can then mount those top-level surfaces read-only.
        if self._live_session is None and not self._control_baseline.is_file():
            self.preflight(
                workspace=workspace,
                artifact_dir=artifact_dir / "control-preflight",
                timeout_seconds=60,
            )
        controlled_passwd_sha256 = sha256_file(self._identity_root / "passwd")
        prompt_path = artifact_dir / "prompt.md"
        write_bytes_atomic(prompt_path, prompt.encode("utf-8"), mode=0o400)
        schema_payload: Mapping[str, Any] | None = None
        if output_schema is not None:
            if not output_schema.is_file() or output_schema.is_symlink():
                raise BenchmarkError(f"unsafe Codex output schema: {output_schema}")
            try:
                parsed_schema = json.loads(output_schema.read_text(encoding="utf-8"))
            except json.JSONDecodeError as error:
                raise BenchmarkError("Codex output schema is invalid JSON") from error
            if not isinstance(parsed_schema, Mapping):
                raise BenchmarkError("Codex output schema must be a JSON object")
            schema_payload = parsed_schema

        started_wall = utc_now()
        started = time.perf_counter_ns()
        bootstrap_deadline = time.monotonic() + 60.0
        active_deadline: float | None = None
        telemetry_deadline: float | None = None
        post_terminal_timeout_kind: str | None = None
        timeout_kind: str | None = None
        event_archive = _BoundedEventArchive(artifact_dir / "events.jsonl")
        protocol_redactions = 0
        final_message = ""
        observed_thread_id = thread_id
        observed_turn_id: str | None = None
        terminal_status: str | None = None
        terminal_event_perf_ns: int | None = None
        latest_cumulative: dict[str, int] | None = None
        latest_cumulative_cache_write_defaulted: bool | None = None
        fork_cumulative_usage_semantics: str | None = None
        raw_responses: dict[str, dict[str, Any]] = {}
        cumulative_usage_notifications: list[dict[str, Any]] = []
        active_context_compactions: set[str] = set()
        context_compaction_item_count = 0
        background_terminal_cleanup: dict[str, Any] | None = None
        workspace_usage: dict[str, int] | None = None
        workspace_limit_violation = False
        artifact_limit_violation = False
        post_terminal_telemetry_settle: dict[str, Any] | None = None
        protocol_error: str | None = None
        capability_violation = False
        capability_attestation: dict[str, Any] = {
            "schema_version": 1,
            "thread_start_config": self._thread_config(),
            "off_contestant_clock": True,
            "reused_thread": self._live_session is not None,
            "fork_baseline_usage_notification": None,
        }
        telemetry_invalid = False
        timed_out = False
        private_auth_ready_before_turn_start = False
        staged_auth: Path | None = None
        active_started_perf_ns: int | None = None
        active_ended_perf_ns: int | None = None
        reused_session = self._live_session is not None
        process: subprocess.Popen[str] | None = None
        reader: _ProtocolReader | None = None
        stderr_capture: Any = None
        monitor: _NetworkViolationMonitor | None = None
        network_before = 0
        command_resources_before = command_cgroup_snapshot(required=False)
        command_resources_after: dict[str, Any] | None = None
        command_resource_delta: dict[str, int] = {}
        command_resource_violation = False

        if reused_session:
            assert self._live_session is not None
            live = self._live_session
            process = live.process
            reader = live.reader
            stderr_capture = live.stderr_capture
            command = live.command
            inner = live.inner
            baseline = dict(live.cumulative_usage)
            marker = live.network_marker
            monitor = live.network_monitor
            network_before = (
                monitor.checkpoint() if monitor is not None else live.network_checkpoint
            )
            if network_before != live.network_checkpoint:
                raise BenchmarkError("offline shell marker changed between repair turns")
            self._refresh_private_auth_from_storage()
            private_auth_ready_before_turn_start = (
                self._assert_private_auth_file() == live.auth_path
            )
        else:
            baseline = (
                dict(self.fork_source_cumulative_usage)
                if self.fork_source_cumulative_usage is not None
                else _zero_usage()
            )
            command_codex = "/codex" if self.externally_sandboxed else str(self.codex_binary)
            inner = self._app_server_command(command_codex)
            marker = self._session_marker if not ephemeral else artifact_dir / "network_violations.bin"
            if not ephemeral and (marker.exists() or marker.is_symlink()):
                raise BenchmarkError("stale persistent-session network marker")
            command = (
                self._bwrap_command(
                    inner,
                    workspace=workspace,
                    artifact_dir=artifact_dir,
                    output_schema=output_schema,
                    network_marker=marker,
                )
                if self.externally_sandboxed
                else inner
            )
            environment = (
                {"PATH": "/usr/bin"}
                if self.externally_sandboxed
                else {
                    "CODEX_HOME": str(self.state_root),
                    "HOME": str(self.state_root.parent),
                    "LANG": "C.UTF-8",
                    "LC_ALL": "C.UTF-8",
                    "LOGNAME": "bench",
                    "NO_COLOR": "1",
                    "PATH": os.environ.get("PATH", "/usr/bin"),
                    "SHELL": str(self.offline_shell) if self.offline_shell else "/bin/sh",
                    "TZ": "UTC",
                    "USER": "bench",
                }
            )
            if self.externally_sandboxed:
                monitor = _NetworkViolationMonitor(marker)
                monitor.start()
            stderr_capture = _BoundedStderrCapture()

        def remaining() -> float:
            nonlocal timeout_kind
            if active_started_perf_ns is None:
                deadline = bootstrap_deadline
                label = "Codex app-server bootstrap timed out"
                kind = "bootstrap"
            elif active_ended_perf_ns is None:
                assert active_deadline is not None
                choices = [
                    (
                        active_deadline,
                        "Codex turn exceeded its active-time allowance",
                        "active",
                    )
                ]
                if telemetry_deadline is not None:
                    choices.append(
                        (
                            telemetry_deadline,
                            (
                                "Codex terminal telemetry did not settle"
                                if post_terminal_timeout_kind == "telemetry"
                                else "Codex background-terminal quiescence timed out"
                            ),
                            post_terminal_timeout_kind or "quiescence",
                        )
                    )
                deadline, label, kind = min(choices, key=lambda item: item[0])
            else:
                assert telemetry_deadline is not None
                deadline = telemetry_deadline
                label = "Codex terminal telemetry did not settle"
                kind = "telemetry"
            value = deadline - time.monotonic()
            if value <= 0:
                timeout_kind = kind
                raise TimeoutError(label)
            return value

        def parse_message(raw: str) -> dict[str, Any]:
            nonlocal artifact_limit_violation, protocol_redactions
            try:
                message = json.loads(raw)
            except json.JSONDecodeError as error:
                raise BenchmarkError("Codex app-server emitted malformed JSONL") from error
            if not isinstance(message, dict):
                raise BenchmarkError("Codex app-server emitted a non-object message")
            if "method" in message and "id" in message:
                raise BenchmarkError(
                    "Codex app-server requested an unsupported client action: "
                    f"{message.get('method')!r}"
                )
            rendered, redactions = _sanitized_protocol_line(message)
            try:
                safe_rendered, credential_redactions = self._redact_artifact_bytes(
                    rendered.encode("utf-8")
                )
                event_archive.append(safe_rendered.decode("utf-8"))
            except BenchmarkError:
                artifact_limit_violation = True
                raise
            protocol_redactions += redactions + credential_redactions
            return message

        def read_message() -> dict[str, Any]:
            assert reader is not None
            while True:
                wait_seconds = remaining()
                try:
                    raw = reader.get(wait_seconds)
                    break
                except TimeoutError:
                    # Re-evaluate the named active/telemetry/quiescence
                    # deadline so a queue timeout receives the benchmark's
                    # correct classification instead of a generic message.
                    remaining()
            return parse_message(raw)

        def await_response(*, request_id: int, method: str, notification: Any) -> Any:
            while True:
                message = read_message()
                if "id" in message:
                    return self._response_result(message, request_id, method)
                notification(message)

        def request_capability(method: str, params: dict[str, Any]) -> Any:
            request_id = self._next_turn_request_id
            self._next_turn_request_id += 1
            assert process is not None and process.stdin is not None
            try:
                self._write_rpc(
                    process.stdin, {"id": request_id, "method": method, "params": params}
                )
                return await_response(
                    request_id=request_id,
                    method=method,
                    notification=startup_notification,
                )
            except (BenchmarkError, TimeoutError, BrokenPipeError, OSError) as error:
                raise ProviderCapabilityViolation(
                    f"Codex capability attestation failed at {method}: {error}"
                ) from error

        def accept_fork_baseline_usage(
            message: Mapping[str, Any], *, phase: str
        ) -> bool:
            """Validate copied-parent usage telemetry without charging the child.

            App-server may emit the forked thread's inherited cumulative usage
            immediately after ``thread/fork`` and before the child task turn.
            This is provenance telemetry for the copied history, not a model
            response.  Admit exactly one such notification only when every
            identity and usage field matches the frozen source checkpoint.
            """

            if (
                message.get("method") != "thread/tokenUsage/updated"
                or self.fork_source_thread_id is None
                or observed_turn_id is not None
            ):
                return False
            params = message.get("params")
            if not isinstance(params, Mapping):
                raise ProviderCapabilityViolation(
                    "Codex fork baseline usage notification is malformed"
                )
            if observed_thread_id is None or params.get("threadId") != observed_thread_id:
                raise ProviderCapabilityViolation(
                    "Codex fork baseline usage belongs to another thread"
                )
            if params.get("turnId") != self.fork_source_last_turn_id:
                raise ProviderCapabilityViolation(
                    "Codex fork baseline usage names the wrong source turn"
                )
            token_usage = params.get("tokenUsage")
            total_payload = (
                token_usage.get("total") if isinstance(token_usage, Mapping) else None
            )
            cumulative = (
                _normalize_usage_breakdown(total_payload)
                if isinstance(total_payload, Mapping)
                else None
            )
            if cumulative != self.fork_source_cumulative_usage:
                raise ProviderCapabilityViolation(
                    "Codex fork baseline usage does not match the frozen source"
                )
            if capability_attestation["fork_baseline_usage_notification"] is not None:
                raise ProviderCapabilityViolation(
                    "Codex emitted duplicate fork baseline usage telemetry"
                )
            last_payload = (
                token_usage.get("last") if isinstance(token_usage, Mapping) else None
            )
            last_usage = (
                _normalize_usage_breakdown(last_payload)
                if isinstance(last_payload, Mapping)
                else None
            )
            if last_usage is None:
                raise ProviderCapabilityViolation(
                    "Codex fork baseline last-turn usage is malformed"
                )
            capability_attestation["fork_baseline_usage_notification"] = {
                "accepted": True,
                "phase": phase,
                "child_thread_id": observed_thread_id,
                "source_turn_id": self.fork_source_last_turn_id,
                "source_cumulative_usage": cumulative,
                "source_last_usage": last_usage,
                "excluded_from_contestant_usage": True,
                "excluded_from_contestant_time": True,
            }
            return True

        def startup_notification(message: Mapping[str, Any]) -> None:
            nonlocal observed_thread_id
            method = message.get("method")
            if not isinstance(method, str):
                raise BenchmarkError("Codex app-server emitted a malformed notification")
            if method == "model/rerouted":
                raise BenchmarkError("Codex app-server rerouted the frozen model")
            params = message.get("params")
            if isinstance(params, Mapping):
                if "threadId" in params and observed_thread_id is not None and params["threadId"] != observed_thread_id:
                    raise ProviderCapabilityViolation("Codex emitted a foreign-thread notification")
                if method.startswith("item/") or method.startswith("rawResponseItem/"):
                    _reject_collaboration_item(params.get("item"))
            if method.startswith("turn/") or method in (
                "thread/tokenUsage/updated",
                "rawResponse/completed",
                "rawResponseItem/completed",
            ):
                if accept_fork_baseline_usage(message, phase="startup_attestation"):
                    return
                raise BenchmarkError(f"Codex app-server emitted premature {method}")
            if method == "thread/started":
                params = message.get("params")
                thread = params.get("thread") if isinstance(params, Mapping) else None
                candidate = thread.get("id") if isinstance(thread, Mapping) else None
                if not isinstance(candidate, str) or not candidate:
                    raise BenchmarkError("Codex app-server emitted malformed thread/started")
                if observed_thread_id is not None and observed_thread_id != candidate:
                    raise ProviderCapabilityViolation("Codex app-server emitted a foreign thread")
                observed_thread_id = candidate

        def turn_notification(message: Mapping[str, Any]) -> None:
            nonlocal observed_turn_id, terminal_status, latest_cumulative, final_message
            nonlocal latest_cumulative_cache_write_defaulted
            nonlocal terminal_event_perf_ns, telemetry_deadline
            nonlocal post_terminal_timeout_kind
            nonlocal telemetry_invalid
            nonlocal context_compaction_item_count
            method = message.get("method")
            params = message.get("params")
            if not isinstance(method, str):
                raise BenchmarkError("Codex app-server emitted a malformed notification")
            if method == "model/rerouted":
                raise BenchmarkError("Codex app-server rerouted the frozen model")
            if method == "thread/started":
                raise ProviderCapabilityViolation("Codex started a child thread during a turn")
            if accept_fork_baseline_usage(
                message, phase="after_turn_request_before_turn_started"
            ):
                return
            if isinstance(params, Mapping):
                if "threadId" in params and params["threadId"] != observed_thread_id:
                    raise ProviderCapabilityViolation("Codex emitted a foreign-thread notification")
                if method.startswith("item/") or method.startswith("rawResponseItem/"):
                    _reject_collaboration_item(params.get("item"))
            if method in (
                "turn/started",
                "turn/completed",
                "thread/tokenUsage/updated",
                "item/started",
                "item/updated",
                "item/completed",
                "rawResponse/completed",
                "rawResponseItem/completed",
            ):
                if not isinstance(params, Mapping):
                    raise BenchmarkError(f"Codex app-server emitted malformed {method}")
                if params.get("threadId") != observed_thread_id:
                    raise BenchmarkError(f"Codex app-server emitted {method} for another thread")
            if method == "rawResponse/completed":
                response_id = params.get("responseId")
                candidate_turn_id = params.get("turnId")
                if (
                    not isinstance(response_id, str)
                    or not response_id
                    or not isinstance(candidate_turn_id, str)
                    or not candidate_turn_id
                ):
                    telemetry_invalid = True
                    raise BenchmarkError("Codex raw response lacks a response or turn identity")
                if observed_turn_id is not None and candidate_turn_id != observed_turn_id:
                    telemetry_invalid = True
                    raise BenchmarkError("Codex raw response belongs to another turn")
                observed_turn_id = candidate_turn_id
                usage_payload = params.get("usage")
                usage = _normalize_raw_usage(usage_payload)
                if usage is None:
                    telemetry_invalid = True
                    raise BenchmarkError("Codex raw response usage is null or malformed")
                canonical = {
                    "thread_id": params.get("threadId"),
                    "turn_id": candidate_turn_id,
                    "usage": usage,
                    "cache_write_input_tokens_defaulted": (
                        isinstance(usage_payload, Mapping)
                        and "cacheWriteInputTokens" not in usage_payload
                    ),
                    "usage_class": (
                        "context_compaction"
                        if active_context_compactions
                        else "turn_work"
                    ),
                }
                prior = raw_responses.get(response_id)
                if prior is not None and prior != canonical:
                    telemetry_invalid = True
                    raise BenchmarkError("Codex reused a raw response id inconsistently")
                raw_responses[response_id] = canonical
            elif method == "rawResponseItem/completed":
                item = params.get("item")
                item_type = item.get("type") if isinstance(item, Mapping) else None
                normalized_item_type = (
                    "".join(character for character in item_type.casefold() if character.isalnum())
                    if isinstance(item_type, str)
                    else ""
                )
                if "websearch" in normalized_item_type or "mcp" in normalized_item_type:
                    raise BenchmarkError(
                        f"prohibited external raw tool item emitted: {item_type!r}"
                    )
            elif method == "turn/started":
                turn = params.get("turn")
                candidate = turn.get("id") if isinstance(turn, Mapping) else None
                if not isinstance(candidate, str) or not candidate:
                    raise BenchmarkError("Codex app-server emitted malformed turn/started")
                if observed_turn_id is not None and observed_turn_id != candidate:
                    raise BenchmarkError("Codex app-server emitted inconsistent turn ids")
                observed_turn_id = candidate
            elif method == "thread/tokenUsage/updated":
                candidate = params.get("turnId")
                if not isinstance(candidate, str) or not candidate:
                    telemetry_invalid = True
                    raise BenchmarkError("Codex usage notification has no turn id")
                if observed_turn_id is not None and candidate != observed_turn_id:
                    telemetry_invalid = True
                    raise BenchmarkError("Codex usage notification belongs to another turn")
                observed_turn_id = candidate
                token_usage = params.get("tokenUsage")
                total_usage = (
                    token_usage.get("total")
                    if isinstance(token_usage, Mapping)
                    else None
                )
                cumulative = (
                    _normalize_usage_breakdown(total_usage)
                    if isinstance(total_usage, Mapping)
                    else None
                )
                if cumulative is None:
                    telemetry_invalid = True
                    raise BenchmarkError("Codex app-server emitted malformed cumulative usage")
                last_usage_payload = (
                    token_usage.get("last")
                    if isinstance(token_usage, Mapping)
                    else None
                )
                last_usage = (
                    _normalize_usage_breakdown(last_usage_payload)
                    if isinstance(last_usage_payload, Mapping)
                    else None
                )
                if last_usage is None:
                    telemetry_invalid = True
                    raise BenchmarkError(
                        "Codex app-server emitted malformed last-response usage"
                    )
                previous_cumulative = latest_cumulative or baseline
                child_reset = (
                    latest_cumulative is None
                    and self.fork_source_thread_id is not None
                    and not reused_session
                    and cumulative == last_usage
                )
                if child_reset:
                    previous_cumulative = _zero_usage()
                try:
                    notification_delta = _usage_delta(
                        cumulative, previous_cumulative
                    )
                except BenchmarkError as error:
                    telemetry_invalid = True
                    raise BenchmarkError(
                        "Codex cumulative usage regressed within a turn"
                    ) from error
                if any(
                    notification_delta[field] != last_usage[field]
                    for field in _zero_usage()
                ):
                    telemetry_invalid = True
                    raise BenchmarkError(
                        "Codex last-response usage disagrees with the cumulative delta"
                    )
                cumulative_usage_notifications.append(
                    {
                        "sequence": len(cumulative_usage_notifications) + 1,
                        "turn_id": candidate,
                        "last_usage": last_usage,
                        "cumulative_usage": cumulative,
                        "cumulative_delta": notification_delta,
                        "received_after_turn_completed": terminal_status is not None,
                    }
                )
                latest_cumulative = cumulative
                latest_cumulative_cache_write_defaulted = not any(
                    name in total_usage
                    for name in ("cacheWriteInputTokens", "cache_write_input_tokens")
                )
            elif method == "item/started":
                item = params.get("item")
                if isinstance(item, Mapping) and item.get("type") == "contextCompaction":
                    item_id = item.get("id")
                    if not isinstance(item_id, str) or not item_id:
                        raise BenchmarkError("Codex context compaction has no identity")
                    active_context_compactions.add(item_id)
                    context_compaction_item_count += 1
            elif method == "item/completed":
                candidate = params.get("turnId")
                if observed_turn_id is not None and candidate != observed_turn_id:
                    raise BenchmarkError("Codex item/completed belongs to another turn")
                item = params.get("item")
                if isinstance(item, Mapping) and item.get("type") == "contextCompaction":
                    item_id = item.get("id")
                    if item_id not in active_context_compactions:
                        raise BenchmarkError("Codex completed an unknown context compaction")
                    active_context_compactions.remove(str(item_id))
                item_type = item.get("type") if isinstance(item, Mapping) else None
                normalized_item_type = (
                    "".join(character for character in item_type.casefold() if character.isalnum())
                    if isinstance(item_type, str)
                    else ""
                )
                if "websearch" in normalized_item_type or "mcp" in normalized_item_type:
                    raise BenchmarkError(
                        f"prohibited external tool item emitted: {item_type!r}"
                    )
                if isinstance(item, Mapping) and item.get("type") in (
                    "agentMessage",
                    "agent_message",
                ):
                    text_value = item.get("text")
                    if not isinstance(text_value, str):
                        raise BenchmarkError("Codex agent message has malformed text")
                    final_message = text_value
            elif method == "turn/completed":
                turn = params.get("turn")
                candidate = turn.get("id") if isinstance(turn, Mapping) else None
                status = turn.get("status") if isinstance(turn, Mapping) else None
                if not isinstance(candidate, str) or not candidate:
                    raise BenchmarkError("Codex app-server emitted malformed turn/completed")
                if observed_turn_id is not None and candidate != observed_turn_id:
                    raise BenchmarkError("Codex app-server completed another turn")
                if status not in ("completed", "failed", "interrupted"):
                    raise BenchmarkError("Codex app-server emitted invalid terminal turn status")
                observed_turn_id = candidate
                terminal_status = status
                if terminal_event_perf_ns is None:
                    terminal_event_perf_ns = time.perf_counter_ns()
                    telemetry_deadline = (
                        time.monotonic() + POST_TERMINAL_TELEMETRY_TIMEOUT_SECONDS
                    )
                    post_terminal_timeout_kind = "telemetry"

        try:
            if not reused_session:
                staged_auth = self._stage_auth()
                process = subprocess.Popen(
                    command,
                    cwd=workspace,
                    env=environment,
                    stdin=subprocess.PIPE,
                    stdout=subprocess.PIPE,
                    stderr=stderr_capture,
                    text=True,
                    bufsize=1,
                    start_new_session=True,
                )
                stderr_capture.parent_after_spawn()
                assert process.stdin is not None and process.stdout is not None
                reader = _ProtocolReader(process.stdout)
                self._write_rpc(
                    process.stdin,
                    {
                        "id": INITIALIZE_REQUEST_ID,
                        "method": "initialize",
                        "params": {
                            "clientInfo": {
                                "name": APP_SERVER_CLIENT_NAME,
                                "version": APP_SERVER_CLIENT_VERSION,
                            },
                            "capabilities": {"experimentalApi": True},
                        },
                    },
                )
                initialized = await_response(
                    request_id=INITIALIZE_REQUEST_ID,
                    method="initialize",
                    notification=startup_notification,
                )
                if not isinstance(initialized, Mapping):
                    raise BenchmarkError("Codex app-server returned malformed initialize result")
                self._write_rpc(process.stdin, {"method": "initialized"})
                cwd = "/workspace" if self.externally_sandboxed else str(workspace)
                capability_attestation["process_config"] = self._attest_config_read(
                    request_capability(
                        "config/read", {"cwd": cwd, "includeLayers": True}
                    )
                )
                capability_attestation["global_features"] = self._attest_feature_list(
                    request_capability, thread_id=None
                )
                if self.fork_source_thread_id is None:
                    thread_method = "thread/start"
                    thread_params: dict[str, Any] = {
                        "approvalPolicy": "never",
                        "config": self._thread_config(),
                        "cwd": cwd,
                        "ephemeral": ephemeral,
                        "experimentalRawEvents": True,
                        "historyMode": "legacy",
                        "model": self.model,
                        "sandbox": "workspace-write" if self.workspace_writable else "read-only",
                    }
                else:
                    if ephemeral:
                        raise BenchmarkError("a benchmark warm-start fork must be persistent")
                    thread_method = "thread/fork"
                    thread_params = {
                        "threadId": self.fork_source_thread_id,
                        "lastTurnId": self.fork_source_last_turn_id,
                        "ephemeral": False,
                    }
                self._write_rpc(
                    process.stdin,
                    {
                        "id": THREAD_REQUEST_ID,
                        "method": thread_method,
                        "params": thread_params,
                    },
                )
                thread_result = await_response(
                    request_id=THREAD_REQUEST_ID,
                    method=thread_method,
                    notification=startup_notification,
                )
                resolved_thread_id, thread_record = self._thread_from_result(
                    thread_result, expected=None, expected_ephemeral=ephemeral
                )
                if observed_thread_id is not None and observed_thread_id != resolved_thread_id:
                    raise ProviderCapabilityViolation("Codex thread notification/result mismatch")
                observed_thread_id = resolved_thread_id
                returned_model = thread_record.get("model")
                if returned_model is not None and returned_model != self.model:
                    raise BenchmarkError("Codex app-server selected the wrong model")
                capability_attestation["thread_features"] = self._attest_feature_list(
                    request_capability, thread_id=observed_thread_id
                )
                capability_attestation["thread_creation"] = {
                    "method": thread_method,
                    "fork_source_thread_id": self.fork_source_thread_id,
                    "fork_source_last_turn_id": self.fork_source_last_turn_id,
                    "fork_source_cumulative_usage": self.fork_source_cumulative_usage,
                }
                private_auth_ready_before_turn_start = (
                    self._assert_private_auth_file() == staged_auth
                )
                self.seal_control_baseline()
                network_before = monitor.checkpoint() if monitor is not None else 0
                if network_before:
                    raise BenchmarkError("offline shell marker changed during app-server startup")
                if not ephemeral:
                    assert process is not None and reader is not None
                    self._live_session = _LiveSession(
                        process=process,
                        reader=reader,
                        stderr_capture=stderr_capture,
                        command=command,
                        inner=inner,
                        workspace=workspace,
                        thread_id=resolved_thread_id,
                        cumulative_usage=dict(baseline),
                        network_marker=marker,
                        network_monitor=monitor,
                        network_checkpoint=network_before,
                        stderr_checkpoint=0,
                        auth_path=staged_auth,
                    )
                    staged_auth = None
            assert process is not None and process.stdin is not None and reader is not None
            assert observed_thread_id is not None
            if reused_session:
                cwd = "/workspace" if self.externally_sandboxed else str(workspace)
                capability_attestation["process_config"] = self._attest_config_read(
                    request_capability(
                        "config/read", {"cwd": cwd, "includeLayers": True}
                    )
                )
                capability_attestation["global_features"] = self._attest_feature_list(
                    request_capability, thread_id=None
                )
                capability_attestation["thread_features"] = self._attest_feature_list(
                    request_capability, thread_id=observed_thread_id
                )
            capability_attestation["passed"] = True
            if not private_auth_ready_before_turn_start:
                raise BenchmarkError(
                    "refreshable private Codex authentication was unavailable before turn/start"
                )
            turn_params: dict[str, Any] = {
                "approvalPolicy": "never",
                "cwd": "/workspace" if self.externally_sandboxed else str(workspace),
                "effort": self.reasoning_effort,
                "input": [{"type": "text", "text": prompt}],
                "model": self.model,
                "sandboxPolicy": (
                    {
                        "type": "workspaceWrite",
                        "writableRoots": [],
                        "networkAccess": False,
                        "excludeSlashTmp": False,
                        "excludeTmpdirEnvVar": False,
                    }
                    if self.workspace_writable
                    else {"type": "readOnly", "networkAccess": False}
                ),
                "threadId": observed_thread_id,
            }
            if schema_payload is not None:
                turn_params["outputSchema"] = dict(schema_payload)
            request_id = self._next_turn_request_id
            self._next_turn_request_id += 1
            active_started_perf_ns = time.perf_counter_ns()
            active_deadline = time.monotonic() + timeout_seconds
            self._write_rpc(
                process.stdin,
                {"id": request_id, "method": "turn/start", "params": turn_params},
            )
            turn_response: Any | None = None
            while turn_response is None or terminal_status is None:
                message = read_message()
                if "id" in message:
                    if turn_response is not None:
                        raise BenchmarkError("Codex app-server duplicated the turn/start response")
                    turn_response = self._response_result(message, request_id, "turn/start")
                    response_turn_id = self._turn_from_result(turn_response)
                    if observed_turn_id is not None and observed_turn_id != response_turn_id:
                        raise BenchmarkError("Codex turn notification/result mismatch")
                    observed_turn_id = response_turn_id
                else:
                    turn_notification(message)
            cleanup_started = time.perf_counter_ns()
            telemetry_deadline = time.monotonic() + 60.0
            post_terminal_timeout_kind = "quiescence"
            cleanup_request_id = self._next_turn_request_id
            self._next_turn_request_id += 1
            self._write_rpc(
                process.stdin,
                {
                    "id": cleanup_request_id,
                    "method": "thread/backgroundTerminals/clean",
                    "params": {"threadId": observed_thread_id},
                },
            )
            cleanup_result = await_response(
                request_id=cleanup_request_id,
                method="thread/backgroundTerminals/clean",
                notification=turn_notification,
            )
            if not isinstance(cleanup_result, Mapping):
                raise BenchmarkError("Codex returned malformed background-terminal cleanup")
            list_request_id = self._next_turn_request_id
            self._next_turn_request_id += 1
            self._write_rpc(
                process.stdin,
                {
                    "id": list_request_id,
                    "method": "thread/backgroundTerminals/list",
                    "params": {"threadId": observed_thread_id, "limit": 100},
                },
            )
            list_result = await_response(
                request_id=list_request_id,
                method="thread/backgroundTerminals/list",
                notification=turn_notification,
            )
            if (
                not isinstance(list_result, Mapping)
                or list_result.get("data") != []
                or list_result.get("nextCursor") not in (None, "")
            ):
                raise BenchmarkError("background terminals remained after cleanup")
            try:
                workspace_usage = bounded_tree_usage(
                    workspace,
                    maximum_entries=MAX_WORKSPACE_ENTRIES,
                    maximum_bytes=MAX_WORKSPACE_BYTES,
                )
            except BenchmarkError:
                workspace_limit_violation = True
                if self._live_session is not None:
                    self._live_session.workspace_safe_to_scan = False
                raise
            cleanup_ended_perf_ns = time.perf_counter_ns()
            background_terminal_cleanup = {
                "cleaned": True,
                "verified_empty": True,
                "excluded_from_contestant_measurement": False,
                "wall_seconds": (
                    cleanup_ended_perf_ns - cleanup_started
                )
                / 1_000_000_000,
            }
            # Workspace quiescence is the model-active boundary. Telemetry
            # ordering below is trusted measurement overhead, not contestant
            # work, and is therefore logged separately off-clock.
            active_ended_perf_ns = cleanup_ended_perf_ns
            # Establish an ordered server-side barrier after terminal cleanup,
            # then drain a bounded quiet interval. Raw usage notifications can
            # be emitted slightly after turn/completed; without this boundary
            # they could be omitted or leak into the next repair turn.
            telemetry_deadline = (
                time.monotonic() + POST_TERMINAL_TELEMETRY_TIMEOUT_SECONDS
            )
            post_terminal_timeout_kind = "telemetry"
            barrier_request_id = self._next_turn_request_id
            self._next_turn_request_id += 1
            self._write_rpc(
                process.stdin,
                {
                    "id": barrier_request_id,
                    "method": "thread/read",
                    "params": {"threadId": observed_thread_id, "includeTurns": False},
                },
            )
            barrier_result = await_response(
                request_id=barrier_request_id,
                method="thread/read",
                notification=turn_notification,
            )
            barrier_thread_id, _barrier_thread = self._thread_from_result(
                barrier_result,
                expected=observed_thread_id,
                expected_ephemeral=ephemeral,
            )
            if barrier_thread_id != observed_thread_id:
                raise BenchmarkError("Codex telemetry barrier returned another thread")

            settle_started = time.perf_counter_ns()
            quiet_started = settle_started
            quiet_deadline = time.monotonic() + POST_TERMINAL_QUIET_SECONDS
            while True:
                quiet_remaining = quiet_deadline - time.monotonic()
                if quiet_remaining <= 0:
                    break
                wait_seconds = min(remaining(), quiet_remaining)
                try:
                    late_raw = reader.get(wait_seconds)
                except TimeoutError:
                    # First propagate a contestant-active or total telemetry
                    # deadline. A timeout only at the short quiet boundary is
                    # the successful end of the drain.
                    remaining()
                    if time.monotonic() >= quiet_deadline:
                        break
                    continue
                late_message = parse_message(late_raw)
                if "id" in late_message:
                    raise BenchmarkError(
                        "Codex app-server emitted an unexpected response after telemetry barrier"
                    )
                turn_notification(late_message)
                quiet_deadline = time.monotonic() + POST_TERMINAL_QUIET_SECONDS
            telemetry_quiet_seconds = (
                time.perf_counter_ns() - quiet_started
            ) / 1_000_000_000
            post_terminal_telemetry_settle = {
                "thread_read_ordering_barrier": True,
                "post_barrier_quiet_seconds": telemetry_quiet_seconds,
                "excluded_from_contestant_measurement": True,
                "wall_seconds": (
                    time.perf_counter_ns() - settle_started
                )
                / 1_000_000_000,
            }
            post_terminal_timeout_kind = None
            if terminal_status != "completed":
                protocol_error = f"Codex turn ended with status {terminal_status}"
        except TimeoutError as error:
            if active_started_perf_ns is not None and active_ended_perf_ns is None:
                active_ended_perf_ns = time.perf_counter_ns()
                active_was_first = (
                    active_deadline is not None
                    and time.monotonic() >= active_deadline
                    and (
                        telemetry_deadline is None
                        or active_deadline <= telemetry_deadline
                    )
                )
                timed_out = timeout_kind == "active" or active_was_first
            if timeout_kind == "telemetry":
                telemetry_invalid = True
            protocol_error = str(error)
        except ProviderCapabilityViolation as error:
            capability_violation = True
            if active_started_perf_ns is not None and active_ended_perf_ns is None:
                active_ended_perf_ns = time.perf_counter_ns()
            protocol_error = str(error)
        except (BenchmarkError, BrokenPipeError, OSError) as error:
            if active_started_perf_ns is not None and active_ended_perf_ns is None:
                active_ended_perf_ns = time.perf_counter_ns()
            protocol_error = str(error)
        stopped = time.perf_counter_ns()
        try:
            command_resources_after = command_cgroup_snapshot(required=False)
            command_resource_delta = command_cgroup_limit_delta(
                command_resources_before, command_resources_after
            )
            command_resource_violation = any(command_resource_delta.values())
            if command_resource_violation:
                protocol_error = protocol_error or (
                    "generated-command cgroup resource ceiling was reached"
                )
        except BenchmarkError as error:
            protocol_error = protocol_error or str(error)
        try:
            self.assert_safe_control_surfaces(
                workspace, scan_workspace=not workspace_limit_violation
            )
        except BenchmarkError as error:
            protocol_error = protocol_error or str(error)
        raw_usage = _usage_sum(
            [record["usage"] for record in raw_responses.values()]
        )
        notification_usage = _usage_sum(
            [record["last_usage"] for record in cumulative_usage_notifications]
        )
        context_compaction_usage = _usage_sum(
            [
                record["usage"]
                for record in raw_responses.values()
                if record.get("usage_class") == "context_compaction"
            ]
        )
        raw_cumulative_cross_checked_usage = _usage_delta(
            raw_usage, context_compaction_usage
        )
        fork_notification_fallback = (
            self.fork_source_thread_id is not None
            and not raw_responses
            and bool(cumulative_usage_notifications)
            and context_compaction_item_count == 0
            and not any(
                item["received_after_turn_completed"]
                for item in cumulative_usage_notifications
            )
        )
        if raw_responses:
            usage = raw_usage
            cumulative_cross_checked_usage = raw_cumulative_cross_checked_usage
            usage_measurement_mode = "raw_response_events"
        elif fork_notification_fallback:
            usage = notification_usage
            cumulative_cross_checked_usage = notification_usage
            usage_measurement_mode = "fork_cumulative_notifications"
        else:
            usage = raw_usage
            cumulative_cross_checked_usage = raw_cumulative_cross_checked_usage
            usage_measurement_mode = "incomplete"
        cumulative_delta: dict[str, int] | None = None
        if latest_cumulative is not None:
            try:
                cumulative_delta = _usage_delta(latest_cumulative, baseline)
            except BenchmarkError as error:
                # App-server versions may report a fork's cumulative usage
                # either including the copied parent history or starting at
                # zero for the new child. Both are unambiguous when the first
                # child turn is cross-checked against exact response-level usage.
                if (
                    self.fork_source_thread_id is not None
                    and not reused_session
                    and latest_cumulative == cumulative_cross_checked_usage
                ):
                    cumulative_delta = dict(latest_cumulative)
                    fork_cumulative_usage_semantics = "child_reset"
                else:
                    protocol_error = protocol_error or str(error)
            else:
                if self.fork_source_thread_id is not None and not reused_session:
                    fork_cumulative_usage_semantics = "parent_inherited"
        usage_complete = False
        if terminal_status == "completed":
            if (
                not raw_responses
                and self.fork_source_thread_id is None
            ):
                telemetry_invalid = True
                protocol_error = protocol_error or (
                    "Codex app-server supplied no exact raw response usage"
                )
            elif not raw_responses and context_compaction_item_count:
                telemetry_invalid = True
                protocol_error = protocol_error or (
                    "Codex fork emitted a context compaction without exact raw usage"
                )
            elif not raw_responses and any(
                item["received_after_turn_completed"]
                for item in cumulative_usage_notifications
            ):
                telemetry_invalid = True
                protocol_error = protocol_error or (
                    "Codex fork emitted task usage only after turn completion"
                )
            elif not raw_responses and not cumulative_usage_notifications:
                telemetry_invalid = True
                protocol_error = protocol_error or (
                    "Codex fork supplied no exact cumulative response usage"
                )
            elif not raw_responses and not fork_notification_fallback:
                telemetry_invalid = True
                protocol_error = protocol_error or (
                    "Codex fork cumulative response usage was not admissible"
                )
            if cumulative_delta is None:
                telemetry_invalid = True
                protocol_error = protocol_error or (
                    "Codex app-server supplied no valid cumulative usage cross-check"
                )
            elif any(
                cumulative_delta[field] != cumulative_cross_checked_usage[field]
                for field in _zero_usage()
            ):
                telemetry_invalid = True
                protocol_error = protocol_error or (
                    "Codex response-level usage disagrees with the cumulative usage delta"
                )
            else:
                usage_complete = bool(raw_responses) or fork_notification_fallback

        current_network = monitor.checkpoint() if monitor is not None else network_before
        network_events = max(0, current_network - network_before)
        if self._live_session is not None:
            self._live_session.network_checkpoint = current_network
        process_unexpectedly_exited = process is None or (
            process.poll() is not None
            and (
                not ephemeral
                or process.returncode not in (0, -signal.SIGTERM)
            )
        )
        keep_session = (
            not ephemeral
            and self._live_session is not None
            and terminal_status == "completed"
            and protocol_error is None
            and not timed_out
            and not network_events
            and not process_unexpectedly_exited
        )
        if keep_session:
            try:
                self._sync_private_auth_to_storage()
            except (OSError, BenchmarkError) as error:
                protocol_error = protocol_error or (
                    f"could not persist refreshed Codex authentication: {error}"
                )
                keep_session = False
        if keep_session:
            assert observed_thread_id is not None and latest_cumulative is not None
            self._live_session.cumulative_usage = dict(latest_cumulative)
            self._store_usage_baseline(observed_thread_id, latest_cumulative)

        stderr_bytes = b""
        if not keep_session and process is not None:
            if self._live_session is not None:
                try:
                    stderr_bytes = stderr_capture.snapshot()
                    self._live_session.stderr_checkpoint = len(stderr_bytes)
                except OSError as error:
                    stderr_bytes = f"could not read stderr capture: {error}\n".encode(
                        "utf-8"
                    )
                    protocol_error = protocol_error or "could not read Codex stderr capture"
                try:
                    self.close(artifact_dir=artifact_dir / "session-close")
                except BenchmarkError as error:
                    protocol_error = protocol_error or str(error)
                if marker.is_file() and not marker.is_symlink():
                    network_events = max(network_events, max(0, marker.stat().st_size - network_before))
            else:
                shutdown = self._stop_process(process)
                try:
                    assert reader is not None
                    late_stdout = reader.drain_until_eof(2.0)
                    if late_stdout["line_count"]:
                        protocol_error = protocol_error or (
                            "Codex app-server emitted protocol messages after the final "
                            "telemetry boundary"
                        )
                except BenchmarkError as error:
                    protocol_error = protocol_error or str(error)
                finally:
                    if process.stdout is not None:
                        process.stdout.close()
                if not shutdown["graceful"]:
                    protocol_error = protocol_error or (
                        "Codex app-server did not exit cleanly "
                        f"(returncode={shutdown['returncode']}, "
                        f"forced={shutdown['forced_signal']})"
                    )
                if monitor is not None:
                    total_network = monitor.stop_and_seal()
                    network_events = max(network_events, max(0, total_network - network_before))
                try:
                    stderr_capture.finish()
                    stderr_bytes = stderr_capture.snapshot()
                except OSError as error:
                    stderr_bytes = f"could not read stderr capture: {error}\n".encode(
                        "utf-8"
                    )
                    protocol_error = protocol_error or "could not read Codex stderr capture"
                try:
                    stderr_capture.close()
                except OSError:
                    pass
        if staged_auth is not None:
            if process is not None:
                try:
                    self._sync_private_auth_to_storage()
                except (OSError, BenchmarkError) as error:
                    protocol_error = protocol_error or (
                        f"could not persist refreshed Codex authentication: {error}"
                    )
            try:
                self._remove_auth(staged_auth)
            except BenchmarkError as error:
                protocol_error = protocol_error or str(error)
            staged_auth = None
        elif keep_session and stderr_capture is not None:
            try:
                stderr_bytes = stderr_capture.snapshot()
                if self._live_session is not None:
                    self._live_session.stderr_checkpoint = len(stderr_bytes)
            except OSError as error:
                stderr_bytes = f"could not read stderr capture: {error}\n".encode("utf-8")
                protocol_error = protocol_error or "could not read Codex stderr capture"

        stderr_stream = (
            stderr_capture.metadata() if stderr_capture is not None else None
        )
        if isinstance(stderr_stream, Mapping) and stderr_stream.get("truncated") is True:
            artifact_limit_violation = True
            protocol_error = protocol_error or "Codex stderr archive ceiling exceeded"
        stderr_bytes, stderr_credential_redactions = self._redact_artifact_bytes(
            stderr_bytes
        )
        safe_message, message_credential_redactions = self._redact_artifact_bytes(
            final_message.encode("utf-8", errors="replace")
        )
        final_message = safe_message.decode("utf-8", errors="replace")
        if protocol_error is not None:
            safe_error, error_credential_redactions = self._redact_artifact_bytes(
                protocol_error.encode("utf-8", errors="replace")
            )
            protocol_error = safe_error.decode("utf-8", errors="replace")
        else:
            error_credential_redactions = 0

        attempt_marker = artifact_dir / "network_violations.bin"
        if attempt_marker != marker or not attempt_marker.exists():
            write_bytes_atomic(attempt_marker, b"!" * network_events, mode=0o400)
        else:
            os.chmod(attempt_marker, 0o400)
        event_archive.seal()
        write_bytes_atomic(artifact_dir / "stderr.log", stderr_bytes, mode=0o400)
        write_bytes_atomic(
            artifact_dir / "last_message.txt", final_message.encode("utf-8"), mode=0o400
        )

        if network_events:
            exit_code = NETWORK_VIOLATION_EXIT_CODE
        elif timed_out:
            exit_code = TIMEOUT_EXIT_CODE
        elif protocol_error is not None:
            exit_code = PROTOCOL_ERROR_EXIT_CODE
        elif process_unexpectedly_exited:
            exit_code = (
                process.returncode
                if process is not None and process.returncode not in (None, 0)
                else PROTOCOL_ERROR_EXIT_CODE
            )
        else:
            exit_code = 0
        result = TurnResult(
            thread_id=observed_thread_id,
            exit_code=exit_code,
            timed_out=timed_out,
            wall_seconds=(stopped - started) / 1_000_000_000,
            usage=usage,
            usage_complete=usage_complete,
            final_message=final_message,
            event_count=event_archive.count,
            command=command,
            active_started_perf_ns=active_started_perf_ns,
            active_ended_perf_ns=active_ended_perf_ns,
            failure_kind=(
                "provider_capability_violation"
                if capability_violation
                else "workspace_limit"
                if workspace_limit_violation
                else (
                    "artifact_limit"
                    if artifact_limit_violation
                    else (
                        "command_resource_limit"
                        if command_resource_violation
                        else ("telemetry_invalid" if telemetry_invalid else None)
                    )
                )
            ),
            thread_cumulative_usage=(
                dict(latest_cumulative) if latest_cumulative is not None else None
            ),
        )
        record: dict[str, Any] = {
            "schema_version": 3,
            "transport": "codex-app-server-stdio",
            "persistent_app_server_session": not ephemeral,
            "app_server_process_reused": reused_session,
            "started_at_utc": started_wall,
            "completed_at_utc": utc_now(),
            "thread_id": result.thread_id,
            "turn_id": observed_turn_id,
            "fork_provenance": (
                {
                    "source_thread_id": self.fork_source_thread_id,
                    "source_last_turn_id": self.fork_source_last_turn_id,
                    "source_cumulative_usage": self.fork_source_cumulative_usage,
                }
                if self.fork_source_thread_id is not None
                else None
            ),
            "terminal_status": terminal_status,
            "exit_code": result.exit_code,
            "timed_out": result.timed_out,
            "failure_kind": result.failure_kind,
            "wall_seconds": result.wall_seconds,
            "model_turn_seconds_to_terminal_boundary": (
                (terminal_event_perf_ns - active_started_perf_ns) / 1_000_000_000
                if active_started_perf_ns is not None and terminal_event_perf_ns is not None
                else None
            ),
            "active_seconds_through_quiescence": (
                (active_ended_perf_ns - active_started_perf_ns) / 1_000_000_000
                if active_started_perf_ns is not None and active_ended_perf_ns is not None
                else None
            ),
            "command": result.command,
            "app_server_command": inner,
            "usage": result.usage,
            "usage_complete": result.usage_complete,
            "usage_measurement": (
                "exact deduplicated app-server rawResponse/completed usage, including "
                "explicitly classified context-compaction responses"
                if usage_measurement_mode == "raw_response_events"
                else (
                    "exact fork-task thread/tokenUsage/updated last-response usage; "
                    "each response is identity-bound and equals its cumulative delta"
                    if usage_measurement_mode == "fork_cumulative_notifications"
                    else "incomplete provider telemetry"
                )
            ),
            "usage_measurement_mode": usage_measurement_mode,
            "capability_attestation": capability_attestation,
            "usage_field_semantics": {
                "cache_write_input_tokens": (
                    "Codex app-server TokenUsageBreakdown schema default 0 is applied "
                    "when cacheWriteInputTokens is omitted"
                ),
                "raw_responses_using_schema_default": sum(
                    1
                    for item in raw_responses.values()
                    if item.get("cache_write_input_tokens_defaulted") is True
                ),
                "cumulative_cross_check_using_schema_default": (
                    latest_cumulative_cache_write_defaulted
                ),
            },
            "raw_response_count": len(raw_responses),
            "raw_responses": [
                {"response_id": response_id, **raw_responses[response_id]}
                for response_id in sorted(raw_responses)
            ],
            "cumulative_usage_notification_count": len(
                cumulative_usage_notifications
            ),
            "cumulative_usage_notifications": cumulative_usage_notifications,
            "fork_notification_fallback_admitted": fork_notification_fallback,
            "cumulative_usage_delta_cross_check": cumulative_delta,
            "cumulative_usage_expected_from_raw_responses": (
                raw_cumulative_cross_checked_usage
            ),
            "cumulative_usage_expected_from_measurement": (
                cumulative_cross_checked_usage
            ),
            "thread_cumulative_usage_after_turn": result.thread_cumulative_usage,
            "context_compaction_usage": context_compaction_usage,
            "context_compaction_response_count": sum(
                1
                for item in raw_responses.values()
                if item.get("usage_class") == "context_compaction"
            ),
            "context_compaction_item_count": context_compaction_item_count,
            "fork_cumulative_usage_semantics": fork_cumulative_usage_semantics,
            "background_terminal_cleanup": background_terminal_cleanup,
            "workspace_resource_ceiling": {
                "maximum_entries": MAX_WORKSPACE_ENTRIES,
                "maximum_bytes": MAX_WORKSPACE_BYTES,
                "observed": workspace_usage,
                "violated": workspace_limit_violation,
                "excluded_from_contestant_measurement": False,
            },
            "generated_command_cgroup": {
                "before": command_resources_before,
                "after": command_resources_after,
                "limit_event_delta": command_resource_delta,
                "violated": command_resource_violation,
            },
            "post_terminal_telemetry_settle": post_terminal_telemetry_settle,
            "event_count": result.event_count,
            "event_archive_bytes": event_archive.bytes,
            "event_archive_limit_bytes": MAX_EVENT_TRACE_BYTES,
            "event_archive_limit_count": MAX_EVENT_TRACE_COUNT,
            "event_archive_violated": artifact_limit_violation,
            "event_trace_redactions": protocol_redactions,
            "credential_redactions_before_publication": (
                stderr_credential_redactions
                + message_credential_redactions
                + error_credential_redactions
            ),
            "event_trace_policy": (
                "Sanitized observable app-server events; encrypted/non-summary reasoning, "
                "system/developer, and authentication fields are removed before persistence."
            ),
            "prompt_sha256": sha256_file(prompt_path),
            "events_sha256": sha256_file(artifact_dir / "events.jsonl"),
            "stderr_sha256": sha256_file(artifact_dir / "stderr.log"),
            "stderr_scope": "app-server session prefix",
            "stderr_stream": stderr_stream,
            "last_message_sha256": sha256_file(artifact_dir / "last_message.txt"),
            "temporary_auth_removed_before_turn_start": False,
            "private_auth_retained_for_refresh": private_auth_ready_before_turn_start,
            "private_auth_runtime_tmpfs": self._private_runtime_is_tmpfs,
            "controlled_passwd_sha256": controlled_passwd_sha256,
            "network_marker_inotify_events": network_events,
            "network_violation_attempts": attempt_marker.stat().st_size,
            "network_violation_marker_sha256": sha256_file(attempt_marker),
            "protocol_error": protocol_error,
            "observable_reasoning_policy": (
                "Raw app-server JSONL retains API-exposed summaries and tool events only; "
                "hidden chain-of-thought is not requested or available."
            ),
        }
        write_json_atomic(artifact_dir / "turn.json", record, mode=0o400)
        return result
