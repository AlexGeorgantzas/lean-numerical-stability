from __future__ import annotations

import hashlib
import json
import os
import re
import stat
import tempfile
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable, Mapping


class BenchmarkError(RuntimeError):
    """Fail-closed benchmark control-plane error."""


# Only these host paths are visible in the Bubblewrap root.  In particular,
# /usr/local, /usr/src, /usr/share/doc, and the host home tree are absent.  The
# few /usr/share and /etc paths below are runtime data needed by the native
# client, TLS/DNS, Poppler, Python, or fontconfig.
SYSTEM_RUNTIME_DIRECTORIES = (
    Path("/usr/bin"),
    Path("/usr/lib"),
    Path("/usr/lib64"),
    Path("/usr/share/zoneinfo"),
    Path("/usr/share/fonts"),
    Path("/usr/share/fontconfig"),
    Path("/usr/share/poppler"),
    Path("/usr/share/mime"),
    Path("/lib"),
    Path("/lib64"),
    Path("/etc/ssl"),
    Path("/etc/ca-certificates"),
    Path("/etc/pki"),
    Path("/etc/fonts"),
    Path("/etc/ld.so.conf.d"),
)
SYSTEM_RUNTIME_FILES = (
    Path("/etc/resolv.conf"),
    Path("/etc/hosts"),
    Path("/etc/nsswitch.conf"),
    Path("/etc/gai.conf"),
    Path("/etc/services"),
    Path("/etc/protocols"),
    Path("/etc/localtime"),
    Path("/etc/timezone"),
    Path("/etc/ld.so.cache"),
    Path("/etc/ld.so.conf"),
)
TREATMENT_MARKERS = (
    b"numstability",
    b"highambench",
    b"lean-fp-analysis",
    b"lean-numerical-stability",
)


def minimal_system_mount_args() -> list[str]:
    """Return the shared, narrow host-runtime mounts for Bubblewrap."""

    arguments = ["--dir", "/usr", "--dir", "/usr/share", "--dir", "/etc"]
    for path in (*SYSTEM_RUNTIME_DIRECTORIES, *SYSTEM_RUNTIME_FILES):
        if path.exists():
            arguments.extend(["--ro-bind", str(path.resolve(strict=True)), str(path)])
    return arguments


def _regular_files_without_following(root: Path) -> Iterable[Path]:
    if root.is_file() and not root.is_symlink():
        yield root
        return
    if not root.is_dir() or root.is_symlink():
        return
    for directory, directory_names, file_names in os.walk(root, followlinks=False):
        directory_names.sort()
        file_names.sort()
        directory_path = Path(directory)
        for name in file_names:
            path = directory_path / name
            if path.is_file() and not path.is_symlink():
                yield path


def visible_system_runtime_manifest() -> dict[str, Any]:
    """Hash and treatment-scan every non-frozen host file exposed to condition N.

    The record is deliberately aggregate rather than a giant file listing.  A
    doctor recomputes it before every pair, so an OS update requires an explicit
    redeployment instead of silently changing the benchmark environment.
    """

    digest = hashlib.sha256()
    file_count = 0
    byte_count = 0
    mounted = [
        path
        for path in (*SYSTEM_RUNTIME_DIRECTORIES, *SYSTEM_RUNTIME_FILES)
        if path.exists()
    ]
    mount_records: list[dict[str, str]] = []

    def record_path(path: Path, identity: bytes) -> None:
        nonlocal file_count, byte_count
        metadata = path.lstat()
        lowered_identity = identity.lower()
        if any(marker in lowered_identity for marker in TREATMENT_MARKERS):
            raise BenchmarkError(
                f"treatment-related path is visible in the common system runtime: {path}"
            )
        if stat.S_ISLNK(metadata.st_mode):
            target = os.fsencode(os.readlink(path))
            if any(marker in target.lower() for marker in TREATMENT_MARKERS):
                raise BenchmarkError(
                    f"treatment-related symlink is visible in the common system runtime: {path}"
                )
            digest.update(
                b"symlink\0"
                + identity
                + b"\0"
                + str(metadata.st_mode).encode()
                + b"\0"
                + target
                + b"\0"
            )
            return
        if stat.S_ISDIR(metadata.st_mode):
            digest.update(
                b"directory\0"
                + identity
                + b"\0"
                + str(metadata.st_mode).encode()
                + b"\0"
            )
            return
        if not stat.S_ISREG(metadata.st_mode):
            raise BenchmarkError(f"unsupported file is visible in system runtime: {path}")
        file_digest = hashlib.sha256()
        carry = b""
        with path.open("rb") as stream:
            for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                file_digest.update(chunk)
                lowered = (carry + chunk).lower()
                if any(marker in lowered for marker in TREATMENT_MARKERS):
                    raise BenchmarkError(
                        "treatment-related bytes are visible in the common system "
                        f"runtime: {path}"
                    )
                carry = lowered[-64:]
                byte_count += len(chunk)
        digest.update(
            b"file\0"
            + identity
            + b"\0"
            + str(metadata.st_mode).encode()
            + b"\0"
            + str(metadata.st_size).encode()
            + b"\0"
            + file_digest.hexdigest().encode("ascii")
            + b"\0"
        )
        file_count += 1

    for mount in mounted:
        source = mount.resolve(strict=True)
        mount_label = str(mount).encode("utf-8")
        source_label = str(source).encode("utf-8")
        mount_records.append({"destination": str(mount), "source": str(source)})
        original = mount.lstat()
        digest.update(
            b"mount\0"
            + mount_label
            + b"\0"
            + source_label
            + b"\0"
            + str(original.st_mode).encode()
            + b"\0"
        )
        if stat.S_ISLNK(original.st_mode):
            digest.update(b"source-link\0" + os.fsencode(os.readlink(mount)) + b"\0")
        record_path(source, mount_label + b"\0.")
        if not source.is_dir():
            continue
        for directory, directory_names, file_names in os.walk(source, followlinks=False):
            directory_names.sort()
            file_names.sort()
            directory_path = Path(directory)
            retained_directories: list[str] = []
            for name in directory_names:
                path = directory_path / name
                relative = path.relative_to(source).as_posix().encode("utf-8")
                record_path(path, mount_label + b"\0" + relative)
                if not path.is_symlink():
                    retained_directories.append(name)
            directory_names[:] = retained_directories
            for name in file_names:
                path = directory_path / name
                relative = path.relative_to(source).as_posix().encode("utf-8")
                record_path(path, mount_label + b"\0" + relative)
    return {
        "schema_version": "formalization-visible-system-runtime-1",
        "mounts": mount_records,
        "file_count": file_count,
        "bytes": byte_count,
        "tree_sha256": digest.hexdigest(),
        "treatment_markers_absent": True,
    }


def treatment_free_runtime_manifest(roots: Mapping[str, Path]) -> dict[str, Any]:
    """Prove that N-visible frozen Lean/package roots contain no treatment marker."""

    marker = b"numstability"
    digest = hashlib.sha256()
    file_count = 0
    byte_count = 0
    for label, root in sorted(roots.items()):
        if not root.is_dir() or root.is_symlink():
            raise BenchmarkError(f"N-visible runtime root is missing or unsafe: {label}")
        # The snapshot may be built in a same-filesystem staging directory and
        # atomically published later, so bind content to its logical role rather
        # than to a transient absolute installer path.
        digest.update(label.encode("utf-8") + b"\0")
        for directory, directory_names, file_names in os.walk(root, followlinks=False):
            directory_names.sort()
            file_names.sort()
            directory_path = Path(directory)
            retained: list[str] = []
            for name in directory_names:
                path = directory_path / name
                relative = path.relative_to(root).as_posix().encode("utf-8")
                metadata = path.lstat()
                if marker in relative.lower():
                    raise BenchmarkError(
                        f"treatment-related path is visible to condition N in {label}"
                    )
                if stat.S_ISLNK(metadata.st_mode):
                    target = os.fsencode(os.readlink(path))
                    if marker in target.lower():
                        raise BenchmarkError(
                            f"treatment-related symlink is visible to condition N in {label}"
                        )
                    digest.update(b"link\0" + relative + b"\0" + target + b"\0")
                elif stat.S_ISDIR(metadata.st_mode):
                    retained.append(name)
                    digest.update(b"dir\0" + relative + b"\0")
                else:
                    raise BenchmarkError(f"special node in N-visible runtime root: {label}")
            directory_names[:] = retained
            for name in file_names:
                path = directory_path / name
                relative = path.relative_to(root).as_posix().encode("utf-8")
                metadata = path.lstat()
                if marker in relative.lower():
                    raise BenchmarkError(
                        f"treatment-related path is visible to condition N in {label}"
                    )
                if stat.S_ISLNK(metadata.st_mode):
                    target = os.fsencode(os.readlink(path))
                    if marker in target.lower():
                        raise BenchmarkError(
                            f"treatment-related symlink is visible to condition N in {label}"
                        )
                    digest.update(b"link\0" + relative + b"\0" + target + b"\0")
                    continue
                if not stat.S_ISREG(metadata.st_mode):
                    raise BenchmarkError(f"special node in N-visible runtime root: {label}")
                file_digest = hashlib.sha256()
                carry = b""
                with path.open("rb") as stream:
                    for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                        file_digest.update(chunk)
                        lowered = (carry + chunk).lower()
                        if marker in lowered:
                            raise BenchmarkError(
                                f"treatment-related bytes are visible to condition N in {label}"
                            )
                        carry = lowered[-(len(marker) - 1) :]
                        byte_count += len(chunk)
                digest.update(
                    b"file\0"
                    + relative
                    + b"\0"
                    + str(metadata.st_size).encode()
                    + b"\0"
                    + file_digest.hexdigest().encode("ascii")
                    + b"\0"
                )
                file_count += 1
    return {
        "schema_version": "formalization-condition-n-runtime-absence-1",
        "roots": sorted(roots),
        "marker": "NumStability (case-insensitive path/content)",
        "file_count": file_count,
        "bytes_scanned": byte_count,
        "scan_sha256": digest.hexdigest(),
        "treatment_absent": True,
    }


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def credential_needles(auth_file: Path) -> set[bytes]:
    if not auth_file.is_file() or auth_file.is_symlink():
        raise BenchmarkError("Codex authentication source is missing or unsafe")
    payload = auth_file.read_bytes()
    needles: set[bytes] = set()
    stripped = payload.strip()
    if len(stripped) >= 16:
        needles.add(stripped)
    if len(payload) >= 16:
        needles.add(payload)

    try:
        parsed = json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError):
        parsed = None
    sensitive_key = re.compile(
        r"(?:auth|bearer|cookie|credential|password|secret|session|token)",
        re.IGNORECASE,
    )

    def collect(value: Any, key: str = "") -> None:
        if isinstance(value, Mapping):
            for child_key, child in value.items():
                collect(child, str(child_key))
        elif isinstance(value, list):
            for child in value:
                collect(child, key)
        elif isinstance(value, str) and sensitive_key.search(key):
            encoded = value.encode("utf-8")
            if len(encoded) >= 8:
                needles.add(encoded)

    collect(parsed)
    if not needles:
        raise BenchmarkError("Codex authentication source contains no scannable secret")
    return needles


def redact_credentials(payload: bytes, needles: Iterable[bytes]) -> tuple[bytes, int]:
    """Remove deployed credential byte strings before artifact publication."""

    redacted = payload
    replacements = 0
    for needle in sorted(set(needles), key=len, reverse=True):
        occurrences = redacted.count(needle)
        if occurrences:
            redacted = redacted.replace(needle, b"[REDACTED_CREDENTIAL]")
            replacements += occurrences
    return redacted, replacements


def assert_no_credentials_in_bytes(
    payloads: Iterable[tuple[str, bytes]], auth_file: Path
) -> dict[str, Any]:
    """Check not-yet-written terminal payloads against deployed credentials."""

    needles = credential_needles(auth_file)
    bytes_scanned = 0
    payloads_scanned = 0
    for label, payload in payloads:
        payloads_scanned += 1
        bytes_scanned += len(payload)
        if any(needle in payload for needle in needles):
            raise BenchmarkError(
                f"credential material detected in prospective result artifact: {label}"
            )
    return {
        "schema_version": "formalization-credential-payload-scan-1",
        "passed": True,
        "payloads_scanned": payloads_scanned,
        "bytes_scanned": bytes_scanned,
        "secret_patterns_scanned": len(needles),
    }


def assert_no_credentials_in_tree(
    root: Path,
    auth_file: Path,
    *,
    maximum_entries: int = 100_000,
    maximum_bytes: int = 4 * 1024 * 1024 * 1024,
) -> dict[str, Any]:
    """Fail closed if an archived result contains the deployed Codex secret.

    The scan looks for the complete auth payload and for values stored under
    credential-like JSON keys. It deliberately reports only artifact paths and
    counts, never the matched bytes or a credential fingerprint.
    """

    if not root.is_dir() or root.is_symlink():
        raise BenchmarkError(f"result closure is missing or unsafe: {root}")
    needles = credential_needles(auth_file)

    if maximum_entries < 1 or maximum_bytes < 1:
        raise BenchmarkError("credential-scan limits must be positive")
    maximum_needle = max(len(needle) for needle in needles)
    entries_scanned = 0
    files_scanned = 0
    bytes_scanned = 0
    pending = [root]
    while pending:
        directory_path = pending.pop()
        try:
            children = os.scandir(directory_path)
        except OSError as error:
            raise BenchmarkError(f"cannot enumerate result closure: {error}") from error
        try:
            with children:
                for child in children:
                    entries_scanned += 1
                    if entries_scanned > maximum_entries:
                        raise BenchmarkError(
                            f"result closure entry ceiling exceeded ({maximum_entries})"
                        )
                    path = Path(child.path)
                    relative = path.relative_to(root)
                    try:
                        metadata = child.stat(follow_symlinks=False)
                    except OSError as error:
                        raise BenchmarkError(
                            f"cannot inspect result artifact: {relative}"
                        ) from error
                    if stat.S_ISLNK(metadata.st_mode):
                        raise BenchmarkError(
                            f"result closure contains a symlink: {relative}"
                        )
                    if stat.S_ISDIR(metadata.st_mode):
                        pending.append(path)
                        continue
                    if not stat.S_ISREG(metadata.st_mode):
                        raise BenchmarkError(
                            f"result closure contains a special file: {relative}"
                        )
                    if bytes_scanned + metadata.st_size > maximum_bytes:
                        raise BenchmarkError(
                            f"result closure byte ceiling exceeded ({maximum_bytes})"
                        )
                    files_scanned += 1
                    carry = b""
                    try:
                        stream = path.open("rb")
                    except OSError as error:
                        raise BenchmarkError(
                            f"cannot read result artifact: {relative}"
                        ) from error
                    with stream:
                        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
                            bytes_scanned += len(chunk)
                            if bytes_scanned > maximum_bytes:
                                raise BenchmarkError(
                                    f"result closure byte ceiling exceeded ({maximum_bytes})"
                                )
                            window = carry + chunk
                            if any(needle in window for needle in needles):
                                raise BenchmarkError(
                                    "credential material detected in result artifact: "
                                    f"{relative}"
                                )
                            carry = window[-max(0, maximum_needle - 1) :]
        except OSError as error:
            raise BenchmarkError(f"cannot enumerate result closure: {error}") from error
    return {
        "schema_version": "formalization-credential-scan-1",
        "passed": True,
        "entries_scanned": entries_scanned,
        "files_scanned": files_scanned,
        "bytes_scanned": bytes_scanned,
        "maximum_entries": maximum_entries,
        "maximum_bytes": maximum_bytes,
        "secret_patterns_scanned": len(needles),
    }


def tree_manifest(root: Path) -> dict[str, Any]:
    """Hash every directory, regular file, and contained symlink in a frozen tree."""

    if not root.is_dir() or root.is_symlink():
        raise BenchmarkError(f"snapshot root is missing or unsafe: {root}")
    entries: list[dict[str, Any]] = [
        {"relative_path": ".", "kind": "directory", "mode": root.lstat().st_mode}
    ]
    resolved_root = root.resolve()
    for path in sorted(root.rglob("*"), key=lambda item: item.relative_to(root).as_posix()):
        relative = path.relative_to(root).as_posix()
        metadata = path.lstat()
        if path.is_symlink():
            target = os.readlink(path)
            resolved = path.resolve()
            try:
                resolved.relative_to(resolved_root)
            except ValueError as error:
                raise BenchmarkError(f"snapshot symlink escapes its root: {relative}") from error
            entries.append(
                {
                    "relative_path": relative,
                    "kind": "symlink",
                    "mode": metadata.st_mode,
                    "target": target,
                }
            )
        elif stat.S_ISDIR(metadata.st_mode):
            entries.append(
                {"relative_path": relative, "kind": "directory", "mode": metadata.st_mode}
            )
        elif stat.S_ISREG(metadata.st_mode):
            entries.append(
                {
                    "relative_path": relative,
                    "kind": "file",
                    "mode": metadata.st_mode,
                    "sha256": sha256_file(path),
                    "bytes": metadata.st_size,
                }
            )
        else:
            raise BenchmarkError(f"snapshot contains unsupported special file: {relative}")
    payload = json.dumps(entries, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return {"entries": entries, "tree_sha256": sha256_bytes(payload)}


def file_tree_fingerprint(root: Path, *, suffix: str | None = None) -> dict[str, Any]:
    """Return a compact, content-only fingerprint of regular files in a tree.

    ``tree_manifest`` remains the canonical frozen-tree record.  This compact
    form is useful when the same bytes are copied into a read-only deployment:
    it deliberately ignores permission changes while authenticating every
    selected relative path, size, and file digest.  Symlinks matching the
    requested suffix are rejected instead of being silently omitted.
    """

    manifest = tree_manifest(root)
    selected: list[dict[str, Any]] = []
    for entry in manifest["entries"]:
        relative = entry["relative_path"]
        matches = suffix is None or relative.endswith(suffix)
        if entry["kind"] == "symlink" and matches:
            raise BenchmarkError(
                f"fingerprinted tree contains a selected symlink: {relative}"
            )
        if entry["kind"] != "file" or not matches:
            continue
        selected.append(
            {
                "relative_path": relative,
                "bytes": entry["bytes"],
                "sha256": entry["sha256"],
            }
        )
    payload = json.dumps(selected, sort_keys=True, separators=(",", ":")).encode(
        "utf-8"
    )
    return {
        "file_count": len(selected),
        "bytes": sum(int(entry["bytes"]) for entry in selected),
        "tree_sha256": sha256_bytes(payload),
    }


def bounded_tree_usage(
    root: Path, *, maximum_entries: int, maximum_bytes: int
) -> dict[str, int]:
    """Measure a tree while stopping before an oversized tree can make sealing unbounded."""

    if maximum_entries < 1 or maximum_bytes < 1:
        raise BenchmarkError("workspace limits must be positive")
    if not root.is_dir() or root.is_symlink():
        raise BenchmarkError(f"workspace root is missing or unsafe: {root}")
    entries = 0
    total_bytes = 0
    pending = [root]
    while pending:
        directory = pending.pop()
        try:
            children = os.scandir(directory)
        except OSError as error:
            raise BenchmarkError(f"cannot enumerate workspace: {error}") from error
        try:
            with children:
                for child in children:
                    entries += 1
                    if entries > maximum_entries:
                        raise BenchmarkError(
                            f"workspace entry ceiling exceeded ({maximum_entries})"
                        )
                    try:
                        metadata = child.stat(follow_symlinks=False)
                    except OSError as error:
                        raise BenchmarkError(
                            f"cannot inspect workspace entry: {error}"
                        ) from error
                    if stat.S_ISLNK(metadata.st_mode):
                        raise BenchmarkError(
                            f"workspace contains a symlink: {child.path}"
                        )
                    if stat.S_ISDIR(metadata.st_mode):
                        if metadata.st_mode & (stat.S_IRUSR | stat.S_IXUSR) != (
                            stat.S_IRUSR | stat.S_IXUSR
                        ):
                            raise BenchmarkError(
                                "workspace contains an unreadable directory"
                            )
                        pending.append(Path(child.path))
                    elif stat.S_ISREG(metadata.st_mode):
                        if not metadata.st_mode & stat.S_IRUSR:
                            raise BenchmarkError("workspace contains an unreadable file")
                        total_bytes += metadata.st_size
                        if total_bytes > maximum_bytes:
                            raise BenchmarkError(
                                f"workspace byte ceiling exceeded ({maximum_bytes})"
                            )
                    else:
                        raise BenchmarkError(
                            f"workspace contains a special file: {child.path}"
                        )
        except OSError as error:
            raise BenchmarkError(f"cannot enumerate workspace: {error}") from error
    return {"entries": entries, "bytes": total_bytes}


def verify_tree_manifest(root: Path, record: Any, *, label: str) -> None:
    if not isinstance(record, dict):
        raise BenchmarkError(f"{label} snapshot record is malformed")
    actual = tree_manifest(root)
    if actual != record:
        raise BenchmarkError(f"{label} snapshot tree mismatch")


def load_json(path: Path) -> dict[str, Any]:
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise BenchmarkError(f"cannot read JSON {path}: {error}") from error
    if not isinstance(value, dict):
        raise BenchmarkError(f"expected a JSON object in {path}")
    return value


def write_bytes_atomic(path: Path, payload: bytes, *, mode: int = 0o600) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        os.fchmod(descriptor, mode)
        offset = 0
        while offset < len(payload):
            written = os.write(descriptor, payload[offset:])
            if written <= 0:
                raise BenchmarkError(f"short write for {path}")
            offset += written
        os.fsync(descriptor)
        os.close(descriptor)
        descriptor = -1
        os.replace(temporary, path)
        os.chmod(path, mode, follow_symlinks=False)
        directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if descriptor >= 0:
            os.close(descriptor)
        temporary.unlink(missing_ok=True)


def write_json_atomic(path: Path, value: Any, *, mode: int = 0o600) -> None:
    write_bytes_atomic(path, canonical_json_bytes(value), mode=mode)


def append_jsonl(path: Path, value: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_WRONLY | os.O_APPEND | os.O_CREAT | os.O_CLOEXEC
    descriptor = os.open(path, flags, 0o600)
    try:
        payload = canonical_json_bytes(dict(value))
        offset = 0
        while offset < len(payload):
            offset += os.write(descriptor, payload[offset:])
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def stable_regular_bytes(path: Path, *, maximum_bytes: int = 8 * 1024 * 1024) -> bytes:
    """Read a non-symlink regular file twice and require a stable inode snapshot."""

    metadata = path.lstat()
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
        raise BenchmarkError(f"candidate is not a regular non-symlink file: {path}")
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags)
    try:
        before = os.fstat(descriptor)
        if before.st_size > maximum_bytes:
            raise BenchmarkError(f"candidate exceeds {maximum_bytes} bytes")
        first = b""
        while len(first) < before.st_size + 1:
            chunk = os.read(descriptor, min(65536, before.st_size + 1 - len(first)))
            if not chunk:
                break
            first += chunk
        middle = os.fstat(descriptor)
        os.lseek(descriptor, 0, os.SEEK_SET)
        second = b""
        while len(second) < len(first) + 1:
            chunk = os.read(descriptor, min(65536, len(first) + 1 - len(second)))
            if not chunk:
                break
            second += chunk
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    fields = ("st_dev", "st_ino", "st_mode", "st_size", "st_mtime_ns", "st_ctime_ns")
    if any(
        getattr(before, field) != getattr(middle, field)
        or getattr(before, field) != getattr(after, field)
        for field in fields
    ) or first != second:
        raise BenchmarkError(f"candidate changed while being frozen: {path}")
    return first


def freeze_candidate(
    source: Path, destination: Path, *, auth_file: Path | None = None
) -> dict[str, Any]:
    payload = stable_regular_bytes(source)
    if auth_file is not None:
        assert_no_credentials_in_bytes([("Candidate.lean", payload)], auth_file)
    write_bytes_atomic(destination, payload, mode=0o400)
    digest = sha256_bytes(payload)
    if sha256_file(destination) != digest:
        raise BenchmarkError("frozen candidate hash verification failed")
    try:
        text = payload.decode("utf-8")
    except UnicodeDecodeError as error:
        raise BenchmarkError("Candidate.lean is not UTF-8") from error
    return {
        "path": str(destination),
        "sha256": digest,
        "bytes": len(payload),
        "lines": len(text.splitlines()),
    }


_PROVENANCE_PATTERNS = (
    re.compile(r"NumStability(?:\.[A-Za-z0-9_']+)*", re.IGNORECASE),
    re.compile(r"[A-Za-z0-9_./-]+\.lean\b"),
    re.compile(r"\b[A-Z][A-Za-z0-9_']*(?:\.[A-Za-z0-9_']+)+\b"),
    re.compile(r"\b(?:TARGET|LOCAL|D|M)[0-9]*\b", re.IGNORECASE),
    re.compile(
        r"\b(?:theorem|lemma|def|abbrev|structure|class|instance|namespace|end|"
        r"import|open|axiom|constant|opaque|unsafe|partial|extern|by|exact|"
        r"apply|intro|simp|simpa|rw|rfl|constructor|fun)\b",
        re.IGNORECASE,
    ),
    re.compile(r":=|=>|@[\[(]|#(?:check|eval|print|reduce|synth|guard)\b"),
    re.compile(r"\b(?:condition\s+[NL]|[NL]\s+condition)\b", re.IGNORECASE),
    re.compile(r"\b(?:attempt|submission|retry|try|rep(?:etition)?)\s*[-#:]?\s*\d+\b", re.IGNORECASE),
    re.compile(r"\b[a-z][A-Za-z0-9']*_[A-Za-z0-9_']+\b"),
    re.compile(r"\b[a-z][a-z0-9']*(?:[A-Z][A-Za-z0-9']*)+\b"),
)


_DECLARATION_PATTERN = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|"
    r"structure|class|inductive|opaque|instance)\s+([A-Za-z_][A-Za-z0-9_']*)",
    re.MULTILINE,
)


def discover_lean_declaration_names(*roots: Path) -> set[str]:
    """Discover names whose appearance would reveal the frozen treatment library."""

    names: set[str] = set()
    for root in roots:
        paths = [root] if root.is_file() else sorted(root.rglob("*.lean"))
        for path in paths:
            if not path.is_file() or path.is_symlink():
                continue
            try:
                source = path.read_text(encoding="utf-8")
            except (OSError, UnicodeDecodeError) as error:
                raise BenchmarkError(f"cannot inspect Lean declaration names in {path}") from error
            names.update(match.group(1) for match in _DECLARATION_PATTERN.finditer(source))
    return names


def neutralize_feedback_text(
    value: str, *, forbidden_identifiers: Iterable[str] = ()
) -> str:
    """Remove code/provenance tokens from auditor-authored repair prose."""

    rendered = value.replace("```", "").replace("`", "")
    identifiers = sorted(
        {
            identifier
            for identifier in forbidden_identifiers
            if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", identifier)
        },
        key=len,
        reverse=True,
    )
    for identifier in identifiers:
        rendered = re.sub(
            rf"(?<![A-Za-z0-9_']){re.escape(identifier)}(?![A-Za-z0-9_'])",
            "[redacted identifier]",
            rendered,
            flags=re.IGNORECASE,
        )
    for pattern in _PROVENANCE_PATTERNS:
        rendered = pattern.sub("[redacted identifier]", rendered)
    rendered = re.sub(r"\s+", " ", rendered).strip()
    if not rendered:
        return "The submitted proposition does not yet encode this requirement."
    return rendered[:2000]


def make_repair_feedback(
    mismatches: list[Mapping[str, Any]], *, forbidden_identifiers: Iterable[str] = ()
) -> dict[str, Any]:
    issues: list[dict[str, str]] = []
    for item in mismatches[:8]:
        requirement = neutralize_feedback_text(
            str(item.get("paper_requirement", "")),
            forbidden_identifiers=forbidden_identifiers,
        )
        mismatch = neutralize_feedback_text(
            str(item.get("candidate_mismatch", "")),
            forbidden_identifiers=forbidden_identifiers,
        )
        issues.append(
            {
                "missing_paper_requirement": requirement,
                "candidate_mismatch": mismatch,
            }
        )
    if not issues:
        issues.append(
            {
                "missing_paper_requirement": (
                    "The paper's complete selected result must be represented without "
                    "unresolved semantic uncertainty."
                ),
                "candidate_mismatch": (
                    "The audit could not establish that the submitted proposition is "
                    "faithful to every material part of the selected result."
                ),
            }
        )
    return {"status": "repair-required", "issues": issues}
