#!/usr/bin/env python3
"""Manage one fail-closed writer lease for a paper-local T4 workspace.

The lease is coordination metadata, not authorization to change benchmark
semantics.  It prevents two cooperating extraction sessions from writing the
same paper concurrently while allowing distinct paper IDs to proceed in
parallel.  Lease records store only a SHA-256 digest of the bearer token.  The
CLI transfers generated credentials through an owner-only ephemeral file and
never prints the bearer token.
"""

from __future__ import annotations

import argparse
from contextlib import contextmanager
import fcntl
import hashlib
import json
import os
from pathlib import Path
import secrets
import stat
import sys
import time
from typing import Any, Iterator, Mapping, Sequence
import uuid

try:
    from .common import BenchmarkToolError
except ImportError:  # Direct script execution.
    from common import BenchmarkToolError  # type: ignore


SCHEMA_VERSION = "highambench-t4-writer-lease-0.1"
KIND = "highambench-t4-writer-lease"
ACTIONS = ("claim", "check", "renew", "release")
DEFAULT_TTL_SECONDS = 3600
MIN_TTL_SECONDS = 1
MAX_TTL_SECONDS = 7 * 24 * 60 * 60
LEASE_FILENAME = "writer_lease.json"
LOCK_FILENAME = ".writer_lease.lock"
HISTORY_DIRECTORY = "writer_lease_history"
CREDENTIAL_SCHEMA_VERSION = "highambench-t4-writer-lease-credential-0.1"
CREDENTIAL_KIND = "highambench-t4-writer-lease-credential"
CREDENTIAL_MAX_BYTES = 4096


def _canonical_json_bytes(value: Mapping[str, Any]) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _validate_paper_id(paper_id: str) -> None:
    if len(paper_id) != 3 or paper_id[0] != "P" or not paper_id[1:].isdigit():
        raise BenchmarkToolError(
            f"paper id must have canonical P0X form (for example P06): {paper_id!r}"
        )


def _canonical_invocation_id(value: str) -> str:
    try:
        parsed = uuid.UUID(value)
    except (ValueError, AttributeError) as error:
        raise BenchmarkToolError(f"invalid invocation UUID: {value!r}") from error
    canonical = str(parsed)
    if value.lower() != canonical:
        raise BenchmarkToolError(
            f"invocation UUID must use canonical lowercase form: {value!r}"
        )
    return canonical


def _validate_token(token: str) -> str:
    if not isinstance(token, str) or not (20 <= len(token) <= 256):
        raise BenchmarkToolError("lease token must contain 20 to 256 characters")
    if any(character.isspace() for character in token):
        raise BenchmarkToolError("lease token may not contain whitespace")
    return token


def _token_digest(token: str) -> str:
    return hashlib.sha256(_validate_token(token).encode("utf-8")).hexdigest()


def _validate_ttl(ttl_seconds: int) -> int:
    if isinstance(ttl_seconds, bool) or not isinstance(ttl_seconds, int):
        raise BenchmarkToolError("lease TTL must be an integer number of seconds")
    if not MIN_TTL_SECONDS <= ttl_seconds <= MAX_TTL_SECONDS:
        raise BenchmarkToolError(
            f"lease TTL must be between {MIN_TTL_SECONDS} and {MAX_TTL_SECONDS} seconds"
        )
    return ttl_seconds


def _secure_credential_parent(path: Path) -> Path:
    if not path.is_absolute():
        raise BenchmarkToolError("lease credential file path must be absolute")
    parent = path.parent
    try:
        metadata = parent.lstat()
    except FileNotFoundError as error:
        raise BenchmarkToolError(
            f"lease credential directory is missing: {parent}"
        ) from error
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
        raise BenchmarkToolError(
            f"lease credential directory must be a non-symlink directory: {parent}"
        )
    if parent.resolve() != parent:
        raise BenchmarkToolError(
            f"lease credential directory path must be canonical: {parent}"
        )
    if metadata.st_uid != os.geteuid() or stat.S_IMODE(metadata.st_mode) & 0o077:
        raise BenchmarkToolError(
            "lease credential directory must be owned by the current user and "
            f"have no group/other permissions: {parent}"
        )
    return parent


def _credential_payload(
    scratch_root: Path, paper_id: str, invocation_id: str, token: str
) -> dict[str, str]:
    _validate_paper_id(paper_id)
    return {
        "schema_version": CREDENTIAL_SCHEMA_VERSION,
        "kind": CREDENTIAL_KIND,
        "scratch_root": str(_secure_root(scratch_root)),
        "paper_id": paper_id,
        "invocation_id": _canonical_invocation_id(invocation_id),
        "token": _validate_token(token),
    }


def write_lease_credentials(
    path: Path,
    scratch_root: Path,
    paper_id: str,
    invocation_id: str,
    token: str,
) -> tuple[int, int]:
    """Create one owner-only credential file without overwriting any path."""

    parent = _secure_credential_parent(path)
    if path.exists() or path.is_symlink():
        raise BenchmarkToolError(
            f"lease credential file already exists; refusing overwrite: {path}"
        )
    payload = _canonical_json_bytes(
        _credential_payload(scratch_root, paper_id, invocation_id, token)
    )
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags, 0o600)
    except OSError as error:
        raise BenchmarkToolError(
            f"cannot safely create lease credential file {path}: {error}"
        ) from error
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        metadata = path.stat(follow_symlinks=False)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_uid != os.geteuid()
            or stat.S_IMODE(metadata.st_mode) != 0o600
        ):
            raise BenchmarkToolError(
                f"lease credential file permissions are unsafe: {path}"
            )
        _fsync_directory(parent)
        return metadata.st_dev, metadata.st_ino
    except BaseException:
        if path.exists() and not path.is_symlink():
            path.unlink()
        raise


def read_lease_credentials(
    path: Path, scratch_root: Path, paper_id: str
) -> tuple[str, str]:
    """Read and validate an owner-only credential file without following links."""

    _secure_credential_parent(path)
    flags = os.O_RDONLY
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags)
    except OSError as error:
        raise BenchmarkToolError(
            f"cannot safely open lease credential file {path}: {error}"
        ) from error
    try:
        metadata = os.fstat(descriptor)
        if (
            not stat.S_ISREG(metadata.st_mode)
            or metadata.st_uid != os.geteuid()
            or stat.S_IMODE(metadata.st_mode) != 0o600
            or metadata.st_size > CREDENTIAL_MAX_BYTES
        ):
            raise BenchmarkToolError(
                f"lease credential file permissions or size are unsafe: {path}"
            )
        with os.fdopen(descriptor, "rb", closefd=False) as stream:
            raw = stream.read(CREDENTIAL_MAX_BYTES + 1)
    finally:
        os.close(descriptor)
    value = _strict_json_object(raw, "lease credential file")
    expected_keys = {
        "schema_version",
        "kind",
        "scratch_root",
        "paper_id",
        "invocation_id",
        "token",
    }
    if set(value) != expected_keys:
        raise BenchmarkToolError("lease credential file has an unexpected field set")
    if (
        value.get("schema_version") != CREDENTIAL_SCHEMA_VERSION
        or value.get("kind") != CREDENTIAL_KIND
    ):
        raise BenchmarkToolError("lease credential file schema/kind is invalid")
    if value.get("scratch_root") != str(_secure_root(scratch_root)):
        raise BenchmarkToolError(
            "lease credential file belongs to another scratch root"
        )
    if value.get("paper_id") != paper_id:
        raise BenchmarkToolError("lease credential file belongs to another paper")
    invocation_id = value.get("invocation_id")
    token = value.get("token")
    if not isinstance(invocation_id, str) or not isinstance(token, str):
        raise BenchmarkToolError("lease credential file credentials are invalid")
    return _canonical_invocation_id(invocation_id), _validate_token(token)


def remove_lease_credentials(
    path: Path,
    scratch_root: Path,
    paper_id: str,
    invocation_id: str,
    token: str,
) -> None:
    """Remove the exact credential file after a successful terminal release."""

    observed_id, observed_token = read_lease_credentials(
        path, scratch_root, paper_id
    )
    if observed_id != _canonical_invocation_id(
        invocation_id
    ) or not secrets.compare_digest(observed_token, _validate_token(token)):
        raise BenchmarkToolError("lease credential file changed before removal")
    parent = path.parent
    path.unlink()
    _fsync_directory(parent)


def _secure_root(path: Path) -> Path:
    if path.is_symlink() or not path.is_dir():
        raise BenchmarkToolError(f"scratch root must be a non-symlink directory: {path}")
    return path.resolve()


def _secure_child_directory(parent: Path, name: str, *, create: bool) -> Path:
    child = parent / name
    if create:
        try:
            child.mkdir(mode=0o700)
        except FileExistsError:
            pass
    try:
        metadata = child.lstat()
    except FileNotFoundError as error:
        raise BenchmarkToolError(f"lease directory is missing: {child}") from error
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISDIR(metadata.st_mode):
        raise BenchmarkToolError(f"lease directory must be a non-symlink directory: {child}")
    return child


def _lease_directory(scratch_root: Path, paper_id: str, *, create: bool) -> Path:
    _validate_paper_id(paper_id)
    root = _secure_root(scratch_root)
    faithfulness = _secure_child_directory(
        root, "t4_source_faithfulness", create=create
    )
    paper = _secure_child_directory(faithfulness, paper_id, create=create)
    try:
        paper.resolve().relative_to(root)
    except ValueError as error:
        raise BenchmarkToolError(f"paper lease directory escapes scratch root: {paper}") from error
    return paper


def _existing_lease_directory(
    scratch_root: Path, paper_id: str
) -> tuple[Path, Path | None]:
    """Locate a lease directory without creating any coordination state."""

    _validate_paper_id(paper_id)
    root = _secure_root(scratch_root)
    faithfulness_path = root / "t4_source_faithfulness"
    try:
        faithfulness_metadata = faithfulness_path.lstat()
    except FileNotFoundError:
        return root, None
    if stat.S_ISLNK(faithfulness_metadata.st_mode) or not stat.S_ISDIR(
        faithfulness_metadata.st_mode
    ):
        raise BenchmarkToolError(
            "lease directory must be a non-symlink directory: "
            f"{faithfulness_path}"
        )

    paper_path = faithfulness_path / paper_id
    try:
        paper_metadata = paper_path.lstat()
    except FileNotFoundError:
        return root, None
    if stat.S_ISLNK(paper_metadata.st_mode) or not stat.S_ISDIR(
        paper_metadata.st_mode
    ):
        raise BenchmarkToolError(
            f"lease directory must be a non-symlink directory: {paper_path}"
        )
    try:
        paper_path.resolve().relative_to(root)
    except ValueError as error:
        raise BenchmarkToolError(
            f"paper lease directory escapes scratch root: {paper_path}"
        ) from error
    return root, paper_path


def _open_lock(directory: Path) -> int:
    path = directory / LOCK_FILENAME
    flags = os.O_RDWR | os.O_CREAT
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags, 0o600)
    except OSError as error:
        raise BenchmarkToolError(f"cannot safely open writer-lease lock {path}: {error}") from error
    metadata = os.fstat(descriptor)
    if not stat.S_ISREG(metadata.st_mode):
        os.close(descriptor)
        raise BenchmarkToolError(f"writer-lease lock is not a regular file: {path}")
    return descriptor


@contextmanager
def _locked_directory(directory: Path) -> Iterator[None]:
    descriptor = _open_lock(directory)
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        yield
    finally:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)


def _strict_json_object(raw: bytes, label: str) -> Mapping[str, Any]:
    def unique_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise BenchmarkToolError(f"{label} contains duplicate key {key!r}")
            result[key] = value
        return result

    try:
        value = json.loads(raw.decode("utf-8"), object_pairs_hook=unique_pairs)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise BenchmarkToolError(f"cannot parse {label}: {error}") from error
    if not isinstance(value, Mapping):
        raise BenchmarkToolError(f"{label} must be a JSON object")
    return value


def _validate_lease(value: Mapping[str, Any], paper_id: str) -> dict[str, Any]:
    expected_keys = {
        "schema_version",
        "kind",
        "paper_id",
        "invocation_id",
        "token_sha256",
        "generation",
        "claimed_at_unix",
        "renewed_at_unix",
        "expires_at_unix",
        "ttl_seconds",
        "previous_lease_sha256",
    }
    if set(value) != expected_keys:
        raise BenchmarkToolError("writer lease has an unexpected field set")
    if value.get("schema_version") != SCHEMA_VERSION or value.get("kind") != KIND:
        raise BenchmarkToolError("writer lease schema/kind is invalid")
    if value.get("paper_id") != paper_id:
        raise BenchmarkToolError("writer lease belongs to another paper")
    invocation_id = value.get("invocation_id")
    if not isinstance(invocation_id, str):
        raise BenchmarkToolError("writer lease invocation_id is invalid")
    _canonical_invocation_id(invocation_id)
    digest = value.get("token_sha256")
    if not isinstance(digest, str) or len(digest) != 64:
        raise BenchmarkToolError("writer lease token digest is invalid")
    try:
        int(digest, 16)
    except ValueError as error:
        raise BenchmarkToolError("writer lease token digest is invalid") from error
    for field in (
        "generation",
        "claimed_at_unix",
        "renewed_at_unix",
        "expires_at_unix",
        "ttl_seconds",
    ):
        item = value.get(field)
        if isinstance(item, bool) or not isinstance(item, int):
            raise BenchmarkToolError(f"writer lease {field} is invalid")
    if value["generation"] < 1:
        raise BenchmarkToolError("writer lease generation must be positive")
    _validate_ttl(value["ttl_seconds"])
    if not (
        value["claimed_at_unix"] <= value["renewed_at_unix"]
        < value["expires_at_unix"]
    ):
        raise BenchmarkToolError("writer lease timestamps are inconsistent")
    previous = value.get("previous_lease_sha256")
    if previous is not None:
        if not isinstance(previous, str) or len(previous) != 64:
            raise BenchmarkToolError("writer lease previous digest is invalid")
        try:
            int(previous, 16)
        except ValueError as error:
            raise BenchmarkToolError("writer lease previous digest is invalid") from error
    return dict(value)


def _read_lease(path: Path, paper_id: str) -> tuple[dict[str, Any], bytes] | None:
    if path.is_symlink():
        raise BenchmarkToolError(f"writer lease may not be a symlink: {path}")
    if not path.exists():
        return None
    metadata = path.stat()
    if not stat.S_ISREG(metadata.st_mode) or metadata.st_size > 64 * 1024:
        raise BenchmarkToolError(f"writer lease is not a safe regular file: {path}")
    raw = path.read_bytes()
    return _validate_lease(_strict_json_object(raw, "writer lease"), paper_id), raw


def _fsync_directory(path: Path) -> None:
    descriptor = os.open(path, os.O_RDONLY | getattr(os, "O_DIRECTORY", 0))
    try:
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _atomic_write(path: Path, payload: bytes) -> None:
    if path.is_symlink() or (path.exists() and not path.is_file()):
        raise BenchmarkToolError(f"writer lease destination is unsafe: {path}")
    temporary = path.with_name(f".{path.name}.tmp-{os.getpid()}-{uuid.uuid4().hex}")
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(temporary, flags, 0o600)
    try:
        with os.fdopen(descriptor, "wb") as stream:
            stream.write(payload)
            stream.flush()
            os.fsync(stream.fileno())
        if path.is_symlink():
            raise BenchmarkToolError(f"writer lease destination became a symlink: {path}")
        os.replace(temporary, path)
        os.chmod(path, 0o600)
        _fsync_directory(path.parent)
    except BaseException:
        if temporary.exists() and not temporary.is_symlink():
            temporary.unlink()
        raise


def _archive_lease(
    directory: Path,
    lease: Mapping[str, Any],
    raw: bytes,
    *,
    reason: str,
    now: int,
) -> str:
    history = _secure_child_directory(directory, HISTORY_DIRECTORY, create=True)
    digest = hashlib.sha256(raw).hexdigest()
    name = (
        f"{reason}-{now}-{lease['generation']}-{lease['invocation_id']}-"
        f"{digest[:16]}.json"
    )
    path = history / name
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        descriptor = os.open(path, flags, 0o600)
    except FileExistsError:
        if path.is_symlink() or not path.is_file() or path.read_bytes() != raw:
            raise BenchmarkToolError(f"writer lease history collision: {path}")
        return path.as_posix()
    with os.fdopen(descriptor, "wb") as stream:
        stream.write(raw)
        stream.flush()
        os.fsync(stream.fileno())
    _fsync_directory(history)
    return path.as_posix()


def _holder_matches(lease: Mapping[str, Any], invocation_id: str, token: str) -> bool:
    return (
        lease.get("invocation_id") == invocation_id
        and secrets.compare_digest(str(lease.get("token_sha256")), _token_digest(token))
    )


def _public_lease(lease: Mapping[str, Any], *, now: int) -> dict[str, Any]:
    return {
        key: value
        for key, value in lease.items()
        if key != "token_sha256"
    } | {"active": lease["expires_at_unix"] > now}


def manage_lease(
    scratch_root: Path,
    paper_id: str,
    action: str,
    *,
    invocation_id: str | None = None,
    token: str | None = None,
    ttl_seconds: int = DEFAULT_TTL_SECONDS,
    takeover_expired: bool = False,
    now: int | None = None,
) -> dict[str, Any]:
    if action not in ACTIONS:
        raise BenchmarkToolError(f"unsupported writer-lease action: {action!r}")
    check_invocation_id: str | None = None
    if action == "check":
        if (invocation_id is None) != (token is None):
            raise BenchmarkToolError(
                "check requires both invocation UUID and token, or neither"
            )
        if invocation_id is not None and token is not None:
            check_invocation_id = _canonical_invocation_id(invocation_id)
            _validate_token(token)
        root, existing_directory = _existing_lease_directory(
            scratch_root, paper_id
        )
        if existing_directory is None:
            lease_path = (
                root / "t4_source_faithfulness" / paper_id / LEASE_FILENAME
            )
            return {
                "ok": True,
                "action": action,
                "paper_id": paper_id,
                "held": False,
                "active": False,
                "lease_path": str(lease_path),
            }
        directory = existing_directory
    else:
        directory = _lease_directory(
            scratch_root, paper_id, create=action == "claim"
        )
    lease_path = directory / LEASE_FILENAME
    with _locked_directory(directory):
        current_time = int(time.time()) if now is None else int(now)
        current = _read_lease(lease_path, paper_id)
        if action == "check":
            if current is None:
                return {
                    "ok": True,
                    "action": action,
                    "paper_id": paper_id,
                    "held": False,
                    "active": False,
                    "lease_path": str(lease_path),
                }
            lease, _ = current
            holder_matches = None
            if check_invocation_id is not None and token is not None:
                holder_matches = _holder_matches(
                    lease, check_invocation_id, token
                )
            return {
                "ok": True,
                "action": action,
                "paper_id": paper_id,
                "held": True,
                "holder_matches": holder_matches,
                "lease_path": str(lease_path),
                "lease": _public_lease(lease, now=current_time),
            }

        if action == "claim":
            ttl = _validate_ttl(ttl_seconds)
            canonical_id = _canonical_invocation_id(
                invocation_id if invocation_id is not None else str(uuid.uuid4())
            )
            bearer = _validate_token(
                token if token is not None else secrets.token_urlsafe(32)
            )
            previous_digest: str | None = None
            generation = 1
            archived_path: str | None = None
            if current is not None:
                lease, raw = current
                active = lease["expires_at_unix"] > current_time
                if active:
                    if _holder_matches(lease, canonical_id, bearer):
                        return {
                            "ok": True,
                            "action": action,
                            "paper_id": paper_id,
                            "acquired": False,
                            "reused": True,
                            "token": bearer,
                            "lease_path": str(lease_path),
                            "lease": _public_lease(lease, now=current_time),
                        }
                    raise BenchmarkToolError(
                        f"active writer lease already exists for {paper_id}; "
                        "use another paper or wait for release/expiry"
                    )
                if not takeover_expired:
                    raise BenchmarkToolError(
                        f"expired writer lease exists for {paper_id}; explicit "
                        "--takeover-expired is required"
                    )
                archived_path = _archive_lease(
                    directory, lease, raw, reason="expired", now=current_time
                )
                previous_digest = hashlib.sha256(raw).hexdigest()
                generation = lease["generation"] + 1
            lease = {
                "schema_version": SCHEMA_VERSION,
                "kind": KIND,
                "paper_id": paper_id,
                "invocation_id": canonical_id,
                "token_sha256": _token_digest(bearer),
                "generation": generation,
                "claimed_at_unix": current_time,
                "renewed_at_unix": current_time,
                "expires_at_unix": current_time + ttl,
                "ttl_seconds": ttl,
                "previous_lease_sha256": previous_digest,
            }
            _atomic_write(lease_path, _canonical_json_bytes(lease))
            return {
                "ok": True,
                "action": action,
                "paper_id": paper_id,
                "acquired": True,
                "reused": False,
                "token": bearer,
                "archived_expired_lease": archived_path,
                "lease_path": str(lease_path),
                "lease": _public_lease(lease, now=current_time),
            }

        if invocation_id is None or token is None:
            raise BenchmarkToolError(f"{action} requires invocation UUID and token")
        canonical_id = _canonical_invocation_id(invocation_id)
        bearer = _validate_token(token)
        if current is None:
            raise BenchmarkToolError(f"no writer lease exists for {paper_id}")
        lease, raw = current
        if not _holder_matches(lease, canonical_id, bearer):
            raise BenchmarkToolError("writer lease holder credentials do not match")

        if action == "renew":
            if lease["expires_at_unix"] <= current_time:
                raise BenchmarkToolError(
                    "expired writer lease cannot be renewed; claim it with explicit takeover"
                )
            ttl = _validate_ttl(ttl_seconds)
            renewed = dict(lease)
            renewed["generation"] += 1
            renewed["renewed_at_unix"] = current_time
            renewed["expires_at_unix"] = current_time + ttl
            renewed["ttl_seconds"] = ttl
            renewed["previous_lease_sha256"] = hashlib.sha256(raw).hexdigest()
            _atomic_write(lease_path, _canonical_json_bytes(renewed))
            return {
                "ok": True,
                "action": action,
                "paper_id": paper_id,
                "lease_path": str(lease_path),
                "lease": _public_lease(renewed, now=current_time),
            }

        archived_path = _archive_lease(
            directory, lease, raw, reason="released", now=current_time
        )
        if lease_path.is_symlink() or not lease_path.is_file():
            raise BenchmarkToolError(f"writer lease became unsafe: {lease_path}")
        lease_path.unlink()
        _fsync_directory(directory)
        return {
            "ok": True,
            "action": action,
            "paper_id": paper_id,
            "released": True,
            "archived_lease": archived_path,
            "lease_path": str(lease_path),
        }


@contextmanager
def locked_active_lease(
    scratch_root: Path,
    paper_id: str,
    invocation_id: str,
    token: str,
    *,
    now: int | None = None,
) -> Iterator[Mapping[str, Any]]:
    """Hold the paper lease lock while a bounded write operation executes."""

    canonical_id = _canonical_invocation_id(invocation_id)
    bearer = _validate_token(token)
    directory = _lease_directory(scratch_root, paper_id, create=False)
    with _locked_directory(directory):
        current_time = int(time.time()) if now is None else int(now)
        current = _read_lease(directory / LEASE_FILENAME, paper_id)
        if current is None:
            raise BenchmarkToolError(f"no writer lease exists for {paper_id}")
        lease, _ = current
        if not _holder_matches(lease, canonical_id, bearer):
            raise BenchmarkToolError("writer lease holder credentials do not match")
        if lease["expires_at_unix"] <= current_time:
            raise BenchmarkToolError("writer lease expired before the write operation")
        yield lease


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("action", choices=ACTIONS)
    parser.add_argument("--scratch-root", type=Path, required=True)
    parser.add_argument("--paper-id", required=True)
    parser.add_argument("--invocation-id")
    parser.add_argument("--token")
    parser.add_argument(
        "--credential-out",
        type=Path,
        help=(
            "owner-only absolute output path for generated claim credentials; "
            "required for claim when --token is omitted"
        ),
    )
    parser.add_argument(
        "--credential-file",
        type=Path,
        help=(
            "owner-only credential file used by check, renew, or release; a "
            "successful release removes it"
        ),
    )
    parser.add_argument("--ttl-seconds", type=int, default=DEFAULT_TTL_SECONDS)
    parser.add_argument("--takeover-expired", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    credential_identity: tuple[int, int] | None = None
    try:
        if args.credential_out is not None and args.action != "claim":
            raise BenchmarkToolError("--credential-out is valid only for claim")
        if args.credential_file is not None and args.action == "claim":
            raise BenchmarkToolError(
                "claim uses --credential-out, not --credential-file"
            )
        if args.credential_out is not None and args.credential_file is not None:
            raise BenchmarkToolError(
                "--credential-out and --credential-file are mutually exclusive"
            )

        invocation_id = args.invocation_id
        token = args.token
        if args.credential_file is not None:
            if invocation_id is not None or token is not None:
                raise BenchmarkToolError(
                    "--credential-file cannot be combined with "
                    "--invocation-id or --token"
                )
            invocation_id, token = read_lease_credentials(
                args.credential_file, args.scratch_root, args.paper_id
            )
        elif args.action == "claim":
            if token is None and args.credential_out is None:
                raise BenchmarkToolError(
                    "claim without --token requires an owner-only "
                    "--credential-out path"
                )
            if args.credential_out is not None:
                invocation_id = _canonical_invocation_id(
                    invocation_id if invocation_id is not None else str(uuid.uuid4())
                )
                token = _validate_token(
                    token if token is not None else secrets.token_urlsafe(32)
                )
                credential_identity = write_lease_credentials(
                    args.credential_out,
                    args.scratch_root,
                    args.paper_id,
                    invocation_id,
                    token,
                )
        result = manage_lease(
            args.scratch_root,
            args.paper_id,
            args.action,
            invocation_id=invocation_id,
            token=token,
            ttl_seconds=args.ttl_seconds,
            takeover_expired=args.takeover_expired,
        )
        if args.action == "release" and args.credential_file is not None:
            assert invocation_id is not None and token is not None
            remove_lease_credentials(
                args.credential_file,
                args.scratch_root,
                args.paper_id,
                invocation_id,
                token,
            )
    except (BenchmarkToolError, OSError, ValueError) as error:
        if credential_identity is not None and args.credential_out is not None:
            try:
                metadata = args.credential_out.lstat()
                if (
                    stat.S_ISREG(metadata.st_mode)
                    and (metadata.st_dev, metadata.st_ino) == credential_identity
                ):
                    args.credential_out.unlink()
                    _fsync_directory(args.credential_out.parent)
            except OSError:
                pass
        print(f"t4-writer-lease error: {error}", file=sys.stderr)
        return 2
    public_result = dict(result)
    public_result.pop("token", None)
    if args.credential_out is not None:
        public_result["credential_file"] = str(args.credential_out)
    if args.credential_file is not None:
        public_result["credential_file"] = str(args.credential_file)
        if args.action == "release":
            public_result["credential_file_removed"] = True
    print(json.dumps(public_result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
