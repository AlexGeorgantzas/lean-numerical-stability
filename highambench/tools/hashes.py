#!/usr/bin/env python3
"""Create, verify, and stage controlled-file SHA-256 manifests."""

from __future__ import annotations

import argparse
import fnmatch
import os
from pathlib import Path
import shutil
from typing import Any, Iterable

try:
    from .common import (
        BenchmarkToolError,
        SCHEMA_VERSION,
        read_json,
        resolve_below,
        safe_relative_path,
        sha256_file,
        write_json,
    )
except ImportError:  # Direct script execution.
    from common import (  # type: ignore
        BenchmarkToolError,
        SCHEMA_VERSION,
        read_json,
        resolve_below,
        safe_relative_path,
        sha256_file,
        write_json,
    )


def _matches_any(path: str, patterns: Iterable[str]) -> bool:
    return any(fnmatch.fnmatchcase(path, pattern) for pattern in patterns)


def collect_files(
    root: Path,
    requested: list[str] | None,
    excludes: list[str],
    includes: list[str] | None = None,
) -> list[Path]:
    root = root.resolve()
    candidates: list[Path] = []
    if requested:
        for raw in requested:
            path = resolve_below(root, raw)
            if path.is_symlink():
                raise BenchmarkToolError(f"controlled paths may not be symlinks: {raw}")
            if path.is_file():
                candidates.append(path)
            elif path.is_dir():
                candidates.extend(item for item in path.rglob("*") if item.is_file())
            else:
                raise BenchmarkToolError(f"controlled path does not exist: {raw}")
    else:
        candidates.extend(item for item in root.rglob("*") if item.is_file())

    result: list[Path] = []
    for path in sorted(set(candidates)):
        relative = path.relative_to(root).as_posix()
        if includes and not _matches_any(relative, includes):
            continue
        if path.is_symlink():
            raise BenchmarkToolError(
                f"controlled trees may not contain symlinked files: {path.relative_to(root)}"
            )
        if not _matches_any(relative, excludes):
            result.append(path)
    return result


def create_manifest(
    root: Path,
    *,
    requested: list[str] | None = None,
    excludes: list[str] | None = None,
    includes: list[str] | None = None,
    label: str = "controlled-task-files",
) -> dict[str, Any]:
    root = root.resolve()
    files = collect_files(root, requested, excludes or [], includes or [])
    return {
        "schema_version": SCHEMA_VERSION,
        "kind": "highambench-controlled-files",
        "label": label,
        "files": [
            {
                "path": path.relative_to(root).as_posix(),
                "sha256": sha256_file(path),
                "bytes": path.stat().st_size,
            }
            for path in files
        ],
    }


def load_manifest(path: Path) -> dict[str, Any]:
    value = read_json(path)
    if not isinstance(value, dict):
        raise BenchmarkToolError(f"manifest must be a JSON object: {path}")
    if value.get("schema_version") != SCHEMA_VERSION:
        raise BenchmarkToolError(f"unsupported manifest schema in {path}")
    if value.get("kind") != "highambench-controlled-files":
        raise BenchmarkToolError(f"unexpected manifest kind in {path}")
    files = value.get("files")
    if not isinstance(files, list):
        raise BenchmarkToolError(f"manifest files must be a list: {path}")
    seen: set[str] = set()
    for entry in files:
        if not isinstance(entry, dict):
            raise BenchmarkToolError(f"invalid manifest entry in {path}")
        relative = entry.get("path")
        digest = entry.get("sha256")
        byte_count = entry.get("bytes")
        if not isinstance(relative, str) or not isinstance(digest, str):
            raise BenchmarkToolError(f"invalid manifest path or digest in {path}")
        safe_relative_path(relative)
        if relative in seen:
            raise BenchmarkToolError(f"duplicate manifest path: {relative}")
        seen.add(relative)
        if len(digest) != 64 or any(ch not in "0123456789abcdef" for ch in digest):
            raise BenchmarkToolError(f"invalid SHA-256 for {relative}")
        if not isinstance(byte_count, int) or byte_count < 0:
            raise BenchmarkToolError(f"invalid byte count for {relative}")
    return value


def verify_manifest(root: Path, manifest: dict[str, Any]) -> dict[str, Any]:
    root = root.resolve()
    missing: list[str] = []
    changed: list[dict[str, Any]] = []
    verified = 0
    for entry in manifest["files"]:
        relative = entry["path"]
        path = resolve_below(root, relative)
        if not path.is_file() or path.is_symlink():
            missing.append(relative)
            continue
        actual_digest = sha256_file(path)
        actual_bytes = path.stat().st_size
        if actual_digest != entry["sha256"] or actual_bytes != entry["bytes"]:
            changed.append(
                {
                    "path": relative,
                    "expected_sha256": entry["sha256"],
                    "actual_sha256": actual_digest,
                    "expected_bytes": entry["bytes"],
                    "actual_bytes": actual_bytes,
                }
            )
        else:
            verified += 1
    return {
        "ok": not missing and not changed,
        "verified": verified,
        "expected": len(manifest["files"]),
        "missing": missing,
        "changed": changed,
    }


def stage_manifest_files(
    source_root: Path,
    destination_root: Path,
    manifest: dict[str, Any],
    *,
    hardlink: bool = False,
) -> dict[str, Any]:
    source_root = source_root.resolve()
    destination_root.mkdir(parents=True, exist_ok=True)
    before = verify_manifest(source_root, manifest)
    if not before["ok"]:
        raise BenchmarkToolError(f"source controlled files do not match manifest: {before}")
    for entry in manifest["files"]:
        source = resolve_below(source_root, entry["path"])
        destination = resolve_below(destination_root, entry["path"])
        destination.parent.mkdir(parents=True, exist_ok=True)
        if destination.exists():
            raise BenchmarkToolError(f"staged controlled path already exists: {destination}")
        if hardlink:
            os.link(source, destination)
        else:
            shutil.copy2(source, destination)
    after = verify_manifest(destination_root, manifest)
    if not after["ok"]:
        raise BenchmarkToolError(f"staged controlled files failed verification: {after}")
    return after


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    subparsers = parser.add_subparsers(dest="command", required=True)

    create = subparsers.add_parser("create", help="create a controlled-file manifest")
    create.add_argument("--root", type=Path, required=True)
    create.add_argument("--output", type=Path, required=True)
    create.add_argument("--label", default="controlled-task-files")
    create.add_argument("--exclude", action="append", default=[])
    create.add_argument(
        "--include",
        action="append",
        default=[],
        help="include only paths matching at least one shell-style pattern",
    )
    create.add_argument("path", nargs="*")

    verify = subparsers.add_parser("verify", help="verify a controlled-file manifest")
    verify.add_argument("--root", type=Path, required=True)
    verify.add_argument("--manifest", type=Path, required=True)
    verify.add_argument("--output", type=Path)

    stage = subparsers.add_parser(
        "stage", help="copy exactly the manifested files into a destination tree"
    )
    stage.add_argument("--root", type=Path, required=True)
    stage.add_argument("--manifest", type=Path, required=True)
    stage.add_argument("--destination", type=Path, required=True)
    stage.add_argument(
        "--hardlink",
        action="store_true",
        help="stage with hard links (source and destination must share a filesystem)",
    )
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        if args.command == "create":
            manifest = create_manifest(
                args.root,
                requested=args.path or None,
                excludes=args.exclude,
                includes=args.include,
                label=args.label,
            )
            write_json(args.output, manifest)
            return 0
        manifest = load_manifest(args.manifest)
        if args.command == "stage":
            result = stage_manifest_files(
                args.root, args.destination, manifest, hardlink=args.hardlink
            )
            import json

            print(json.dumps(result, indent=2, sort_keys=True))
            return 0
        result = verify_manifest(args.root, manifest)
        if args.output:
            write_json(args.output, result)
        else:
            import json

            print(json.dumps(result, indent=2, sort_keys=True))
        return 0 if result["ok"] else 1
    except BenchmarkToolError as error:
        print(f"error: {error}")
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
