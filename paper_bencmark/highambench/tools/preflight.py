#!/usr/bin/env python3
"""Check that condition N exposes no NumStability library artifacts."""

from __future__ import annotations

import argparse
import os
from pathlib import Path
import tempfile
from typing import Any, Iterable, Sequence

try:
    from .common import (
        BenchmarkToolError,
        parse_command_json,
        render_command,
        run_captured,
        truncate_text,
        write_json,
    )
except ImportError:  # Direct script execution.
    from common import (  # type: ignore
        BenchmarkToolError,
        parse_command_json,
        render_command,
        run_captured,
        truncate_text,
        write_json,
    )


DEFAULT_MARKERS = ("NumStability", "numStability", "lean-fp-analysis")
TEXT_SCAN_SUFFIXES = {
    ".lean",
    ".json",
    ".toml",
    ".yaml",
    ".yml",
    ".md",
    ".txt",
    ".cfg",
    ".ini",
    ".lake",
}
TEXT_SCAN_NAMES = {
    "lake-manifest.json",
    "lakefile.toml",
    "lean-toolchain",
    "manifest.json",
}

# A nonzero compiler exit is not by itself proof that the requested module is
# hidden: the command might instead have failed because Lake is broken, the
# toolchain is missing, or the probe file is unreadable. These fragments are
# import-resolution errors emitted by supported Lean 4 toolchains.
MISSING_IMPORT_MARKERS = (
    "unknown module prefix",
    "unknown module",
    "could not find module",
    "cannot find module",
    "no directory",
    "does not exist in the search path",
    "not found in the search path",
)


def _is_below(path: Path, roots: Sequence[Path]) -> bool:
    resolved = path.resolve()
    for root in roots:
        try:
            resolved.relative_to(root.resolve())
            return True
        except ValueError:
            pass
    return False


def scan_artifact_leaks(
    root: Path,
    *,
    markers: Iterable[str] = DEFAULT_MARKERS,
    content_limit_bytes: int = 4 * 1024 * 1024,
    allowed_roots: Sequence[Path] = (),
) -> list[dict[str, Any]]:
    root = root.resolve()
    markers = tuple(markers)
    leaks: list[dict[str, Any]] = []
    for directory, directory_names, file_names in os.walk(root, followlinks=False):
        base = Path(directory)
        kept_directories: list[str] = []
        for name in directory_names:
            path = base / name
            if _is_below(path, allowed_roots):
                continue
            relative = path.relative_to(root).as_posix()
            if path.is_symlink():
                target = str(path.resolve(strict=False))
                leaks.append({"kind": "symlink", "path": relative, "target": target})
                continue
            if any(marker.lower() in relative.lower() for marker in markers):
                leaks.append({"kind": "path", "path": relative})
            kept_directories.append(name)
        directory_names[:] = kept_directories

        for name in file_names:
            path = base / name
            if _is_below(path, allowed_roots):
                continue
            relative = path.relative_to(root).as_posix()
            if path.is_symlink():
                target = str(path.resolve(strict=False))
                leaks.append({"kind": "symlink", "path": relative, "target": target})
                continue
            if any(marker.lower() in relative.lower() for marker in markers):
                leaks.append({"kind": "path", "path": relative})
            try:
                size = path.stat().st_size
            except OSError:
                continue
            if size > content_limit_bytes:
                continue
            if path.suffix.lower() not in TEXT_SCAN_SUFFIXES and name not in TEXT_SCAN_NAMES:
                continue
            try:
                content = path.read_text(encoding="utf-8", errors="ignore")
            except OSError:
                continue
            found = [marker for marker in markers if marker.lower() in content.lower()]
            if found:
                leaks.append({"kind": "content", "path": relative, "markers": found})
    return sorted(leaks, key=lambda item: (item["path"], item["kind"]))


def probe_forbidden_import(
    root: Path,
    command_template: Sequence[str] | None,
    *,
    module: str = "NumStability",
    timeout_seconds: float = 60.0,
) -> dict[str, Any]:
    if command_template is None:
        return {
            "attempted": False,
            "reliable": False,
            "importable": None,
            "note": "no Lean import-probe command was configured",
        }
    descriptor, raw_path = tempfile.mkstemp(
        prefix="HighamBenchNoLibraryProbe_", suffix=".lean", dir=root
    )
    os.close(descriptor)
    probe = Path(raw_path)
    probe.write_text(f"import {module}\n#check True\n", encoding="utf-8")
    try:
        command = render_command(
            command_template,
            {"workspace": root, "probe": probe, "module": module},
        )
        result = run_captured(command, cwd=root, timeout_seconds=timeout_seconds)
    finally:
        probe.unlink(missing_ok=True)
    output, truncated = truncate_text(result["output"], 20_000)
    if result["system_error"] or result["timed_out"]:
        reliable = False
        importable: bool | None = None
        conclusion = "probe command did not complete"
    elif result["exit_code"] == 0:
        reliable = True
        importable = True
        conclusion = "forbidden module imported successfully"
    else:
        lowered = result["output"].lower()
        missing_module_error = module.lower() in lowered and any(
            marker in lowered for marker in MISSING_IMPORT_MARKERS
        )
        reliable = missing_module_error
        importable = False if missing_module_error else None
        conclusion = (
            "compiler reported that the forbidden module is absent"
            if missing_module_error
            else "compiler failed for a reason that does not prove module absence"
        )
    return {
        "attempted": True,
        "reliable": reliable,
        "importable": importable,
        "command": result["command"],
        "exit_code": result["exit_code"],
        "timed_out": result["timed_out"],
        "system_error": result["system_error"],
        "output": output,
        "output_truncated": truncated,
        "conclusion": conclusion,
    }


def run_preflight(
    root: Path,
    *,
    markers: Iterable[str] = DEFAULT_MARKERS,
    probe_command: Sequence[str] | None = None,
    probe_timeout_seconds: float = 60.0,
    allowed_roots: Sequence[Path] = (),
) -> dict[str, Any]:
    root = root.resolve()
    markers = tuple(markers)
    leaks = scan_artifact_leaks(root, markers=markers, allowed_roots=allowed_roots)
    scanned_files = 0
    scanned_directories = 0
    scanned_symlinks = 0
    for directory, directory_names, file_names in os.walk(root, followlinks=False):
        base = Path(directory)
        kept: list[str] = []
        for name in directory_names:
            path = base / name
            if _is_below(path, allowed_roots):
                continue
            if path.is_symlink():
                scanned_symlinks += 1
            else:
                scanned_directories += 1
                kept.append(name)
        directory_names[:] = kept
        for name in file_names:
            path = base / name
            if _is_below(path, allowed_roots):
                continue
            if path.is_symlink():
                scanned_symlinks += 1
            else:
                scanned_files += 1
    probe = probe_forbidden_import(
        root,
        probe_command,
        timeout_seconds=probe_timeout_seconds,
    )
    ok = not leaks and probe.get("importable") is not True and probe.get("reliable") is True
    return {
        "ok": ok,
        "filesystem_scan": {
            "root": ".",
            "markers": list(markers),
            "regular_file_count": scanned_files,
            "directory_count": scanned_directories,
            "symlink_count": scanned_symlinks,
            "content_limit_bytes": 4 * 1024 * 1024,
        },
        "filesystem_leaks": leaks,
        "import_probe": probe,
        "complete": probe.get("reliable") is True,
    }


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("root", type=Path)
    parser.add_argument("--marker", action="append", default=[])
    parser.add_argument(
        "--probe-command-json",
        help='JSON argv; placeholders: {workspace}, {probe}, {module}',
    )
    parser.add_argument("--probe-timeout-seconds", type=float, default=60.0)
    parser.add_argument("--output", type=Path)
    return parser


def main() -> int:
    args = make_parser().parse_args()
    try:
        command = parse_command_json(args.probe_command_json, option="--probe-command-json")
        result = run_preflight(
            args.root,
            markers=args.marker or DEFAULT_MARKERS,
            probe_command=command,
            probe_timeout_seconds=args.probe_timeout_seconds,
        )
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
