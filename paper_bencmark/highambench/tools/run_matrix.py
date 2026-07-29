#!/usr/bin/env python3
"""Run the frozen HighamBench N/L matrix in its recorded order.

The orchestrator deliberately separates *assignments* from *attempts*.  A
SYSTEM_ERROR is kept as an incident and retried once, as required by the
benchmark specification.  Every other outcome becomes the single final record
for that assignment.  The command is resumable: completed assignment records
are not run again unless ``--force`` is supplied.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
from pathlib import PurePosixPath
import platform
import re
import shutil
import subprocess
import sys
import tempfile
from typing import Any, Iterable, Mapping

try:
    from .common import BenchmarkToolError, read_json, sha256_file, write_json
    from .hashes import load_manifest, verify_manifest
except ImportError:  # Direct script execution.
    from common import BenchmarkToolError, read_json, sha256_file, write_json  # type: ignore
    from hashes import load_manifest, verify_manifest  # type: ignore


# A release manifest must cover the complete benchmark tree.  These entries are
# also named explicitly so a truncated manifest cannot silently omit a runtime
# component while still verifying the files it happens to list.
REQUIRED_RUNTIME_RELEASE_FILES = {
    "agent_prompt.md",
    "metadata/library_olean.json",
    "metadata/library_source.json",
    "metadata/manifest.json",
    "metadata/packages_olean.json",
    "metadata/packages_runtime.json",
    "metadata/run_order.json",
    "shared/HighamBench/Definitions.lean",
    "tools/codex_isolated.py",
    "tools/__init__.py",
    "tools/analyze.py",
    "tools/check_construction.py",
    "tools/common.py",
    "tools/dependency_audit.lean",
    "tools/hashes.py",
    "tools/lean_isolated.py",
    "tools/offline_shell.c",
    "tools/preflight.py",
    "tools/render_report.py",
    "tools/result_set.py",
    "tools/run_matrix.py",
    "tools/runner.py",
    "tools/validator.py",
    "tools/tests/__init__.py",
    "tools/tests/test_analyze.py",
    "tools/tests/test_check_construction.py",
    "tools/tests/test_hashes.py",
    "tools/tests/test_isolation_adapters.py",
    "tools/tests/test_preflight.py",
    "tools/tests/test_render_report.py",
    "tools/tests/test_result_set.py",
    "tools/tests/test_run_matrix.py",
    "tools/tests/test_runner.py",
    "tools/tests/test_validator.py",
}
RELEASE_MANIFEST_RELATIVE = "metadata/release_files.json"
FROZEN_RELEASE_MANIFEST_PATH = "paper_bencmark/highambench/metadata/release_files.json"
FROZEN_PACKAGES_RUNTIME_MANIFEST_PATH = (
    "paper_bencmark/highambench/metadata/packages_runtime.json"
)
PACKAGE_BASE_COMPILED_SUFFIX = ".olean"
PACKAGE_COMPILED_SUPPORT_SUFFIXES = (
    ".olean.server",
    ".olean.private",
    ".ir",
)
ENVIRONMENT_BUNDLE_DEFINITION = (
    "SHA-256 of UTF-8 canonical JSON with sorted keys and compact separators over an "
    "object containing the complete config and environment records, after removing "
    "environment_id and environment_bundle_sha256 from their top-level/frozen locations."
)


def _json_argv(items: Iterable[str | Path]) -> str:
    return json.dumps([str(item) for item in items])


def _require_file(path: Path, label: str) -> Path:
    resolved = path.resolve()
    if not resolved.is_file():
        raise BenchmarkToolError(f"{label} is not a file: {resolved}")
    return resolved


def _require_dir(path: Path, label: str) -> Path:
    resolved = path.resolve()
    if not resolved.is_dir():
        raise BenchmarkToolError(f"{label} is not a directory: {resolved}")
    return resolved


def _mapping(value: Any, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise BenchmarkToolError(f"{label} must be a JSON object")
    return value


def _fixed_value(label: str, *values: Any) -> Any:
    """Return one nonempty value after proving all metadata copies agree."""

    if any(value is None or value == "" for value in values):
        raise BenchmarkToolError(f"frozen {label} is missing")
    first = values[0]
    if any(value != first for value in values[1:]):
        raise BenchmarkToolError(f"frozen {label} disagrees across metadata: {values!r}")
    return first


def environment_bundle_digest(
    config: Mapping[str, Any], environment: Mapping[str, Any]
) -> str:
    """Compute the non-circular canonical environment/configuration digest."""

    config_copy = json.loads(json.dumps(config))
    environment_copy = json.loads(json.dumps(environment))
    frozen = config_copy.get("frozen_environment")
    if isinstance(frozen, dict):
        frozen.pop("environment_id", None)
        frozen.pop("environment_bundle_sha256", None)
    environment_copy.pop("environment_id", None)
    environment_copy.pop("environment_bundle_sha256", None)
    payload = {"config": config_copy, "environment": environment_copy}
    canonical = json.dumps(
        payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(canonical).hexdigest()


def canonical_document_digest(value: Mapping[str, Any]) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _nonempty_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise BenchmarkToolError(f"{label} must be a nonempty string")
    return value


def _sha256_value(value: Any, label: str) -> str:
    digest = _nonempty_string(value, label)
    if not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise BenchmarkToolError(f"{label} must be a lowercase SHA-256 digest")
    return digest


def _manifest_papers(manifest: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    raw_papers = manifest.get("papers")
    if not isinstance(raw_papers, list) or not raw_papers:
        raise BenchmarkToolError("benchmark manifest must contain a nonempty papers list")
    papers = [_mapping(value, f"manifest.papers[{index}]") for index, value in enumerate(raw_papers)]
    paper_ids = [
        _nonempty_string(paper.get("paper_id"), f"manifest.papers[{index}].paper_id")
        for index, paper in enumerate(papers)
    ]
    if len(set(paper_ids)) != len(paper_ids):
        raise BenchmarkToolError("benchmark manifest repeats a paper_id")
    for paper_id in paper_ids:
        if re.fullmatch(r"P[0-9]+", paper_id) is None:
            raise BenchmarkToolError(f"invalid paper_id in benchmark manifest: {paper_id!r}")

    corpus = _mapping(manifest.get("corpus"), "manifest.corpus")
    corpus_ids = corpus.get("paper_ids")
    if corpus_ids != paper_ids:
        raise BenchmarkToolError(
            "manifest.corpus.paper_ids must equal the ordered manifest paper IDs"
        )
    if corpus.get("paper_count") != len(papers):
        raise BenchmarkToolError("manifest.corpus.paper_count disagrees with papers")
    return papers


def corpus_slug(manifest: Mapping[str, Any]) -> str:
    """Return the ordered, filesystem-safe corpus identity used in run metadata."""

    return "-".join(str(paper["paper_id"]).lower() for paper in _manifest_papers(manifest))


def _available_manifest_targets(
    manifest: Mapping[str, Any],
) -> list[tuple[Mapping[str, Any], Mapping[str, Any]]]:
    available: list[tuple[Mapping[str, Any], Mapping[str, Any]]] = []
    seen: set[str] = set()
    for paper in _manifest_papers(manifest):
        paper_id = str(paper["paper_id"])
        targets = paper.get("targets")
        if not isinstance(targets, list):
            raise BenchmarkToolError(f"manifest paper {paper_id} has no targets list")
        for index, raw_target in enumerate(targets):
            target = _mapping(raw_target, f"manifest target {paper_id}[{index}]")
            if target.get("availability") != "available":
                continue
            task_id = _nonempty_string(target.get("task_id"), "manifest target task_id")
            if task_id in seen:
                raise BenchmarkToolError(f"benchmark manifest repeats task {task_id}")
            seen.add(task_id)
            tier = _nonempty_string(target.get("tier"), f"manifest target {task_id} tier")
            if task_id != f"{paper_id}-{tier}":
                raise BenchmarkToolError(
                    f"manifest task {task_id} disagrees with paper {paper_id} and tier {tier}"
                )
            available.append((paper, target))
    if not available:
        raise BenchmarkToolError("benchmark manifest contains no available tasks")
    return available


def required_release_files(manifest: Mapping[str, Any]) -> set[str]:
    """Return runtime files plus every paper/task file named by the manifest."""

    required = set(REQUIRED_RUNTIME_RELEASE_FILES)
    for paper in _manifest_papers(manifest):
        required.add(f"tasks/{paper['paper_id']}/paper.json")
    for paper, target in _available_manifest_targets(manifest):
        paper_id = str(paper["paper_id"])
        tier = str(target["tier"])
        task_id = str(target["task_id"])
        required.add(f"metadata/controlled/{task_id}.json")
        required.update(
            {
                f"tasks/{paper_id}/{tier}/Target.lean",
                f"tasks/{paper_id}/{tier}/context.md",
                f"tasks/{paper_id}/{tier}/task.json",
            }
        )
    return required


def _declared_benchmark_path(value: Any, expected: str, label: str) -> str:
    declared = PurePosixPath(_nonempty_string(value, label))
    if declared.is_absolute() or ".." in declared.parts:
        raise BenchmarkToolError(f"{label} is not a safe benchmark path")
    expected_path = PurePosixPath(expected)
    project_path = PurePosixPath("paper_bencmark/highambench") / expected_path
    if declared not in (expected_path, project_path):
        raise BenchmarkToolError(
            f"{label} must name {project_path.as_posix()}, not {declared.as_posix()}"
        )
    return expected_path.as_posix()


def load_task_catalog(
    root: Path, manifest: Mapping[str, Any] | None = None
) -> dict[str, dict[str, str]]:
    """Load execution identities from mutually checked manifest and task records."""

    root = root.resolve()
    manifest = manifest or _mapping(
        read_json(root / "metadata" / "manifest.json"), "benchmark manifest"
    )
    catalog: dict[str, dict[str, str]] = {}
    for paper, target in _available_manifest_targets(manifest):
        paper_id = str(paper["paper_id"])
        tier = str(target["tier"])
        task_id = str(target["task_id"])
        target_dir = f"tasks/{paper_id}/{tier}"
        target_file = f"{target_dir}/Target.lean"
        context_file = f"{target_dir}/context.md"
        task_file = f"{target_dir}/task.json"

        paper_source = _mapping(paper.get("source"), f"manifest paper {paper_id} source")
        paper_sha256 = _sha256_value(
            paper_source.get("sha256"), f"manifest paper {paper_id} source SHA-256"
        )
        paper_record = _mapping(
            read_json(_require_file(root / f"tasks/{paper_id}/paper.json", f"{paper_id} paper record")),
            f"{paper_id} paper record",
        )
        if paper_record.get("paper_id") != paper_id:
            raise BenchmarkToolError(f"{paper_id} paper record has the wrong paper_id")
        recorded_paper_source = _mapping(
            paper_record.get("source"), f"{paper_id} paper record source"
        )
        if recorded_paper_source.get("sha256") != paper_sha256:
            raise BenchmarkToolError(f"{paper_id} paper SHA-256 disagrees across metadata")

        task = _mapping(
            read_json(_require_file(root / task_file, f"{task_id} task record")),
            f"{task_id} task record",
        )
        for field, expected in (
            ("task_id", task_id),
            ("paper_id", paper_id),
            ("tier", tier),
        ):
            if task.get(field) != expected:
                raise BenchmarkToolError(
                    f"{task_id} task record {field}={task.get(field)!r}, expected {expected!r}"
                )
        task_source = _mapping(task.get("paper_source"), f"{task_id}.paper_source")
        if task_source.get("sha256") != paper_sha256:
            raise BenchmarkToolError(f"{task_id} paper SHA-256 disagrees across metadata")
        _declared_benchmark_path(task.get("context_file"), context_file, f"{task_id} context_file")

        formal = _mapping(task.get("formal_statement"), f"{task_id}.formal_statement")
        namespace = _nonempty_string(formal.get("namespace"), f"{task_id} namespace")
        theorem_name = _nonempty_string(
            formal.get("theorem_name"), f"{task_id} theorem_name"
        )
        _declared_benchmark_path(
            formal.get("target_file"), target_file, f"{task_id} formal target_file"
        )
        lean_target = _mapping(target.get("lean_target"), f"manifest target {task_id}.lean_target")
        if lean_target.get("declaration") != theorem_name:
            raise BenchmarkToolError(f"{task_id} theorem name disagrees across metadata")
        _declared_benchmark_path(
            lean_target.get("file"), target_file, f"manifest target {task_id} file"
        )
        required_declaration = f"{namespace}.{theorem_name}"
        validation = _mapping(task.get("validation"), f"{task_id}.validation")
        if validation.get("required_declaration") != required_declaration:
            raise BenchmarkToolError(f"{task_id} validation declaration disagrees")
        _declared_benchmark_path(
            validation.get("controlled_target_file"),
            target_file,
            f"{task_id} controlled target_file",
        )

        for relative, label in (
            (target_file, f"{task_id} target"),
            (context_file, f"{task_id} context"),
            (f"metadata/controlled/{task_id}.json", f"{task_id} controlled manifest"),
        ):
            _require_file(root / relative, label)
        catalog[task_id] = {
            "task_id": task_id,
            "paper_id": paper_id,
            "paper_sha256": paper_sha256,
            "tier": tier,
            "theorem_name": theorem_name,
            "required_declaration": required_declaration,
            "target_dir": target_dir,
            "target_file": target_file,
            "context_file": context_file,
        }

    for paper in _manifest_papers(manifest):
        paper_id = str(paper["paper_id"])
        paper_record = _mapping(
            read_json(root / f"tasks/{paper_id}/paper.json"), f"{paper_id} paper record"
        )
        expected = [
            task_id for task_id, task in catalog.items() if task["paper_id"] == paper_id
        ]
        if paper_record.get("included_tasks") != expected:
            raise BenchmarkToolError(
                f"{paper_id} paper record included_tasks disagrees with the manifest"
            )
    return catalog


def _command_output(command: list[str], label: str) -> str:
    try:
        completed = subprocess.run(
            command,
            check=False,
            capture_output=True,
            text=True,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise BenchmarkToolError(f"cannot inspect {label}: {error}") from error
    if completed.returncode != 0:
        detail = (completed.stderr or completed.stdout).strip()
        raise BenchmarkToolError(
            f"cannot inspect {label} (exit {completed.returncode}): {detail}"
        )
    return (completed.stdout or completed.stderr).strip()


def _git_head(repository: Path, label: str) -> str:
    value = _command_output(
        ["git", "-C", str(repository.resolve()), "rev-parse", "HEAD"], label
    ).splitlines()[-1]
    if not re.fullmatch(r"[0-9a-f]{40}", value):
        raise BenchmarkToolError(f"{label} returned an invalid Git commit: {value!r}")
    return value


def _require_git_sources_clean(repository: Path, paths: list[str], label: str) -> None:
    tracked = subprocess.run(
        ["git", "-C", str(repository.resolve()), "diff", "--quiet", "HEAD", "--", *paths],
        check=False,
        capture_output=True,
        text=True,
    )
    if tracked.returncode not in (0, 1):
        raise BenchmarkToolError(f"cannot check {label} tracked files: {tracked.stderr.strip()}")
    if tracked.returncode == 1:
        raise BenchmarkToolError(f"{label} has tracked changes relative to its frozen commit")
    untracked = _command_output(
        [
            "git",
            "-C",
            str(repository.resolve()),
            "ls-files",
            "--others",
            "--exclude-standard",
            "--",
            *paths,
        ],
        f"{label} untracked files",
    )
    if untracked:
        raise BenchmarkToolError(f"{label} has untracked files: {untracked.splitlines()[:5]}")


def _in_release_scope(relative: str) -> bool:
    if relative == "agent_prompt.md":
        return True
    if relative.startswith(("shared/", "tasks/", "tools/", "metadata/controlled/")):
        return True
    return relative in {
        "metadata/manifest.json",
        "metadata/run_order.json",
        "metadata/library_olean.json",
        "metadata/library_source.json",
        "metadata/packages_olean.json",
        "metadata/packages_runtime.json",
    }


def _release_tree_files(root: Path) -> set[str]:
    files: set[str] = set()
    for path in root.rglob("*"):
        if not path.is_file():
            continue
        relative = path.relative_to(root).as_posix()
        if relative == RELEASE_MANIFEST_RELATIVE:
            continue
        if "__pycache__" in path.parts or path.suffix == ".pyc":
            continue
        if _in_release_scope(relative):
            files.add(relative)
    return files


def _verify_release_manifest(root: Path, raw_path: Path | None) -> dict[str, Any]:
    path = (raw_path or (root / RELEASE_MANIFEST_RELATIVE)).resolve()
    if path != (root / RELEASE_MANIFEST_RELATIVE).resolve():
        raise BenchmarkToolError(
            f"release manifest must be {RELEASE_MANIFEST_RELATIVE}, not {path}"
        )
    _require_file(path, "global release manifest")
    release = load_manifest(path)
    listed = {entry["path"] for entry in release["files"]}
    actual = _release_tree_files(root)
    benchmark_manifest = _mapping(
        read_json(root / "metadata" / "manifest.json"), "benchmark manifest"
    )
    missing_required = sorted(required_release_files(benchmark_manifest) - listed)
    if missing_required:
        raise BenchmarkToolError(
            "global release manifest omits required runtime files: "
            + ", ".join(missing_required)
        )
    if listed != actual:
        omitted = sorted(actual - listed)
        nonexistent = sorted(listed - actual)
        raise BenchmarkToolError(
            "global release manifest is not an exact evaluation-package snapshot "
            f"(omitted={omitted[:8]}, nonexistent={nonexistent[:8]})"
        )
    verification = verify_manifest(root, release)
    if not verification["ok"]:
        raise BenchmarkToolError(
            f"global release files changed after freezing: {verification}"
        )
    return {
        "path": RELEASE_MANIFEST_RELATIVE,
        "sha256": sha256_file(path),
        "file_count": len(listed),
        "verification": verification,
    }


def exact_tree_digest(root: Path) -> dict[str, Any]:
    """Hash every regular file and internal symbolic link in a tree.

    Lean toolchains contain a small number of normal relative symbolic links
    between shared libraries.  Their link text is part of the frozen tree.  A
    link that resolves outside the mounted root is rejected because its final
    bytes would otherwise be outside this fingerprint.
    """

    root = _require_dir(root, "compiled tree")
    entries: list[tuple[str, str, int, str]] = []
    regular_file_count = 0
    symlink_count = 0
    for path in root.rglob("*"):
        if path.is_symlink():
            try:
                path.resolve(strict=True).relative_to(root)
            except (OSError, ValueError) as error:
                raise BenchmarkToolError(
                    f"frozen tree contains a broken or external symlink: {path}"
                ) from error
            link_text = os.readlink(path)
            link_bytes = os.fsencode(link_text)
            relative = path.relative_to(root).as_posix()
            entries.append(
                ("L", relative, len(link_bytes), hashlib.sha256(link_bytes).hexdigest())
            )
            symlink_count += 1
            continue
        if path.is_dir():
            continue
        if not path.is_file():
            raise BenchmarkToolError(f"frozen tree contains a special file: {path}")
        relative = path.relative_to(root).as_posix()
        entries.append(("F", relative, path.stat().st_size, sha256_file(path)))
        regular_file_count += 1
    digest = hashlib.sha256()
    total_bytes = 0
    for entry_type, relative, byte_count, entry_digest in sorted(entries):
        digest.update(entry_type.encode("ascii"))
        digest.update(b"\0")
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(str(byte_count).encode("ascii"))
        digest.update(b"\0")
        digest.update(entry_digest.encode("ascii"))
        digest.update(b"\n")
        total_bytes += byte_count
    return {
        "algorithm": (
            "sha256(entry-type NUL relative-path NUL byte-count NUL "
            "content-or-link-text-sha256 newline)"
        ),
        "file_count": len(entries),
        "regular_file_count": regular_file_count,
        "symlink_count": symlink_count,
        "total_bytes": total_bytes,
        "tree_sha256": digest.hexdigest(),
    }


def compiled_environment_summary(
    toolchain_root: Path, packages_root: Path
) -> dict[str, Any]:
    """Return exact digests for the mounted toolchain and package build trees."""

    toolchain_tree = _require_dir(toolchain_root, "Lean toolchain tree")
    package_rows: list[dict[str, Any]] = []
    for package in sorted(packages_root.iterdir(), key=lambda item: item.name):
        if package.is_symlink():
            raise BenchmarkToolError(f"packages root contains a symlinked package: {package}")
        compiled = package / ".lake" / "build" / "lib" / "lean"
        if not compiled.is_dir():
            continue
        commit = _git_head(package, f"{package.name} package commit")
        _require_git_sources_clean(package, ["."], f"{package.name} package")
        package_rows.append(
            {
                "package": package.name,
                "relative_root": f"{package.name}/.lake/build/lib/lean",
                "git_commit": commit,
                **exact_tree_digest(compiled),
            }
        )
    if not any(row["package"] == "mathlib" for row in package_rows):
        raise BenchmarkToolError("compiled package trees do not contain mathlib")
    return {
        "schema_version": 1,
        "kind": "highambench-compiled-environment-summary",
        # The adapters mount all of toolchain_root, not only lib/lean.  Hash the
        # complete visible tree so executables and auxiliary runtime files are
        # covered by the same exact snapshot.
        "toolchain": {"relative_root": ".", **exact_tree_digest(toolchain_tree)},
        "packages": package_rows,
    }


def _verify_compiled_environment_summary(
    args: argparse.Namespace,
    project: Path,
    frozen: Mapping[str, Any],
    lean: Mapping[str, Any],
) -> dict[str, Any]:
    relative = _fixed_value(
        "compiled environment summary path",
        frozen.get("compiled_environment_summary"),
        lean.get("compiled_environment_summary"),
    )
    expected_digest = _fixed_value(
        "compiled environment summary SHA-256",
        frozen.get("compiled_environment_summary_sha256"),
        lean.get("compiled_environment_summary_sha256"),
    )
    summary_path = (project / str(relative)).resolve()
    try:
        summary_path.relative_to(project)
    except ValueError as error:
        raise BenchmarkToolError("compiled environment summary escapes project root") from error
    _require_file(summary_path, "compiled environment summary")
    if sha256_file(summary_path) != expected_digest:
        raise BenchmarkToolError("compiled environment summary has the wrong SHA-256")
    expected = read_json(summary_path)
    if not isinstance(expected, Mapping):
        raise BenchmarkToolError("compiled environment summary must be an object")
    actual = compiled_environment_summary(args.toolchain_root.resolve(), args.packages_root.resolve())
    if expected != actual:
        raise BenchmarkToolError("actual compiled Lean/package trees differ from the frozen summary")
    return {
        "path": str(relative),
        "sha256": expected_digest,
        "toolchain_file_count": actual["toolchain"]["file_count"],
        "package_count": len(actual["packages"]),
        "package_file_count": sum(row["file_count"] for row in actual["packages"]),
    }


def expected_packages_runtime_files(packages_root: Path) -> set[str]:
    """Return the exact files permitted in the package runtime mount.

    The evaluated process needs each package's base compiled modules and Lean
    4.29's split compiled support files (``.olean.server``,
    ``.olean.private``, and ``.ir``), together with readable mathlib sources.
    It does not need Git metadata, build traces, caches, package sources other
    than mathlib, or any other file from the original package checkouts.
    """

    packages_root = _require_dir(packages_root, "original Lake packages")
    expected: set[str] = set()
    for package in sorted(packages_root.iterdir(), key=lambda item: item.name):
        if package.is_symlink():
            raise BenchmarkToolError(
                f"packages root contains a symlinked package: {package}"
            )
        if not package.is_dir():
            raise BenchmarkToolError(
                f"packages root contains a non-directory entry: {package}"
            )
        compiled = package / ".lake" / "build" / "lib" / "lean"
        if not compiled.is_dir():
            continue
        for path in compiled.rglob("*"):
            if path.is_symlink():
                raise BenchmarkToolError(
                    f"compiled package tree contains a symlink: {path}"
                )
            if path.is_file() and path.name.endswith(
                (PACKAGE_BASE_COMPILED_SUFFIX, *PACKAGE_COMPILED_SUPPORT_SUFFIXES)
            ):
                expected.add(path.relative_to(packages_root).as_posix())

    mathlib = _require_dir(packages_root / "mathlib", "mathlib package")
    mathlib_root = mathlib / "Mathlib.lean"
    if not mathlib_root.is_file() or mathlib_root.is_symlink():
        raise BenchmarkToolError("mathlib runtime source Mathlib.lean is missing")
    expected.add(mathlib_root.relative_to(packages_root).as_posix())
    mathlib_sources = _require_dir(mathlib / "Mathlib", "mathlib source tree")
    for path in mathlib_sources.rglob("*"):
        if path.is_symlink():
            raise BenchmarkToolError(f"mathlib source tree contains a symlink: {path}")
        if path.is_file() and path.suffix == ".lean":
            expected.add(path.relative_to(packages_root).as_posix())
    if not any(path.endswith(PACKAGE_BASE_COMPILED_SUFFIX) for path in expected):
        raise BenchmarkToolError("package runtime contains no compiled Lean modules")
    if not any(path.endswith(PACKAGE_COMPILED_SUPPORT_SUFFIXES) for path in expected):
        raise BenchmarkToolError(
            "package runtime contains no split compiled support files"
        )
    return expected


def _verify_packages_runtime(
    args: argparse.Namespace,
    project: Path,
    frozen: Mapping[str, Any],
    runtime: Mapping[str, Any],
) -> dict[str, Any]:
    relative = _fixed_value(
        "packages runtime manifest path",
        frozen.get("packages_runtime_manifest"),
        runtime.get("packages_runtime_manifest"),
    )
    if relative != FROZEN_PACKAGES_RUNTIME_MANIFEST_PATH:
        raise BenchmarkToolError(
            "frozen packages runtime manifest path must be "
            f"{FROZEN_PACKAGES_RUNTIME_MANIFEST_PATH}"
        )
    expected_digest = _fixed_value(
        "packages runtime manifest SHA-256",
        frozen.get("packages_runtime_manifest_sha256"),
        runtime.get("packages_runtime_manifest_sha256"),
    )
    if not isinstance(expected_digest, str) or not re.fullmatch(
        r"[0-9a-f]{64}", expected_digest
    ):
        raise BenchmarkToolError("packages runtime manifest SHA-256 is invalid")
    manifest_path = (project / str(relative)).resolve()
    try:
        manifest_path.relative_to(project)
    except ValueError as error:
        raise BenchmarkToolError("packages runtime manifest escapes project root") from error
    _require_file(manifest_path, "packages runtime manifest")
    if sha256_file(manifest_path) != expected_digest:
        raise BenchmarkToolError("packages runtime manifest has the wrong SHA-256")
    manifest = load_manifest(manifest_path)
    listed = {entry["path"] for entry in manifest["files"]}
    expected = expected_packages_runtime_files(args.packages_root.resolve())
    if listed != expected:
        raise BenchmarkToolError(
            "packages runtime manifest is not the exact permitted projection "
            f"(omitted={sorted(expected - listed)[:8]}, "
            f"unexpected={sorted(listed - expected)[:8]})"
        )

    runtime_root = _require_dir(
        args.packages_runtime_root, "pruned packages runtime root"
    )
    if runtime_root == args.packages_root.resolve():
        raise BenchmarkToolError(
            "packages runtime root must be a separate pruned tree, not the original package checkout"
        )
    verification = verify_manifest(runtime_root, manifest)
    if not verification["ok"]:
        raise BenchmarkToolError(
            f"pruned packages runtime tree is not frozen: {verification}"
        )
    actual: set[str] = set()
    for path in runtime_root.rglob("*"):
        if path.is_symlink():
            raise BenchmarkToolError(f"packages runtime tree contains a symlink: {path}")
        if path.is_dir():
            continue
        if not path.is_file():
            raise BenchmarkToolError(
                f"packages runtime tree contains a special file: {path}"
            )
        actual.add(path.relative_to(runtime_root).as_posix())
    if actual != listed:
        raise BenchmarkToolError(
            "packages runtime root is not the exact frozen manifest tree "
            f"(extra={sorted(actual - listed)[:8]}, "
            f"missing={sorted(listed - actual)[:8]})"
        )
    return {
        "path": str(relative),
        "sha256": expected_digest,
        "file_count": len(listed),
        "source_file_count": sum(path.endswith(".lean") for path in listed),
        "olean_file_count": sum(
            path.endswith(PACKAGE_BASE_COMPILED_SUFFIX) for path in listed
        ),
        "compiled_support_file_count": sum(
            path.endswith(PACKAGE_COMPILED_SUPPORT_SUFFIXES) for path in listed
        ),
        "verification": verification,
    }


def _visible_memory_bytes() -> int:
    try:
        first = Path("/proc/meminfo").read_text(encoding="utf-8").splitlines()[0]
        key, value, unit = first.split()
        if key != "MemTotal:" or unit != "kB":
            raise ValueError(first)
        return int(value) * 1024
    except (OSError, ValueError, IndexError) as error:
        raise BenchmarkToolError(f"cannot read visible memory size: {error}") from error


def _verify_host_class(environment: Mapping[str, Any], frozen: Mapping[str, Any]) -> dict[str, Any]:
    host = _mapping(environment.get("host_class"), "environment.host_class")
    actual_kernel = f"{platform.system()} {platform.release()} {platform.machine()}"
    actual_virtualization = _command_output(
        ["systemd-detect-virt", "--container"], "container virtualization"
    ).splitlines()[-1]
    processor = ""
    try:
        for line in Path("/proc/cpuinfo").read_text(encoding="utf-8").splitlines():
            if line.lower().startswith("model name") and ":" in line:
                processor = line.split(":", 1)[1].strip()
                break
    except OSError as error:
        raise BenchmarkToolError(f"cannot inspect CPU model: {error}") from error
    online_cpus = len(os.sched_getaffinity(0)) if hasattr(os, "sched_getaffinity") else os.cpu_count()
    actual = {
        "kernel": actual_kernel,
        "virtualization": actual_virtualization.upper(),
        "processor": processor,
        "online_logical_cpus": online_cpus,
        "visible_memory_bytes": _visible_memory_bytes(),
    }
    for field, value in actual.items():
        if host.get(field) != value:
            raise BenchmarkToolError(
                f"host field {field}={value!r} does not match frozen {host.get(field)!r}"
            )
    if frozen.get("operating_system") != actual_kernel:
        raise BenchmarkToolError("config operating_system does not match the current host")
    hardware = frozen.get("hardware_class")
    if not isinstance(hardware, str) or not hardware:
        raise BenchmarkToolError("config has no frozen hardware class")
    return actual


def _match_optional_claim(args: argparse.Namespace, field: str, frozen: Any) -> None:
    claimed = getattr(args, field, None)
    if claimed is not None and claimed != frozen:
        raise BenchmarkToolError(
            f"command-line {field.replace('_', '-')}={claimed!r} disagrees with frozen {frozen!r}"
        )
    setattr(args, field, frozen)


def verify_frozen_run_environment(
    args: argparse.Namespace, root: Path
) -> dict[str, Any]:
    """Verify the complete frozen execution bundle before any attempt starts.

    The returned identity and limits come from the checked metadata.  Caller
    arguments can only assert matching values; they cannot redefine a run.
    """

    project = args.project_root.resolve()
    if args.packages_root.resolve() != (project / ".lake" / "packages").resolve():
        raise BenchmarkToolError("packages_root is not the project .lake/packages tree")
    if args.library_source.resolve() != (project / "NumStability").resolve():
        raise BenchmarkToolError("library_source is not project_root/NumStability")
    if args.library_root_file.resolve() != (project / "NumStability.lean").resolve():
        raise BenchmarkToolError("library_root_file is not project_root/NumStability.lean")
    config = _mapping(read_json(root / "metadata" / "config.json"), "config")
    environment = _mapping(
        read_json(root / "metadata" / "environment.json"), "environment record"
    )
    manifest = _mapping(read_json(root / "metadata" / "manifest.json"), "manifest")
    run_order = _mapping(read_json(root / "metadata" / "run_order.json"), "run order")
    benchmark_id = _fixed_value(
        "benchmark id",
        config.get("benchmark_id"),
        manifest.get("benchmark_id"),
        run_order.get("benchmark_id"),
    )
    frozen = _mapping(config.get("frozen_environment"), "config.frozen_environment")
    lean = _mapping(environment.get("lean"), "environment.lean")
    agent = _mapping(environment.get("agent"), "environment.agent")
    isolation = _mapping(environment.get("isolation"), "environment.isolation")
    runtime = _mapping(environment.get("runtime"), "environment.runtime")
    python_record = _mapping(runtime.get("python"), "environment.runtime.python")

    environment_id = _fixed_value(
        "environment id", frozen.get("environment_id"), environment.get("environment_id")
    )
    bundle_digest = _fixed_value(
        "environment bundle SHA-256",
        frozen.get("environment_bundle_sha256"),
        environment.get("environment_bundle_sha256"),
    )
    if not isinstance(bundle_digest, str) or not re.fullmatch(r"[0-9a-f]{64}", bundle_digest):
        raise BenchmarkToolError("environment bundle SHA-256 is invalid")
    if environment.get("environment_bundle_definition") != ENVIRONMENT_BUNDLE_DEFINITION:
        raise BenchmarkToolError("environment bundle definition does not name the implemented algorithm")
    actual_bundle_digest = environment_bundle_digest(config, environment)
    if bundle_digest != actual_bundle_digest:
        raise BenchmarkToolError(
            "environment_bundle_sha256 does not match the canonical config/environment payload"
        )
    expected_environment_id = f"highambench-{corpus_slug(manifest)}-{bundle_digest[:16]}"
    if environment_id != expected_environment_id:
        raise BenchmarkToolError("environment_id is not derived from the frozen bundle SHA-256")

    agent_id = _fixed_value("agent id", frozen.get("agent_id"), agent.get("id"))
    agent_version = _fixed_value(
        "agent version", frozen.get("agent_version"), agent.get("version")
    )
    model = _fixed_value("model", frozen.get("model_version"), agent.get("model"))
    reasoning_effort = _fixed_value(
        "model reasoning effort",
        frozen.get("model_reasoning_effort"),
        agent.get("reasoning_effort"),
    )
    prompt_digest = _fixed_value(
        "prompt SHA-256", frozen.get("prompt_sha256"), agent.get("prompt_sha256")
    )
    binary_digest = _fixed_value(
        "Codex binary SHA-256",
        frozen.get("agent_binary_sha256"),
        agent.get("binary_sha256"),
    )
    for label, digest in (
        ("prompt SHA-256", prompt_digest),
        ("Codex binary SHA-256", binary_digest),
    ):
        if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise BenchmarkToolError(f"{label} is invalid")

    limits = _mapping(config.get("limits"), "config.limits")
    wall_limit = limits.get("wall_clock_seconds")
    token_limit = limits.get("total_model_tokens")
    if not isinstance(wall_limit, int) or isinstance(wall_limit, bool) or wall_limit <= 0:
        raise BenchmarkToolError("frozen wall-clock limit is not a positive integer")
    if not isinstance(token_limit, int) or isinstance(token_limit, bool) or token_limit <= 0:
        raise BenchmarkToolError("frozen model-token limit is not a positive integer")
    if limits.get("failure_scored_time_seconds") != wall_limit:
        raise BenchmarkToolError("failure scored time must equal the frozen wall-clock limit")
    _match_optional_claim(args, "agent_id", agent_id)
    _match_optional_claim(args, "agent_version", agent_version)
    _match_optional_claim(args, "model", model)
    _match_optional_claim(args, "reasoning_effort", reasoning_effort)
    _match_optional_claim(args, "time_limit_seconds", wall_limit)
    _match_optional_claim(args, "token_limit", token_limit)
    # There is intentionally no --environment-id input.  This is the only
    # assignment of the value used by runner_command.
    args.environment_id = environment_id

    release_relative = _fixed_value(
        "release manifest path",
        frozen.get("release_manifest"),
        environment.get("release_manifest"),
    )
    if release_relative != FROZEN_RELEASE_MANIFEST_PATH:
        raise BenchmarkToolError(
            f"frozen release manifest path must be {FROZEN_RELEASE_MANIFEST_PATH}"
        )
    release_digest = _fixed_value(
        "release manifest SHA-256",
        frozen.get("release_manifest_sha256"),
        environment.get("release_manifest_sha256"),
    )
    release_check = _verify_release_manifest(root, getattr(args, "release_manifest", None))
    if release_check["sha256"] != release_digest:
        raise BenchmarkToolError("global release manifest does not match its frozen SHA-256")
    host_check = _verify_host_class(environment, frozen)

    python_version = _fixed_value(
        "Python version", frozen.get("python_version"), python_record.get("version")
    )
    python_binary_digest = _fixed_value(
        "Python binary SHA-256",
        frozen.get("python_binary_sha256"),
        python_record.get("binary_sha256"),
    )
    if platform.python_version() != python_version:
        raise BenchmarkToolError(
            f"actual Python version {platform.python_version()!r} does not match "
            f"frozen {python_version!r}"
        )
    python_executable = _require_file(Path(sys.executable), "Python executable")
    if not isinstance(python_binary_digest, str) or not re.fullmatch(
        r"[0-9a-f]{64}", python_binary_digest
    ):
        raise BenchmarkToolError("Python binary SHA-256 is invalid")
    if sha256_file(python_executable) != python_binary_digest:
        raise BenchmarkToolError(
            "actual Python executable does not match its frozen SHA-256"
        )

    actual_binary_digest = sha256_file(args.codex.resolve())
    if actual_binary_digest != binary_digest:
        raise BenchmarkToolError("actual Codex binary does not match its frozen SHA-256")
    codex_output = _command_output([str(args.codex.resolve()), "--version"], "Codex version")
    version_match = re.search(r"(?:codex(?:-cli)?\s+)(\S+)", codex_output)
    if version_match is None or version_match.group(1) != agent_version:
        raise BenchmarkToolError(
            f"actual Codex version {codex_output!r} does not match {agent_version!r}"
        )
    feature_output = _command_output(
        [str(args.codex.resolve()), "features", "list"], "Codex feature list"
    )
    rollout_row = next(
        (
            " ".join(line.split())
            for line in feature_output.splitlines()
            if line.split() and line.split()[0] == "rollout_budget"
        ),
        None,
    )
    if rollout_row is None:
        raise BenchmarkToolError(
            "frozen Codex binary does not expose the required rollout_budget feature"
        )
    # The adapter enables this feature under --strict-config and supplies the
    # frozen total-token limit with both accounting weights equal to one.
    args.token_control_verified = True

    expected_lean_commit = _fixed_value(
        "Lean commit", frozen.get("lean_commit"), lean.get("commit")
    )
    lean_executable = _require_file(args.toolchain_root / "bin" / "lean", "Lean executable")
    expected_lean_binary = _fixed_value(
        "Lean binary SHA-256",
        frozen.get("lean_binary_sha256"),
        lean.get("binary_sha256"),
    )
    if sha256_file(lean_executable) != expected_lean_binary:
        raise BenchmarkToolError("actual Lean executable does not match frozen SHA-256")
    lean_output = _command_output([str(lean_executable), "--version"], "Lean version")
    lean_match = re.search(
        r"Lean \(version ([^,]+),.*?commit ([0-9a-f]{40}),", lean_output
    )
    if lean_match is None:
        raise BenchmarkToolError(f"cannot parse Lean version output: {lean_output!r}")
    expected_lean_version = lean.get("version")
    if lean_match.group(1) != expected_lean_version or lean_match.group(2) != expected_lean_commit:
        raise BenchmarkToolError("actual Lean version or commit does not match frozen metadata")
    toolchain = frozen.get("lean_toolchain")
    if not isinstance(toolchain, str) or toolchain.rsplit(":v", 1)[-1] != expected_lean_version:
        raise BenchmarkToolError("Lean toolchain name disagrees with the environment record")

    expected_mathlib = _fixed_value(
        "mathlib commit", frozen.get("mathlib_commit"), lean.get("mathlib_commit")
    )
    expected_numstability = _fixed_value(
        "NumStability commit",
        frozen.get("numstability_commit"),
        lean.get("numstability_commit"),
    )
    mathlib_repository = _require_dir(args.packages_root / "mathlib", "mathlib repository")
    if _git_head(mathlib_repository, "mathlib commit") != expected_mathlib:
        raise BenchmarkToolError("actual mathlib commit does not match frozen metadata")
    if _git_head(project, "NumStability commit") != expected_numstability:
        raise BenchmarkToolError("actual NumStability commit does not match frozen metadata")
    _require_git_sources_clean(mathlib_repository, ["Mathlib", "Mathlib.lean"], "mathlib")
    _require_git_sources_clean(project, ["NumStability", "NumStability.lean"], "NumStability")

    source_manifest_relative = _fixed_value(
        "NumStability source manifest path",
        frozen.get("numstability_source_manifest"),
        lean.get("numstability_source_manifest"),
    )
    source_manifest_digest = _fixed_value(
        "NumStability source manifest SHA-256",
        frozen.get("numstability_source_manifest_sha256"),
        lean.get("numstability_source_manifest_sha256"),
    )
    source_manifest_path = (project / str(source_manifest_relative)).resolve()
    try:
        source_manifest_path.relative_to(project)
    except ValueError as error:
        raise BenchmarkToolError("NumStability source manifest path escapes project root") from error
    _require_file(source_manifest_path, "NumStability source manifest")
    if sha256_file(source_manifest_path) != source_manifest_digest:
        raise BenchmarkToolError("NumStability source manifest has the wrong SHA-256")
    source_manifest = load_manifest(source_manifest_path)
    source_check = verify_manifest(project, source_manifest)
    if not source_check["ok"]:
        raise BenchmarkToolError(f"NumStability source tree is not frozen: {source_check}")
    listed_source = {entry["path"] for entry in source_manifest["files"]}
    actual_source = {"NumStability.lean"}
    for path in (project / "NumStability").rglob("*"):
        if path.is_symlink():
            raise BenchmarkToolError(f"NumStability source tree contains a symlink: {path}")
        if path.is_file():
            actual_source.add(path.relative_to(project).as_posix())
    if listed_source != actual_source:
        raise BenchmarkToolError(
            "NumStability source manifest is not exact "
            f"(extra={sorted(actual_source - listed_source)[:8]}, "
            f"missing={sorted(listed_source - actual_source)[:8]})"
        )

    compiled_environment_check = _verify_compiled_environment_summary(
        args, project, frozen, lean
    )
    packages_runtime_check = _verify_packages_runtime(
        args, project, frozen, runtime
    )

    actual_prompt = _require_file(root / "agent_prompt.md", "agent prompt")
    if sha256_file(actual_prompt) != prompt_digest:
        raise BenchmarkToolError("agent prompt does not match frozen SHA-256")
    shared_source = _require_file(
        root / "shared" / "HighamBench" / "Definitions.lean", "shared source"
    )
    shared_olean = _require_file(
        args.shared_olean_root / "HighamBench" / "Definitions.olean", "shared olean"
    )
    if sha256_file(shared_source) != lean.get("shared_definitions_sha256"):
        raise BenchmarkToolError("shared source does not match frozen SHA-256")
    if sha256_file(shared_olean) != lean.get("shared_definitions_olean_sha256"):
        raise BenchmarkToolError("shared olean does not match frozen SHA-256")
    shared_files: set[str] = set()
    for path in args.shared_olean_root.resolve().rglob("*"):
        if path.is_symlink():
            raise BenchmarkToolError(f"shared olean root contains a symlink: {path}")
        if path.is_file():
            shared_files.add(path.relative_to(args.shared_olean_root.resolve()).as_posix())
    if shared_files != {"HighamBench/Definitions.olean"}:
        raise BenchmarkToolError(
            f"shared olean root is not exact; found importable files {sorted(shared_files)}"
        )

    explicit_hashes = {
        root / "tools" / "codex_isolated.py": isolation.get("filesystem_adapter_sha256"),
        root / "tools" / "lean_isolated.py": isolation.get("lean_adapter_sha256"),
        root / "tools" / "offline_shell.c": isolation.get("offline_shell_source_sha256"),
        root / "tools" / "runner.py": isolation.get("runner_sha256"),
        root / "tools" / "validator.py": isolation.get("validator_sha256"),
        root / "tools" / "dependency_audit.lean": isolation.get("dependency_audit_sha256"),
        args.offline_shell.resolve(): isolation.get("offline_shell_binary_sha256"),
    }
    for path, expected in explicit_hashes.items():
        _require_file(path, f"frozen component {path.name}")
        if not isinstance(expected, str) or sha256_file(path) != expected:
            raise BenchmarkToolError(f"{path.name} does not match its frozen SHA-256")

    bwrap = _require_file(Path("/bin/bwrap"), "bubblewrap executable")
    bwrap_digest = _fixed_value(
        "bubblewrap binary SHA-256",
        frozen.get("bubblewrap_binary_sha256"),
        isolation.get("bubblewrap_binary_sha256"),
    )
    if sha256_file(bwrap) != bwrap_digest:
        raise BenchmarkToolError("actual bubblewrap executable does not match frozen SHA-256")
    bwrap_version = _fixed_value(
        "bubblewrap version",
        frozen.get("bubblewrap_version"),
        isolation.get("bubblewrap_version"),
    )
    actual_bwrap_version = _command_output([str(bwrap), "--version"], "bubblewrap version")
    if actual_bwrap_version != bwrap_version:
        raise BenchmarkToolError("actual bubblewrap version does not match frozen metadata")

    compiled_path = _fixed_value(
        "NumStability compiled manifest path",
        frozen.get("numstability_compiled_manifest"),
        lean.get("numstability_compiled_manifest"),
    )
    compiled_digest = _fixed_value(
        "NumStability compiled manifest SHA-256",
        frozen.get("numstability_compiled_manifest_sha256"),
        lean.get("numstability_compiled_manifest_sha256"),
    )
    compiled_manifest_path = (project / str(compiled_path)).resolve()
    try:
        compiled_manifest_path.relative_to(project)
    except ValueError as error:
        raise BenchmarkToolError("compiled-library manifest path escapes project root") from error
    _require_file(compiled_manifest_path, "NumStability compiled manifest")
    if sha256_file(compiled_manifest_path) != compiled_digest:
        raise BenchmarkToolError("compiled-library manifest file has the wrong SHA-256")
    compiled_manifest = load_manifest(compiled_manifest_path)
    compiled_check = verify_manifest(args.library_olean.resolve(), compiled_manifest)
    if not compiled_check["ok"]:
        raise BenchmarkToolError(f"compiled NumStability tree is not frozen: {compiled_check}")
    listed_compiled = {entry["path"] for entry in compiled_manifest["files"]}
    actual_compiled: set[str] = set()
    for path in args.library_olean.resolve().rglob("*"):
        if path.is_symlink():
            raise BenchmarkToolError(f"compiled NumStability tree contains a symlink: {path}")
        if path.is_file():
            actual_compiled.add(path.relative_to(args.library_olean.resolve()).as_posix())
    if actual_compiled != listed_compiled:
        raise BenchmarkToolError(
            "compiled NumStability mount is not the exact pruned manifest tree "
            f"(extra={sorted(actual_compiled - listed_compiled)[:8]}, "
            f"missing={sorted(listed_compiled - actual_compiled)[:8]})"
        )

    return {
        "schema_version": 1,
        "kind": "highambench-frozen-run-verification",
        "ok": True,
        "benchmark_id": benchmark_id,
        "environment_id": environment_id,
        "environment_bundle_sha256": bundle_digest,
        "agent": {
            "id": agent_id,
            "version": agent_version,
            "binary_sha256": actual_binary_digest,
            "model": model,
            "reasoning_effort": reasoning_effort,
        },
        "python": {
            "version": python_version,
            "binary_sha256": python_binary_digest,
        },
        "token_control": {
            "feature": "rollout_budget",
            "feature_row": rollout_row,
            "strict_config": True,
            "limit_tokens": token_limit,
            "prefill_token_weight": 1,
            "sampling_token_weight": 1,
        },
        "lean": {
            "version": lean_match.group(1),
            "commit": lean_match.group(2),
            "binary_sha256": expected_lean_binary,
            "mathlib_commit": expected_mathlib,
            "numstability_commit": expected_numstability,
            "compiled_files_verified": compiled_check["verified"],
            "source_files_verified": source_check["verified"],
        },
        "host_class": host_check,
        "limits": {"wall_clock_seconds": wall_limit, "total_model_tokens": token_limit},
        "release_manifest": release_check,
        "packages_runtime": packages_runtime_check,
        "compiled_environment_summary": compiled_environment_check,
        "bubblewrap": {"version": bwrap_version, "binary_sha256": bwrap_digest},
        "metadata_document_sha256": {
            "config": canonical_document_digest(config),
            "environment": canonical_document_digest(environment),
            "manifest": canonical_document_digest(manifest),
            "run_order": canonical_document_digest(run_order),
        },
    }


def _copy_incident_logs(record: dict[str, Any], incidents: Path, suffix: str) -> None:
    incidents.mkdir(parents=True, exist_ok=True)
    for field in ("agent_log", "validation_log"):
        raw = record.get(field)
        if not isinstance(raw, str):
            continue
        source = Path(raw)
        if not source.is_file():
            continue
        destination = incidents / f"{record.get('run_id')}.{suffix}.{source.name}"
        shutil.copy2(source, destination)
        record[field] = str(destination)


def _incident_record_paths(incidents_dir: Path, planned_run_id: str) -> list[Path]:
    pattern = re.compile(rf"^{re.escape(planned_run_id)}\.attempt-([0-9]+)\.json$")
    found: list[tuple[int, Path]] = []
    if incidents_dir.is_dir():
        for path in incidents_dir.iterdir():
            match = pattern.fullmatch(path.name)
            if match and path.is_file():
                found.append((int(match.group(1)), path))
    return [path for _, path in sorted(found)]


def _rebuild_jsonl(
    records_dir: Path,
    incidents_dir: Path,
    assignments: list[dict[str, Any]],
    output: Path,
) -> None:
    lines: list[str] = []
    run_ids: set[str] = set()
    for assignment in assignments:
        for incident_path in _incident_record_paths(incidents_dir, assignment["run_id"]):
            incident = read_json(incident_path)
            run_id = incident.get("run_id") if isinstance(incident, Mapping) else None
            if not isinstance(run_id, str) or not run_id:
                raise BenchmarkToolError(f"saved incident has no run_id: {incident_path}")
            if run_id in run_ids:
                raise BenchmarkToolError(f"saved result repeats run_id {run_id}")
            run_ids.add(run_id)
            lines.append(json.dumps(incident, sort_keys=True, separators=(",", ":")))
        record_path = records_dir / f"{assignment['run_id']}.json"
        if record_path.is_file():
            value = read_json(record_path)
            run_id = value.get("run_id") if isinstance(value, Mapping) else None
            if not isinstance(run_id, str) or not run_id:
                raise BenchmarkToolError(f"saved final record has no run_id: {record_path}")
            if run_id in run_ids:
                raise BenchmarkToolError(f"saved result repeats run_id {run_id}")
            run_ids.add(run_id)
            lines.append(json.dumps(value, sort_keys=True, separators=(",", ":")))
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(output.suffix + ".tmp")
    temporary.write_text("\n".join(lines) + ("\n" if lines else ""), encoding="utf-8")
    temporary.replace(output)


def configured_repetition_ids(config: Mapping[str, Any]) -> list[str]:
    repetitions = config.get("repetitions")
    if not isinstance(repetitions, list) or not repetitions:
        raise BenchmarkToolError("config must contain a nonempty repetitions list")
    result: list[str] = []
    for index, raw in enumerate(repetitions):
        repetition = _mapping(raw, f"config.repetitions[{index}]")
        repetition_id = _nonempty_string(
            repetition.get("id"), f"config.repetitions[{index}].id"
        )
        if repetition_id in result:
            raise BenchmarkToolError(f"config repeats repetition {repetition_id}")
        result.append(repetition_id)
    return result


def _validate_planned_counts(
    config: Mapping[str, Any],
    task_catalog: Mapping[str, Mapping[str, str]],
    repetition_ids: list[str],
) -> None:
    planned = config.get("planned_counts_per_agent")
    if planned is None:
        return
    planned = _mapping(planned, "config.planned_counts_per_agent")
    paper_count = len({task["paper_id"] for task in task_catalog.values()})
    expected = {
        "papers": paper_count,
        "tasks": len(task_catalog),
        "repetitions_per_task": len(repetition_ids),
        "conditions": 2,
        "paired_assignments": len(task_catalog) * len(repetition_ids),
        "runs": len(task_catalog) * len(repetition_ids) * 2,
    }
    for field, value in expected.items():
        if planned.get(field) != value:
            raise BenchmarkToolError(
                f"planned count {field}={planned.get(field)!r}, expected {value}"
            )


def assignments_from_order(
    order: Mapping[str, Any],
    task_catalog: Mapping[str, Mapping[str, str]] | None = None,
    repetition_ids: Iterable[str] | None = None,
) -> list[dict[str, Any]]:
    """Expand paired run order and, when supplied, prove exact task coverage."""

    assignments: list[dict[str, Any]] = []
    raw_pairs = order.get("pairs")
    if not isinstance(raw_pairs, list):
        raise BenchmarkToolError("run order must contain a pairs list")
    seen_pairs: set[str] = set()
    seen_runs: set[str] = set()
    seen_task_repetitions: set[tuple[str, str]] = set()
    configured_repetitions = (
        list(repetition_ids) if repetition_ids is not None else None
    )
    if configured_repetitions is not None and len(set(configured_repetitions)) != len(
        configured_repetitions
    ):
        raise BenchmarkToolError("configured repetition IDs are not unique")

    for raw_pair in raw_pairs:
        if not isinstance(raw_pair, Mapping):
            raise BenchmarkToolError("run-order pairs must be objects")
        pair = raw_pair
        pair_id = _nonempty_string(pair.get("pair_id"), "run-order pair_id")
        task_id = _nonempty_string(
            pair.get("task_id"), f"run-order pair {pair_id} task_id"
        )
        repetition_id = _nonempty_string(
            pair.get("repetition_id"), f"run-order pair {pair_id} repetition_id"
        )
        if pair_id != f"{task_id}-{repetition_id}":
            raise BenchmarkToolError(
                f"run-order pair_id {pair_id!r} does not match task and repetition"
            )
        if pair_id in seen_pairs:
            raise BenchmarkToolError(f"run order repeats pair_id {pair_id}")
        seen_pairs.add(pair_id)
        task_repetition = (task_id, repetition_id)
        if task_repetition in seen_task_repetitions:
            raise BenchmarkToolError(
                f"run order repeats task/repetition pair {task_id}/{repetition_id}"
            )
        seen_task_repetitions.add(task_repetition)

        if task_catalog is not None:
            task = task_catalog.get(task_id)
            if task is None:
                raise BenchmarkToolError(f"unknown task in run order: {task_id}")
            task_identity = dict(task)
        else:
            match = re.fullmatch(r"(P[0-9]+)-(T[123])", task_id)
            if match is None:
                raise BenchmarkToolError(f"malformed task in run order: {task_id}")
            task_identity = {
                "task_id": task_id,
                "paper_id": match.group(1),
                "tier": match.group(2),
            }
        if configured_repetitions is not None and repetition_id not in configured_repetitions:
            raise BenchmarkToolError(
                f"run-order pair {pair_id} names unknown repetition {repetition_id}"
            )

        condition_order = pair.get("condition_order")
        run_ids = pair.get("run_ids")
        if condition_order not in (["N", "L"], ["L", "N"]):
            raise BenchmarkToolError(f"bad condition order for {pair_id}")
        if not isinstance(run_ids, list) or len(run_ids) != 2:
            raise BenchmarkToolError(f"bad run IDs for {pair_id}")
        for index, condition in enumerate(condition_order):
            expected = f"{pair_id}-{condition}"
            if run_ids[index] != expected:
                raise BenchmarkToolError(
                    f"run ID/order mismatch for {pair_id}: {run_ids[index]} != {expected}"
                )
            if expected in seen_runs:
                raise BenchmarkToolError(f"run order repeats run_id {expected}")
            seen_runs.add(expected)
            assignments.append(
                {
                    **task_identity,
                    "pair_id": pair_id,
                    "repetition_id": repetition_id,
                    "condition": condition,
                    "condition_order": list(condition_order),
                    "order_index": index + 1,
                    "run_id": run_ids[index],
                }
            )

    if task_catalog is not None and configured_repetitions is not None:
        expected_pairs = {
            (task_id, repetition_id)
            for task_id in task_catalog
            for repetition_id in configured_repetitions
        }
        if seen_task_repetitions != expected_pairs:
            missing = sorted(expected_pairs - seen_task_repetitions)
            unexpected = sorted(seen_task_repetitions - expected_pairs)
            raise BenchmarkToolError(
                "run order is not the exact task/repetition matrix "
                f"(missing={missing[:8]}, unexpected={unexpected[:8]})"
            )
    return assignments


def _assignment_task_identity(
    root: Path, assignment: Mapping[str, Any]
) -> Mapping[str, str]:
    required = {
        "task_id",
        "paper_id",
        "paper_sha256",
        "tier",
        "theorem_name",
        "required_declaration",
        "target_dir",
        "target_file",
        "context_file",
    }
    if required.issubset(assignment):
        return {field: str(assignment[field]) for field in required}
    task_id = _nonempty_string(assignment.get("task_id"), "assignment task_id")
    task = load_task_catalog(root).get(task_id)
    if task is None:
        raise BenchmarkToolError(f"assignment names unknown task {task_id}")
    return task


def runner_command(args: argparse.Namespace, assignment: dict[str, Any], attempt_jsonl: Path,
                   attempt_output: Path, base_workspace: Path) -> list[str]:
    root = args.benchmark_root.resolve()
    project = args.project_root.resolve()
    task = _assignment_task_identity(root, assignment)
    task_id = task["task_id"]
    paper_id = task["paper_id"]
    paper_sha256 = task["paper_sha256"]
    tier = task["tier"]
    condition = assignment["condition"]
    target_declaration = task["required_declaration"]
    common_adapter = [
        sys.executable,
        str(root / "tools" / "codex_isolated.py"),
        "--condition",
        condition,
        "--workspace",
        "{workspace}",
        "--prompt-file",
        "{workspace}/task/agent_prompt.md",
        "--context-file",
        f"{{workspace}}/task/{task['context_file']}",
        "--target-file",
        f"{{workspace}}/task/{task['target_file']}",
        "--usage-output",
        "{workspace}/usage.json",
        "--codex",
        str(args.codex.resolve()),
        "--auth-file",
        str(args.auth_file.resolve()),
        "--offline-shell",
        str(args.offline_shell.resolve()),
        "--toolchain-root",
        str(args.toolchain_root.resolve()),
        "--packages-root",
        str(args.packages_runtime_root.resolve()),
        "--shared-olean-root",
        str(args.shared_olean_root.resolve()),
        "--library-source",
        str(args.library_source.resolve()),
        "--library-root-file",
        str(args.library_root_file.resolve()),
        "--library-olean",
        str(args.library_olean.resolve()),
        "--model",
        args.model,
        "--reasoning-effort",
        args.reasoning_effort,
        "--token-limit",
        str(args.token_limit),
    ]
    lean_base = [
        sys.executable,
        str(root / "tools" / "lean_isolated.py"),
        "--condition",
        condition,
        "--workspace",
        "{workspace}",
        "--toolchain-root",
        str(args.toolchain_root.resolve()),
        "--packages-root",
        str(args.packages_runtime_root.resolve()),
        "--shared-olean-root",
        str(args.shared_olean_root.resolve()),
        "--library-source",
        str(args.library_source.resolve()),
        "--library-root-file",
        str(args.library_root_file.resolve()),
        "--library-olean",
        str(args.library_olean.resolve()),
    ]
    compile_command = lean_base[:2] + ["olean"] + lean_base[2:] + [
        "--source", "{checked_submission}"
    ]
    probe_command = lean_base[:2] + ["probe"] + lean_base[2:] + [
        "--source", "{probe}"
    ]
    audit_command = lean_base[:2] + ["audit"] + lean_base[2:] + [
        "--source", "{checked_submission}",
        "--audit-helper", str((root / "tools" / "dependency_audit.lean").resolve()),
        "--submission-module", "{submission_module}",
        "--target-theorem", target_declaration,
        "--expected-module", "{expected_module}",
        "--expected-theorem", "{expected_theorem}",
        "--local-modules-file", "{local_modules_file}",
    ]

    pair_order = "N-first" if assignment["condition_order"][0] == "N" else "L-first"
    command = [
        sys.executable,
        str((root / "tools" / "runner.py").resolve()),
        "--condition", condition,
        "--task-id", task_id,
        "--paper-id", paper_id,
        "--paper-sha256", paper_sha256,
        "--tier", tier,
        "--repetition-id", assignment["repetition_id"],
        "--pair-id", assignment["pair_id"],
        "--pair-order", pair_order,
        "--order-index", str(assignment["order_index"]),
        "--run-id", assignment["run_id"],
        "--agent-id", args.agent_id,
        "--agent-version", args.agent_version,
        "--model", args.model,
        "--reasoning-effort", args.reasoning_effort,
        "--environment-id", args.environment_id,
        "--freeze-check-json", args.freeze_check_json,
        "--base-workspace", str(base_workspace),
        "--task-root", str(root),
        "--controlled-manifest", str(root / "metadata" / "controlled" / f"{task_id}.json"),
        "--task-dest", "task",
        "--workspace-parent", str((args.results_root / "workspaces").resolve()),
        "--logs-dir", str((args.results_root / "logs").resolve()),
        "--raw-jsonl", str(attempt_jsonl),
        "--submission-relative", "Submission.lean",
        "--canonical-relative", f"task/{task['target_file']}",
        "--target-theorem", target_declaration,
        "--submission-module", "Submission",
        "--audit-helper", str((root / "tools" / "dependency_audit.lean").resolve()),
        "--prompt-relative", "task/agent_prompt.md",
        "--usage-relative", "usage.json",
        "--agent-command-json", _json_argv(common_adapter),
        "--compile-command-json", _json_argv(compile_command),
        "--audit-command-json", _json_argv(audit_command),
        "--n-probe-command-json", _json_argv(probe_command),
        "--hidden-parent", str((args.results_root / "hidden").resolve()),
        "--time-limit-seconds", str(args.time_limit_seconds),
        "--token-limit", str(args.token_limit),
        "--fresh-conversation",
        "--filesystem-isolated",
        "--output", str(attempt_output),
    ]
    if args.agent_network_verified:
        command.append("--network-disabled")
    if args.token_control_verified:
        command.append("--token-enforced")
    if condition == "L":
        command.append("--library-available")
    return command


def run(args: argparse.Namespace) -> int:
    root = _require_dir(args.benchmark_root, "benchmark root")
    _require_dir(args.project_root, "project root")
    for path, label in (
        (args.codex, "Codex executable"),
        (args.auth_file, "Codex auth file"),
        (args.offline_shell, "offline shell"),
        (args.library_root_file, "library root file"),
    ):
        _require_file(path, label)
    for path, label in (
        (args.toolchain_root, "Lean toolchain"),
        (args.packages_root, "Lake packages"),
        (args.packages_runtime_root, "pruned packages runtime"),
        (args.shared_olean_root, "shared olean root"),
        (args.library_source, "library source"),
        (args.library_olean, "library olean root"),
    ):
        _require_dir(path, label)
    freeze_check = verify_frozen_run_environment(args, root)
    manifest = _mapping(
        read_json(root / "metadata" / "manifest.json"), "benchmark manifest"
    )
    config = _mapping(read_json(root / "metadata" / "config.json"), "config")
    task_catalog = load_task_catalog(root, manifest)
    repetition_ids = configured_repetition_ids(config)
    _validate_planned_counts(config, task_catalog, repetition_ids)
    order = _mapping(read_json(root / "metadata" / "run_order.json"), "run order")
    assignments = assignments_from_order(order, task_catalog, repetition_ids)
    expected_runs = len(task_catalog) * len(repetition_ids) * 2
    if len(assignments) != expected_runs:
        raise BenchmarkToolError(
            f"expected {expected_runs} assignments from frozen metadata, "
            f"found {len(assignments)}"
        )

    results = args.results_root.resolve()
    records = results / "records"
    attempts = results / "attempts"
    incidents = results / "incidents"
    for directory in (records, attempts, incidents, results / "logs", results / "workspaces"):
        directory.mkdir(parents=True, exist_ok=True)
    write_json(results / "freeze_check.json", freeze_check)
    args.freeze_check_json = json.dumps(
        freeze_check, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    )

    with tempfile.TemporaryDirectory(prefix="highambench-base-", dir=results) as raw_base:
        base = Path(raw_base)
        for assignment in assignments:
            final_record = records / f"{assignment['run_id']}.json"
            if final_record.is_file() and not args.force:
                continue
            if args.force:
                for old_incident in _incident_record_paths(incidents, assignment["run_id"]):
                    old_incident.unlink()
            selected: dict[str, Any] | None = None
            for attempt in (1, 2):
                attempt_jsonl = attempts / f"{assignment['run_id']}.attempt-{attempt}.jsonl"
                attempt_output = attempts / f"{assignment['run_id']}.attempt-{attempt}.json"
                attempt_jsonl.unlink(missing_ok=True)
                attempt_output.unlink(missing_ok=True)
                command = runner_command(args, assignment, attempt_jsonl, attempt_output, base)
                completed = subprocess.run(command, cwd=args.project_root.resolve(), check=False)
                if not attempt_output.is_file():
                    raise BenchmarkToolError(
                        f"runner produced no record for {assignment['run_id']} (exit {completed.returncode})"
                    )
                selected = read_json(attempt_output)
                if selected.get("run_id") != assignment["run_id"]:
                    raise BenchmarkToolError(
                        f"runner returned run_id {selected.get('run_id')!r}; "
                        f"expected {assignment['run_id']!r}"
                    )
                startup_system_error = (
                    selected.get("failure_code") == "SYSTEM_ERROR"
                    and selected.get("useful_work_started") is False
                )
                if not startup_system_error or attempt == 2:
                    break
                selected["planned_run_id"] = assignment["run_id"]
                selected["run_id"] = (
                    f"{assignment['run_id']}-system-attempt-{attempt}"
                )
                _copy_incident_logs(selected, incidents, f"attempt-{attempt}")
                write_json(
                    incidents / f"{assignment['run_id']}.attempt-{attempt}.json", selected
                )
            assert selected is not None
            write_json(final_record, selected)
            _rebuild_jsonl(records, incidents, assignments, results / "runs.jsonl")
    _rebuild_jsonl(records, incidents, assignments, results / "runs.jsonl")
    complete = sum((records / f"{item['run_id']}.json").is_file() for item in assignments)
    print(f"HighamBench assignments complete: {complete}/{len(assignments)}")
    return 0 if complete == len(assignments) else 1


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve().parents[1]
    parser.add_argument("--benchmark-root", type=Path, default=here)
    parser.add_argument("--project-root", type=Path, required=True)
    parser.add_argument("--results-root", type=Path, required=True)
    parser.add_argument("--codex", type=Path, required=True)
    parser.add_argument("--auth-file", type=Path, required=True)
    parser.add_argument("--offline-shell", type=Path, required=True)
    parser.add_argument("--toolchain-root", type=Path, required=True)
    parser.add_argument("--packages-root", type=Path, required=True)
    parser.add_argument("--packages-runtime-root", type=Path, required=True)
    parser.add_argument("--shared-olean-root", type=Path, required=True)
    parser.add_argument("--library-source", type=Path, required=True)
    parser.add_argument("--library-root-file", type=Path, required=True)
    parser.add_argument("--library-olean", type=Path, required=True)
    parser.add_argument("--release-manifest", type=Path)
    parser.add_argument("--agent-id", help="optional assertion; metadata supplies the value")
    parser.add_argument("--agent-version", help="optional assertion; metadata and the binary supply it")
    parser.add_argument("--model", help="optional assertion; metadata supplies the value")
    parser.add_argument("--reasoning-effort", help="optional assertion; metadata supplies the value")
    parser.add_argument("--time-limit-seconds", type=int, help="optional assertion; metadata supplies it")
    parser.add_argument("--token-limit", type=int, help="optional assertion; metadata supplies it")
    parser.add_argument(
        "--agent-network-verified",
        action="store_true",
        help="claim the agent shell no-socket diagnostic was completed",
    )
    parser.add_argument(
        "--token-control-verified",
        action="store_true",
        help="claim the configured rollout budget was independently verified",
    )
    parser.add_argument("--force", action="store_true")
    return parser


def main() -> int:
    try:
        args = make_parser().parse_args()
        return run(args)
    except (OSError, BenchmarkToolError, ValueError) as error:
        print(f"run-matrix error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
