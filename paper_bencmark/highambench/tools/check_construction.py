#!/usr/bin/env python3
"""Validate private construction proofs for manifest-available benchmark tasks.

This command is a release check, not a benchmark run.  It stages only one
released task package in each fresh temporary workspace and copies the matching
private proof to ``Submission.lean``.  The private source directory is never
mounted by either the benchmark agent adapter or the isolated Lean adapter.

The task matrix and theorem names come from ``metadata/manifest.json``. Any
private helper modules imported by a proof are discovered from that paper's
private source directory, copied as source, and compiled afresh inside the
isolated Lean adapter. No paper ID or tier receives a special helper rule, and
no private ``.olean`` file is reused. Every submission then goes through the
normal hidden validator, including its isolated compilation and transitive
dependency audit.
"""

from __future__ import annotations

import argparse
from collections.abc import Iterable, Mapping
from concurrent.futures import ThreadPoolExecutor
from dataclasses import dataclass
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import sys
import tempfile
from typing import Any, Callable

try:
    from .common import (
        BenchmarkToolError,
        SCHEMA_VERSION,
        run_captured,
        sha256_file,
        temporary_directory,
        utc_now,
        write_json,
    )
    from .hashes import load_manifest, stage_manifest_files, verify_manifest
    from .preflight import run_preflight
    from .validator import ValidationConfig, extract_imports, validate
except ImportError:  # Direct script execution.
    from common import (  # type: ignore
        BenchmarkToolError,
        SCHEMA_VERSION,
        run_captured,
        sha256_file,
        temporary_directory,
        utc_now,
        write_json,
    )
    from hashes import load_manifest, stage_manifest_files, verify_manifest  # type: ignore
    from preflight import run_preflight  # type: ignore
    from validator import ValidationConfig, extract_imports, validate  # type: ignore


CENTRAL_MANIFEST_RELATIVE = Path("metadata/manifest.json")
GOLD_PROOF_FILENAME_RE = re.compile(r"^T[0-9]+_[NL]\.lean$")
CURRENT_CONSTRUCTION_EVIDENCE_RELATIVE = Path(
    "metadata/evidence/construction_validation_full_current.json"
)
CONDITION_N_POINTER_RELATIVE = Path("metadata/evidence/condition_n_preflight.json")
LIBRARY_DEPENDENCY_POINTER_RELATIVE = Path(
    "metadata/evidence/library_dependency_probe.json"
)
CURRENT_CONSTRUCTION_EVIDENCE_PROJECT_PATH = (
    "paper_bencmark/highambench/metadata/evidence/"
    "construction_validation_full_current.json"
)
EXPECTED_FULL_PAPER_COUNT = 20
EXPECTED_FULL_TASK_COUNT = 60
EXPECTED_FULL_RESULT_COUNT = 120

CONSTRUCTION_TOOL_RELATIVES = (
    "tools/check_construction.py",
    "tools/common.py",
    "tools/hashes.py",
    "tools/lean_isolated.py",
    "tools/preflight.py",
    "tools/validator.py",
    "tools/dependency_audit.lean",
)
CONDITION_N_FORBIDDEN_MARKERS = (
    "NumStability",
    "numStability",
    "lean-fp-analysis",
)
PACKAGE_BASE_COMPILED_SUFFIX = ".olean"
PACKAGE_COMPILED_SUPPORT_SUFFIXES = (
    ".olean.server",
    ".olean.private",
    ".ir",
)


@dataclass(frozen=True)
class ConstructionSpec:
    task_id: str
    paper_id: str
    tier: str
    condition: str
    target_theorem: str
    canonical_relative: str
    gold_filename: str


@dataclass(frozen=True)
class ConstructionEnvironment:
    project_root: Path
    benchmark_root: Path
    private_gold_root: Path
    central_manifest: Path
    specs: tuple[ConstructionSpec, ...]
    manifest_task_ids: tuple[str, ...]
    manifest_paper_ids: tuple[str, ...]
    selected_paper_ids: tuple[str, ...]
    toolchain_root: Path
    packages_root: Path
    shared_olean_root: Path
    library_source: Path
    library_root_file: Path
    library_olean: Path
    hidden_parent: Path | None
    bwrap: Path
    lean_adapter: Path
    audit_helper: Path
    source_manifest: Path
    compiled_manifest: Path
    packages_manifest: Path
    shared_root_relative: str
    timeout_seconds: float


CommandRunner = Callable[..., dict[str, Any]]
Validator = Callable[[ValidationConfig], dict[str, Any]]
Preflight = Callable[..., dict[str, Any]]


def _manifest_mapping(value: Any, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise BenchmarkToolError(f"{label} must be a JSON object")
    return value


def _manifest_list(value: Any, label: str) -> list[Any]:
    if not isinstance(value, list):
        raise BenchmarkToolError(f"{label} must be a JSON array")
    return value


def _manifest_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise BenchmarkToolError(f"{label} must be a nonempty string")
    return value


def _canonical_target_relative(
    target_file: str, *, paper_id: str, tier: str
) -> str:
    """Validate the central-manifest target and return its benchmark-relative path."""

    expected = Path("tasks") / paper_id / tier / "Target.lean"
    parts = Path(target_file).parts
    suffix = expected.parts
    if len(parts) < len(suffix) or tuple(parts[-len(suffix) :]) != suffix:
        raise BenchmarkToolError(
            f"central manifest target for {paper_id}-{tier} must end in "
            f"{expected.as_posix()}: {target_file}"
        )
    return expected.as_posix()


def construction_specs(
    benchmark_root: Path | None = None,
    *,
    paper_ids: Iterable[str] | None = None,
) -> list[ConstructionSpec]:
    """Discover the N/L construction matrix from the central task manifest.

    Only targets whose manifest ``availability`` is ``"available"`` are
    included.  Manifest order is preserved, with N immediately before L for
    each task.  ``paper_ids`` is an explicit partial-check selector; omitting it
    means every available task in the manifest.
    """

    root = (
        Path(__file__).resolve().parents[1]
        if benchmark_root is None
        else Path(benchmark_root).resolve()
    )
    manifest_path = _required_file(
        root / CENTRAL_MANIFEST_RELATIVE, "central benchmark manifest"
    )
    try:
        document = json.loads(manifest_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise BenchmarkToolError(
            f"central benchmark manifest is invalid JSON: {error}"
        ) from error
    manifest = _manifest_mapping(document, "central benchmark manifest")

    requested: tuple[str, ...] | None = None
    if paper_ids is not None:
        requested = tuple(dict.fromkeys(str(item) for item in paper_ids))
        if not requested or any(not item for item in requested):
            raise BenchmarkToolError("paper selector must contain a nonempty paper id")

    specs: list[ConstructionSpec] = []
    seen_papers: set[str] = set()
    seen_tasks: set[str] = set()
    available_papers: set[str] = set()
    for paper_index, raw_paper in enumerate(
        _manifest_list(manifest.get("papers"), "central manifest papers")
    ):
        paper = _manifest_mapping(raw_paper, f"central manifest paper {paper_index}")
        paper_id = _manifest_string(
            paper.get("paper_id"), f"central manifest paper {paper_index} paper_id"
        )
        if paper_id in seen_papers:
            raise BenchmarkToolError(
                f"central benchmark manifest repeats paper_id {paper_id}"
            )
        seen_papers.add(paper_id)
        for target_index, raw_target in enumerate(
            _manifest_list(
                paper.get("targets"), f"central manifest {paper_id} targets"
            )
        ):
            target = _manifest_mapping(
                raw_target, f"central manifest {paper_id} target {target_index}"
            )
            if target.get("availability") != "available":
                continue
            available_papers.add(paper_id)
            task_id = _manifest_string(
                target.get("task_id"),
                f"central manifest {paper_id} target {target_index} task_id",
            )
            tier = _manifest_string(
                target.get("tier"), f"central manifest {task_id} tier"
            )
            if task_id != f"{paper_id}-{tier}":
                raise BenchmarkToolError(
                    f"central manifest task identity disagrees: {task_id}, "
                    f"paper {paper_id}, tier {tier}"
                )
            if task_id in seen_tasks:
                raise BenchmarkToolError(
                    f"central benchmark manifest repeats task_id {task_id}"
                )
            seen_tasks.add(task_id)
            lean_target = _manifest_mapping(
                target.get("lean_target"), f"central manifest {task_id} lean_target"
            )
            declaration = _manifest_string(
                lean_target.get("declaration"),
                f"central manifest {task_id} Lean declaration",
            )
            target_file = _manifest_string(
                lean_target.get("file"), f"central manifest {task_id} target file"
            )
            canonical_relative = _canonical_target_relative(
                target_file, paper_id=paper_id, tier=tier
            )
            if requested is not None and paper_id not in requested:
                continue
            target_theorem = (
                declaration if "." in declaration else f"HighamBench.{declaration}"
            )
            for condition in ("N", "L"):
                specs.append(
                    ConstructionSpec(
                        task_id=task_id,
                        paper_id=paper_id,
                        tier=tier,
                        condition=condition,
                        target_theorem=target_theorem,
                        canonical_relative=canonical_relative,
                        gold_filename=f"{tier}_{condition}.lean",
                    )
                )

    if requested is not None:
        unknown = [paper_id for paper_id in requested if paper_id not in seen_papers]
        unavailable = [
            paper_id
            for paper_id in requested
            if paper_id in seen_papers and paper_id not in available_papers
        ]
        if unknown:
            raise BenchmarkToolError(
                "paper selector names unknown paper ids: " + ", ".join(unknown)
            )
        if unavailable:
            raise BenchmarkToolError(
                "paper selector has no available tasks: " + ", ".join(unavailable)
            )
    if not specs:
        raise BenchmarkToolError("central benchmark manifest has no selected available tasks")
    return specs


def _required_directory(path: Path, label: str) -> Path:
    resolved = path.resolve()
    if not resolved.is_dir():
        raise BenchmarkToolError(f"{label} is not a directory: {resolved}")
    return resolved


def _required_file(path: Path, label: str) -> Path:
    if path.is_symlink():
        raise BenchmarkToolError(f"{label} may not be a symlink: {path}")
    resolved = path.resolve()
    if not resolved.is_file():
        raise BenchmarkToolError(f"{label} is not a file: {resolved}")
    return resolved


def _private_gold_root(
    private_gold_root: Path, selected_paper_ids: tuple[str, ...]
) -> Path:
    """Normalize either the shared private root or one selected paper directory."""

    root = _required_directory(private_gold_root, "private gold root")
    if len(selected_paper_ids) == 1 and root.name == selected_paper_ids[0]:
        return root.parent.resolve()
    if root.name in selected_paper_ids:
        raise BenchmarkToolError(
            "a direct paper private-gold directory can only be used when that "
            "single paper is selected"
        )
    return root


def _helper_module(relative: Path) -> str:
    return ".".join(relative.with_suffix("").parts)


def local_helper_sources(private_paper_root: Path, gold_path: Path) -> tuple[Path, ...]:
    """Return the imported local-helper closure in dependency-first order.

    A helper is any imported module whose matching ``.lean`` source exists
    below the same paper's private directory. Other private proof files may not
    be used as helpers. This convention is identical for every paper and tier.
    """

    root = private_paper_root.resolve()
    gold = _required_file(gold_path, "private construction proof")
    try:
        gold.relative_to(root)
    except ValueError as error:
        raise BenchmarkToolError("private proof is outside its paper directory") from error

    module_sources: dict[str, Path] = {}
    for source in sorted(root.rglob("*.lean")):
        if source.is_symlink():
            raise BenchmarkToolError(f"private helper source may not be a symlink: {source}")
        relative = source.relative_to(root)
        module = _helper_module(relative)
        if module in module_sources:
            raise BenchmarkToolError(f"duplicate private helper module {module}")
        module_sources[module] = source

    ordered: list[Path] = []
    complete: set[str] = set()
    active: set[str] = set()

    def visit(module: str) -> None:
        source = module_sources.get(module)
        if source is None or source == gold:
            return
        if module in complete:
            return
        if module in active:
            raise BenchmarkToolError(f"cyclic private helper imports include {module}")
        relative = source.relative_to(root)
        if GOLD_PROOF_FILENAME_RE.fullmatch(relative.name):
            raise BenchmarkToolError(
                f"private proof {gold.name} may not import another proof file: {relative}"
            )
        active.add(module)
        try:
            imports = extract_imports(source.read_text(encoding="utf-8"))
        except (OSError, UnicodeDecodeError) as error:
            raise BenchmarkToolError(f"cannot read private helper {relative}: {error}") from error
        for imported in imports:
            visit(imported)
        active.remove(module)
        complete.add(module)
        ordered.append(relative)

    try:
        gold_imports = extract_imports(gold.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError) as error:
        raise BenchmarkToolError(f"cannot read private proof {gold}: {error}") from error
    for imported in gold_imports:
        visit(imported)
    return tuple(ordered)


def _task_ids(specs: Iterable[ConstructionSpec]) -> tuple[str, ...]:
    return tuple(dict.fromkeys(spec.task_id for spec in specs))


def _paper_ids(specs: Iterable[ConstructionSpec]) -> tuple[str, ...]:
    return tuple(dict.fromkeys(spec.paper_id for spec in specs))


def _scope_record(
    *,
    central_manifest: Path,
    manifest_task_ids: tuple[str, ...],
    manifest_paper_ids: tuple[str, ...],
    selected_specs: Iterable[ConstructionSpec],
    selected_paper_ids: tuple[str, ...],
) -> dict[str, Any]:
    selected_task_ids = _task_ids(selected_specs)
    return {
        "central_manifest": CENTRAL_MANIFEST_RELATIVE.as_posix(),
        "central_manifest_sha256": sha256_file(central_manifest),
        "manifest_paper_ids": list(manifest_paper_ids),
        "manifest_available_task_ids": list(manifest_task_ids),
        "selected_paper_ids": list(selected_paper_ids),
        "selected_task_ids": list(selected_task_ids),
        "complete_manifest_scope": (
            selected_task_ids == manifest_task_ids
            and selected_paper_ids == manifest_paper_ids
        ),
    }


def resolve_environment(args: argparse.Namespace) -> ConstructionEnvironment:
    benchmark_root = _required_directory(args.benchmark_root, "benchmark root")
    project_root = _required_directory(args.project_root, "project root")
    all_specs = construction_specs(benchmark_root)
    selected_arg = getattr(args, "paper_id", None)
    manifest_paper_ids = _paper_ids(all_specs)
    if not selected_arg:
        selected_paper_ids = manifest_paper_ids
        specs = all_specs
    else:
        requested_paper_ids = tuple(
            dict.fromkeys(str(item) for item in selected_arg)
        )
        specs = construction_specs(
            benchmark_root, paper_ids=requested_paper_ids
        )
        selected_paper_ids = _paper_ids(specs)
    private_gold_root = _private_gold_root(
        args.private_gold, selected_paper_ids
    )
    hidden_parent: Path | None = None
    if args.hidden_parent is not None:
        args.hidden_parent.mkdir(parents=True, exist_ok=True)
        hidden_parent = _required_directory(args.hidden_parent, "hidden workspace parent")

    environment = ConstructionEnvironment(
        project_root=project_root,
        benchmark_root=benchmark_root,
        private_gold_root=private_gold_root,
        central_manifest=_required_file(
            benchmark_root / CENTRAL_MANIFEST_RELATIVE,
            "central benchmark manifest",
        ),
        specs=tuple(specs),
        manifest_task_ids=_task_ids(all_specs),
        manifest_paper_ids=manifest_paper_ids,
        selected_paper_ids=selected_paper_ids,
        toolchain_root=_required_directory(args.toolchain_root, "Lean toolchain root"),
        packages_root=_required_directory(args.packages_root, "Lean packages root"),
        shared_olean_root=_required_directory(
            args.shared_olean_root, "shared task olean root"
        ),
        library_source=_required_directory(args.library_source, "NumStability source"),
        library_root_file=_required_file(
            args.library_root_file, "NumStability root source"
        ),
        library_olean=_required_directory(args.library_olean, "NumStability olean root"),
        hidden_parent=hidden_parent,
        bwrap=_required_file(args.bwrap, "bubblewrap executable"),
        lean_adapter=_required_file(
            benchmark_root / "tools" / "lean_isolated.py", "isolated Lean adapter"
        ),
        audit_helper=_required_file(
            benchmark_root / "tools" / "dependency_audit.lean",
            "dependency audit helper",
        ),
        source_manifest=_required_file(
            benchmark_root / "metadata" / "library_source.json",
            "NumStability source manifest",
        ),
        compiled_manifest=_required_file(
            benchmark_root / "metadata" / "library_olean.json",
            "NumStability compiled manifest",
        ),
        packages_manifest=_required_file(
            benchmark_root / "metadata" / "packages_runtime.json",
            "pruned package-runtime manifest",
        ),
        shared_root_relative=args.shared_root_relative,
        timeout_seconds=args.timeout_seconds,
    )

    missing_material: list[str] = []
    for spec in specs:
        _required_file(
            benchmark_root / "metadata" / "controlled" / f"{spec.task_id}.json",
            f"{spec.task_id} controlled manifest",
        )
        gold_path = private_gold_root / spec.paper_id / spec.gold_filename
        if gold_path.is_symlink() or not gold_path.is_file():
            missing_material.append(
                f"{spec.task_id}/{spec.condition} proof ({gold_path})"
            )
    if missing_material:
        raise BenchmarkToolError(
            "private construction material is missing for manifest-available "
            "selected tasks: " + "; ".join(missing_material)
        )
    return environment


def _exact_regular_files(root: Path) -> set[str]:
    """List every regular file below ``root`` and reject links/special files."""

    root = root.resolve()
    files: set[str] = set()
    for path in root.rglob("*"):
        if path.is_symlink():
            raise BenchmarkToolError(f"frozen tree contains a symlink: {path}")
        if path.is_dir():
            continue
        if not path.is_file():
            raise BenchmarkToolError(f"frozen tree contains a special file: {path}")
        files.add(path.relative_to(root).as_posix())
    return files


def _manifest_identity(
    manifest_path: Path,
    verification_root: Path,
    *,
    actual_files: set[str],
    label: str,
) -> dict[str, Any]:
    manifest = load_manifest(manifest_path)
    listed = {entry["path"] for entry in manifest["files"]}
    if listed != actual_files:
        raise BenchmarkToolError(
            f"{label} manifest is not an exact tree snapshot "
            f"(extra={sorted(actual_files - listed)[:8]}, "
            f"missing={sorted(listed - actual_files)[:8]})"
        )
    verification = verify_manifest(verification_root, manifest)
    if not verification["ok"]:
        raise BenchmarkToolError(f"{label} manifest verification failed: {verification}")
    return {
        "path": manifest_path.relative_to(manifest_path.parents[1]).as_posix(),
        "sha256": sha256_file(manifest_path),
        "label": manifest.get("label"),
        "file_count": len(listed),
        "total_bytes": sum(entry["bytes"] for entry in manifest["files"]),
        "verified": verification["verified"],
        "exact_tree": True,
    }


def _binary_marker_scan(root: Path, relatives: set[str]) -> dict[str, Any]:
    markers = tuple(marker.lower().encode("utf-8") for marker in CONDITION_N_FORBIDDEN_MARKERS)
    maximum = max(len(marker) for marker in markers)
    matches: list[dict[str, str]] = []
    seen_matches: set[tuple[str, str]] = set()
    total_bytes = 0
    for relative in sorted(relatives):
        path = root / relative
        overlap = b""
        with path.open("rb") as handle:
            while chunk := handle.read(1024 * 1024):
                total_bytes += len(chunk)
                lowered = overlap + chunk.lower()
                for original, marker in zip(CONDITION_N_FORBIDDEN_MARKERS, markers):
                    key = (relative, original)
                    if marker in lowered and key not in seen_matches:
                        seen_matches.add(key)
                        matches.append({"path": relative, "marker": original})
                overlap = lowered[-(maximum - 1) :] if maximum > 1 else b""
    return {
        "complete": True,
        "markers": list(CONDITION_N_FORBIDDEN_MARKERS),
        "files_scanned": len(relatives),
        "bytes_scanned": total_bytes,
        "matches": matches,
        "ok": not matches,
    }


def verification_basis(environment: ConstructionEnvironment) -> dict[str, Any]:
    """Authenticate the tools and exact library trees used by this check."""

    expected_source = (environment.project_root / "NumStability").resolve()
    expected_root_file = (environment.project_root / "NumStability.lean").resolve()
    if environment.library_source != expected_source:
        raise BenchmarkToolError(
            "NumStability source must be project_root/NumStability for construction checks"
        )
    if environment.library_root_file != expected_root_file:
        raise BenchmarkToolError(
            "NumStability root source must be project_root/NumStability.lean"
        )

    source_files = {
        f"NumStability/{relative}"
        for relative in _exact_regular_files(environment.library_source)
    }
    source_files.add("NumStability.lean")
    source_identity = _manifest_identity(
        environment.source_manifest,
        environment.project_root,
        actual_files=source_files,
        label="NumStability source",
    )

    compiled_files = _exact_regular_files(environment.library_olean)
    if not compiled_files or any(
        not relative.startswith("NumStability/") for relative in compiled_files
    ):
        raise BenchmarkToolError(
            "compiled NumStability tree must be nonempty and contain only NumStability/*"
        )
    compiled_identity = _manifest_identity(
        environment.compiled_manifest,
        environment.library_olean,
        actual_files=compiled_files,
        label="compiled NumStability",
    )

    package_files = _exact_regular_files(environment.packages_root)
    bad_package_files = sorted(
        relative
        for relative in package_files
        if not (
            (
                "/.lake/build/lib/lean/" in relative
                and relative.endswith(
                    (PACKAGE_BASE_COMPILED_SUFFIX, *PACKAGE_COMPILED_SUPPORT_SUFFIXES)
                )
            )
            or (
                relative.startswith("mathlib/Mathlib/")
                and relative.endswith(".lean")
            )
            or relative == "mathlib/Mathlib.lean"
        )
    )
    if bad_package_files:
        raise BenchmarkToolError(
            "pruned package runtime contains files outside mathlib source and the "
            "permitted package compiled artifacts (.olean, .olean.server, "
            ".olean.private, .ir): "
            + ", ".join(bad_package_files[:8])
        )
    if not any(
        relative.endswith(PACKAGE_BASE_COMPILED_SUFFIX)
        for relative in package_files
    ):
        raise BenchmarkToolError("pruned package runtime contains no compiled Lean modules")
    if not any(
        relative.endswith(PACKAGE_COMPILED_SUPPORT_SUFFIXES)
        for relative in package_files
    ):
        raise BenchmarkToolError(
            "pruned package runtime contains no split compiled support files"
        )
    if "mathlib/Mathlib.lean" not in package_files:
        raise BenchmarkToolError("pruned package runtime omits mathlib/Mathlib.lean")
    packages_identity = _manifest_identity(
        environment.packages_manifest,
        environment.packages_root,
        actual_files=package_files,
        label="pruned package runtime",
    )
    packages_absence_scan = _binary_marker_scan(
        environment.packages_root, package_files
    )
    if not packages_absence_scan["ok"]:
        raise BenchmarkToolError(
            "pruned package runtime leaks a condition-N marker: "
            f"{packages_absence_scan['matches'][:8]}"
        )

    environment_path = _required_file(
        environment.benchmark_root / "metadata" / "environment.json",
        "benchmark environment record",
    )
    try:
        environment_record = json.loads(environment_path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise BenchmarkToolError(f"benchmark environment record is invalid JSON: {error}") from error
    lean_record = _manifest_mapping(
        _manifest_mapping(environment_record, "benchmark environment record").get("lean"),
        "benchmark environment Lean record",
    )
    frozen_shared_bundles = _manifest_mapping(
        lean_record.get("shared_olean_bundles"), "benchmark shared olean bundles"
    )
    if set(frozen_shared_bundles) != set(environment.manifest_paper_ids):
        raise BenchmarkToolError(
            "benchmark shared olean bundles do not exactly cover the manifest papers"
        )
    try:
        central_record = json.loads(environment.central_manifest.read_text(encoding="utf-8"))
    except json.JSONDecodeError as error:
        raise BenchmarkToolError(f"central benchmark manifest is invalid JSON: {error}") from error
    central_mapping = _manifest_mapping(central_record, "central benchmark manifest")
    expected_modules_by_paper = {
        paper_id: set() for paper_id in environment.manifest_paper_ids
    }
    for index, raw_entry in enumerate(
        _manifest_list(
            central_mapping.get("controlled_shared_files"),
            "central manifest controlled_shared_files",
        )
    ):
        entry = _manifest_mapping(raw_entry, f"controlled shared file {index}")
        path = _manifest_string(entry.get("path"), f"controlled shared file {index} path")
        prefix = "paper_bencmark/highambench/shared/"
        if path.startswith(prefix):
            module_source = path[len(prefix) :]
        elif path.startswith("shared/"):
            module_source = path[len("shared/") :]
        else:
            raise BenchmarkToolError(f"invalid controlled shared path: {path}")
        if not module_source.startswith("HighamBench/") or not module_source.endswith(".lean"):
            raise BenchmarkToolError(f"invalid controlled shared module: {path}")
        module_olean = module_source[:-5] + ".olean"
        for paper_id in _manifest_list(
            entry.get("paper_ids"), f"controlled shared file {path} paper_ids"
        ):
            if paper_id not in expected_modules_by_paper:
                raise BenchmarkToolError(
                    f"controlled shared file {path} names unknown paper {paper_id}"
                )
            expected_modules_by_paper[str(paper_id)].add(module_olean)
    expected_shared_files: set[str] = set()
    shared_olean_bundles: dict[str, dict[str, str]] = {}
    for paper_id in environment.manifest_paper_ids:
        raw_bundle = _manifest_mapping(
            frozen_shared_bundles[paper_id], f"benchmark shared olean bundle {paper_id}"
        )
        if not raw_bundle or any(
            not isinstance(relative, str)
            or not relative.startswith("HighamBench/")
            or not relative.endswith(".olean")
            for relative in raw_bundle
        ):
            raise BenchmarkToolError(
                f"benchmark shared olean bundle {paper_id} names invalid modules"
            )
        if set(raw_bundle) != expected_modules_by_paper[paper_id]:
            raise BenchmarkToolError(
                f"benchmark shared olean bundle {paper_id} disagrees with its paper scope"
            )
        bundle_hashes: dict[str, str] = {}
        for relative, expected in raw_bundle.items():
            if not isinstance(expected, str) or re.fullmatch(r"[0-9a-f]{64}", expected) is None:
                raise BenchmarkToolError(
                    f"invalid frozen SHA-256 for shared olean {paper_id}/{relative}"
                )
            bundled_relative = f"{paper_id}/{relative}"
            expected_shared_files.add(bundled_relative)
            actual = sha256_file(environment.shared_olean_root / bundled_relative)
            if actual != expected:
                raise BenchmarkToolError(
                    f"shared olean {paper_id}/{relative} has the wrong SHA-256"
                )
            bundle_hashes[relative] = actual
        shared_olean_bundles[paper_id] = bundle_hashes
    shared_files = _exact_regular_files(environment.shared_olean_root)
    if shared_files != expected_shared_files:
        raise BenchmarkToolError(
            "shared olean root does not exactly match environment metadata "
            f"(extra={sorted(shared_files - expected_shared_files)}, "
            f"missing={sorted(expected_shared_files - shared_files)})"
        )
    tool_hashes: dict[str, str] = {}
    for relative in CONSTRUCTION_TOOL_RELATIVES:
        path = _required_file(
            environment.benchmark_root / relative, f"construction tool {relative}"
        )
        tool_hashes[relative] = sha256_file(path)

    return {
        "tools": tool_hashes,
        "executables": {
            "python": {
                "path": str(Path(sys.executable).resolve()),
                "sha256": sha256_file(Path(sys.executable).resolve()),
                "version": platform.python_version(),
            },
            "bubblewrap": {
                "path": str(environment.bwrap),
                "sha256": sha256_file(environment.bwrap),
            },
        },
        "shared_olean": {
            "bundles": shared_olean_bundles,
            "exact_file_count": len(expected_shared_files),
            "condition_n_absence_scan": _binary_marker_scan(
                environment.shared_olean_root,
                expected_shared_files,
            ),
        },
        "numstability_source": source_identity,
        "packages_runtime": {
            **packages_identity,
            "mount_root": str(environment.packages_root),
            "only_mathlib_source_and_lean_compiled_artifacts": True,
            "mathlib_source_file_count": sum(
                relative.endswith(".lean") for relative in package_files
            ),
            "base_olean_file_count": sum(
                relative.endswith(PACKAGE_BASE_COMPILED_SUFFIX)
                for relative in package_files
            ),
            "compiled_support_file_count": sum(
                relative.endswith(PACKAGE_COMPILED_SUPPORT_SUFFIXES)
                for relative in package_files
            ),
            "condition_n_absence_scan": packages_absence_scan,
        },
        "numstability_compiled": {
            **compiled_identity,
            "mount_root": str(environment.library_olean),
            "only_numstability_namespace": True,
        },
    }


def isolated_lean_command(
    environment: ConstructionEnvironment,
    *,
    action: str,
    condition: str,
    paper_id: str,
    workspace: str | Path,
    source: str | Path,
    submission_module: str | None = None,
    target_theorem: str | None = None,
    expected_module: str | None = None,
    expected_theorem: str | None = None,
) -> list[str]:
    """Build one wrapper command; N deliberately receives no library options."""

    command = [
        sys.executable,
        str(environment.lean_adapter),
        action,
        "--condition",
        condition,
        "--workspace",
        str(workspace),
        "--source",
        str(source),
        "--toolchain-root",
        str(environment.toolchain_root),
        "--packages-root",
        str(environment.packages_root),
        "--shared-olean-root",
        str(environment.shared_olean_root / paper_id),
        "--shared-root-relative",
        environment.shared_root_relative,
        "--bwrap",
        str(environment.bwrap),
    ]
    if condition == "L":
        command.extend(
            [
                "--library-source",
                str(environment.library_source),
                "--library-root-file",
                str(environment.library_root_file),
                "--library-olean",
                str(environment.library_olean),
            ]
        )
    if action in ("audit", "build-audit"):
        if submission_module is None or target_theorem is None:
            raise BenchmarkToolError(
                "isolated audit command needs a module and target theorem"
            )
        command.extend(
            [
                "--audit-helper",
                str(environment.audit_helper),
                "--submission-module",
                submission_module,
                "--target-theorem",
                target_theorem,
            ]
        )
        if expected_module is not None or expected_theorem is not None:
            if expected_module is None or expected_theorem is None:
                raise BenchmarkToolError(
                    "semantic audit needs both expected module and theorem"
                )
            command.extend(
                [
                    "--expected-module",
                    expected_module,
                    "--expected-theorem",
                    expected_theorem,
                    "--local-modules-file",
                    "{local_modules_file}",
                ]
            )
    return command


def _helper_build_summary(
    completed: dict[str, Any], *, olean_created: bool
) -> dict[str, Any]:
    return {
        "exit_code": completed.get("exit_code"),
        "timed_out": bool(completed.get("timed_out")),
        "system_error": completed.get("system_error"),
        "seconds": completed.get("seconds"),
        "olean_created": olean_created,
    }


def _audit_summary(validation: dict[str, Any]) -> dict[str, Any]:
    audit = validation.get("dependency_audit")
    if not isinstance(audit, dict):
        return {
            "complete": False,
            "exit_code": None,
            "format_version": None,
            "forbidden_dependency_count": None,
            "library_use": validation.get("library_use"),
            "library_declarations": validation.get("library_declarations", []),
        }
    parsed = audit.get("parsed") if isinstance(audit.get("parsed"), dict) else {}
    complete = bool(
        validation.get("library_audit_complete")
        and audit.get("system_error") is None
        and not audit.get("timed_out")
        and audit.get("exit_code") == 0
        and parsed.get("ok")
        and not parsed.get("forbidden_dependencies")
    )
    return {
        "complete": complete,
        "exit_code": audit.get("exit_code"),
        "format_version": parsed.get("format_version"),
        "forbidden_dependency_count": len(parsed.get("forbidden_dependencies", [])),
        "local_modules": parsed.get("local_modules", []),
        "missing_helper_modules": parsed.get("missing_helper_modules", []),
        "semantic_type_check": parsed.get("type_check"),
        "library_use": validation.get("library_use"),
        "library_declarations": validation.get("library_declarations", []),
    }


def _validation_summary(validation: dict[str, Any]) -> dict[str, Any]:
    compile_result = (
        validation.get("compile") if isinstance(validation.get("compile"), dict) else {}
    )
    controlled_before = (
        validation.get("controlled_before")
        if isinstance(validation.get("controlled_before"), dict)
        else {}
    )
    controlled_hidden = (
        validation.get("controlled_hidden")
        if isinstance(validation.get("controlled_hidden"), dict)
        else {}
    )
    controlled_after_compile = (
        validation.get("controlled_after_compile")
        if isinstance(validation.get("controlled_after_compile"), dict)
        else {}
    )
    controlled_after_expected = (
        validation.get("controlled_after_expected_compile")
        if isinstance(validation.get("controlled_after_expected_compile"), dict)
        else {}
    )
    controlled_after_audit = (
        validation.get("controlled_after_audit")
        if isinstance(validation.get("controlled_after_audit"), dict)
        else {}
    )
    semantic = (
        validation.get("semantic_statement_check")
        if isinstance(validation.get("semantic_statement_check"), dict)
        else {}
    )
    statement = (
        validation.get("statement_check")
        if isinstance(validation.get("statement_check"), dict)
        else {}
    )
    return {
        "pass": bool(validation.get("pass")),
        "failure_code": validation.get("failure_code"),
        "note": validation.get("note", ""),
        "statement_unchanged": bool(statement.get("ok")),
        "controlled_before_ok": bool(controlled_before.get("ok")),
        "controlled_hidden_ok": bool(controlled_hidden.get("ok")),
        "controlled_after_compile_ok": bool(controlled_after_compile.get("ok")),
        "controlled_after_expected_compile_ok": bool(
            controlled_after_expected.get("ok")
        ),
        "controlled_after_audit_ok": bool(controlled_after_audit.get("ok")),
        "semantic_statement_equal": semantic.get("equal") is True,
        "static_finding_count": len(validation.get("static_findings", [])),
        "compile_exit_code": compile_result.get("exit_code"),
        "compile_timed_out": bool(compile_result.get("timed_out")),
        "dependency_audit": _audit_summary(validation),
    }


def _construction_reasons(
    spec: ConstructionSpec,
    validation: dict[str, Any],
    audit: dict[str, Any],
) -> list[str]:
    reasons: list[str] = []
    if not validation.get("pass"):
        reasons.append("the existing hidden validator did not accept the proof")
    if not audit.get("complete"):
        reasons.append("the transitive dependency audit was incomplete or failed")
    if spec.condition == "N" and validation.get("library_use") is not False:
        reasons.append("condition N unexpectedly reported a NumStability dependency")
    if spec.condition == "L" and validation.get("library_use") is not True:
        reasons.append("the private L construction did not use a NumStability declaration")
    return reasons


def check_one(
    environment: ConstructionEnvironment,
    spec: ConstructionSpec,
    *,
    command_runner: CommandRunner = run_captured,
    validator_fn: Validator = validate,
    preflight_fn: Preflight = run_preflight,
) -> dict[str, Any]:
    manifest_path = (
        environment.benchmark_root
        / "metadata"
        / "controlled"
        / f"{spec.task_id}.json"
    )
    private_paper_root = environment.private_gold_root / spec.paper_id
    gold_path = private_paper_root / spec.gold_filename
    helper_relatives = local_helper_sources(private_paper_root, gold_path)
    manifest = load_manifest(manifest_path)

    with temporary_directory(
        environment.hidden_parent, prefix=f"highambench-construction-{spec.task_id}-{spec.condition}-"
    ) as workspace:
        task_root = workspace / "task"
        staged = stage_manifest_files(environment.benchmark_root, task_root, manifest)
        n_preflight: dict[str, Any] | None = None
        if spec.condition == "N":
            probe_command = isolated_lean_command(
                environment,
                action="probe",
                condition="N",
                paper_id=spec.paper_id,
                workspace="{workspace}",
                source="{probe}",
            )
            n_preflight = preflight_fn(
                workspace,
                probe_command=probe_command,
                probe_timeout_seconds=environment.timeout_seconds,
            )
            n_preflight["controlled_manifest_sha256"] = sha256_file(manifest_path)
            n_preflight["controlled_files_verified_after_staging"] = staged
            if not n_preflight.get("ok"):
                return {
                    "task_id": spec.task_id,
                    "paper_id": spec.paper_id,
                    "tier": spec.tier,
                    "condition": spec.condition,
                    "target_theorem": spec.target_theorem,
                    "pass": False,
                    "reasons": [
                        "the complete staged condition-N package failed its library-absence preflight"
                    ],
                    "manifest_sha256": sha256_file(manifest_path),
                    "gold_source_sha256": sha256_file(gold_path),
                    "helpers": [],
                    "condition_n_library_arguments_omitted": True,
                    "n_preflight": n_preflight,
                    "validation": None,
                }

        # Private proof material is copied only after the public N-package
        # absence check.  It is never part of what that check scans.
        submission = workspace / "Submission.lean"
        shutil.copy2(gold_path, submission)

        helper_records: list[dict[str, Any]] = []
        local_sources: list[str] = []
        for helper_relative in helper_relatives:
            helper_source = private_paper_root / helper_relative
            staged_helper = workspace / helper_relative
            staged_helper.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(helper_source, staged_helper)
            helper_digest = sha256_file(staged_helper)
            helper_name = helper_relative.as_posix()
            helper_module = _helper_module(helper_relative)
            local_sources.append(helper_name)

            # Build every imported helper from source in the same isolated
            # condition as the proof. The submission's normal dependency audit
            # below checks the complete transitive proof dependency graph.
            helper_command = isolated_lean_command(
                environment,
                action="olean",
                condition=spec.condition,
                paper_id=spec.paper_id,
                workspace=workspace,
                source=staged_helper,
            )
            completed = command_runner(
                helper_command,
                cwd=environment.project_root,
                timeout_seconds=environment.timeout_seconds,
            )
            helper_olean = staged_helper.with_suffix(".olean")
            helper_build = _helper_build_summary(
                completed, olean_created=helper_olean.is_file()
            )
            helper_record = {
                "path": helper_name,
                "module": helper_module,
                "source_sha256": helper_digest,
                "build": helper_build,
            }
            helper_records.append(helper_record)
            if (
                completed.get("system_error") is not None
                or completed.get("timed_out")
                or completed.get("exit_code") != 0
                or not helper_olean.is_file()
            ):
                return {
                    "task_id": spec.task_id,
                    "paper_id": spec.paper_id,
                    "tier": spec.tier,
                    "condition": spec.condition,
                    "target_theorem": spec.target_theorem,
                    "pass": False,
                    "reasons": ["the private helper failed its isolated fresh build"],
                    "manifest_sha256": sha256_file(manifest_path),
                    "gold_source_sha256": sha256_file(gold_path),
                    "helpers": helper_records,
                    "condition_n_library_arguments_omitted": spec.condition == "N",
                    "n_preflight": n_preflight,
                    "validation": None,
                }

        compile_command = isolated_lean_command(
            environment,
            action="olean",
            condition=spec.condition,
            paper_id=spec.paper_id,
            workspace="{workspace}",
            source="{checked_submission}",
        )
        audit_command = isolated_lean_command(
            environment,
            action="audit",
            condition=spec.condition,
            paper_id=spec.paper_id,
            workspace="{workspace}",
            source="{checked_submission}",
            submission_module="{submission_module}",
            target_theorem=spec.target_theorem,
            expected_module="{expected_module}",
            expected_theorem="{expected_theorem}",
        )
        validation = validator_fn(
            ValidationConfig(
                workspace=workspace,
                submission_relative="Submission.lean",
                canonical_relative=f"task/{spec.canonical_relative}",
                target_theorem=spec.target_theorem,
                compile_command=compile_command,
                condition=spec.condition,
                controlled_manifest=manifest_path,
                controlled_root_relative="task",
                local_source_relatives=local_sources,
                audit_command=audit_command,
                submission_module="Submission",
                audit_helper=environment.audit_helper,
                hidden_parent=environment.hidden_parent,
                compile_timeout_seconds=environment.timeout_seconds,
                audit_timeout_seconds=environment.timeout_seconds,
            )
        )
        summary = _validation_summary(validation)
        reasons = _construction_reasons(
            spec, validation, summary["dependency_audit"]
        )
        return {
            "task_id": spec.task_id,
            "paper_id": spec.paper_id,
            "tier": spec.tier,
            "condition": spec.condition,
            "target_theorem": spec.target_theorem,
            "pass": not reasons,
            "reasons": reasons,
            "manifest_sha256": sha256_file(manifest_path),
            "gold_source_sha256": sha256_file(gold_path),
            "helpers": helper_records,
            "condition_n_library_arguments_omitted": spec.condition == "N",
            "n_preflight": n_preflight,
            "validation": summary,
        }


def run_checks(
    environment: ConstructionEnvironment,
    *,
    jobs: int = 1,
    command_runner: CommandRunner = run_captured,
    validator_fn: Validator = validate,
    preflight_fn: Preflight = run_preflight,
) -> dict[str, Any]:
    if jobs <= 0:
        raise BenchmarkToolError("construction jobs must be positive")
    basis = verification_basis(environment)

    def run_one(spec: ConstructionSpec) -> dict[str, Any]:
        try:
            return check_one(
                environment,
                spec,
                command_runner=command_runner,
                validator_fn=validator_fn,
                preflight_fn=preflight_fn,
            )
        except (OSError, BenchmarkToolError, ValueError) as error:
            return {
                "task_id": spec.task_id,
                "paper_id": spec.paper_id,
                "tier": spec.tier,
                "condition": spec.condition,
                "target_theorem": spec.target_theorem,
                "pass": False,
                "reasons": [f"construction check could not run: {error}"],
                "condition_n_library_arguments_omitted": spec.condition == "N",
                "validation": None,
            }

    if jobs == 1:
        results = [run_one(spec) for spec in environment.specs]
    else:
        with ThreadPoolExecutor(max_workers=jobs) as executor:
            results = list(executor.map(run_one, environment.specs))

    passed = sum(bool(result.get("pass")) for result in results)
    n_results = [result for result in results if result["condition"] == "N"]
    l_results = [result for result in results if result["condition"] == "L"]
    expected = len(environment.specs)
    evidence = {
        "schema_version": 1,
        "kind": "highambench-private-construction-check",
        "generated_at_utc": utc_now(),
        "execution": {
            "jobs": jobs,
            "result_order": "central manifest order, N then L per task",
        },
        "pass": passed == len(results) == expected,
        "scope": _scope_record(
            central_manifest=environment.central_manifest,
            manifest_task_ids=environment.manifest_task_ids,
            manifest_paper_ids=environment.manifest_paper_ids,
            selected_specs=environment.specs,
            selected_paper_ids=environment.selected_paper_ids,
        ),
        "summary": {
            "expected": expected,
            "checked": len(results),
            "passed": passed,
            "condition_n_passed": sum(bool(item.get("pass")) for item in n_results),
            "condition_l_passed": sum(bool(item.get("pass")) for item in l_results),
        },
        "isolation": {
            "fresh_workspace_per_result": True,
            "controlled_task_staged_under": "task/",
            "private_gold_staged_as": "Submission.lean",
            "private_helper_oleans_reused": False,
            "condition_n_numstability_mounts_configured": False,
            "condition_n_preflight_after_complete_controlled_staging": True,
            "condition_l_numstability_mounts_configured": True,
            "validator_hidden_rebuild": True,
        },
        "verification_basis": basis,
        "results": results,
    }
    evidence["record_status"] = (
        "current_final"
        if evidence["pass"] and evidence["scope"]["complete_manifest_scope"]
        else "partial_construction_check"
    )
    return evidence


def _hex_digest(value: Any, label: str) -> str:
    if not isinstance(value, str) or re.fullmatch(r"[0-9a-f]{64}", value) is None:
        raise BenchmarkToolError(f"{label} must be a lowercase SHA-256 digest")
    return value


def _positive_integer(value: Any, label: str) -> int:
    if type(value) is not int or value <= 0:
        raise BenchmarkToolError(f"{label} must be a positive integer")
    return value


def _canonical_json_bytes(value: Any) -> bytes:
    return (json.dumps(value, indent=2, sort_keys=True) + "\n").encode("utf-8")


def _current_controlled_manifest_hashes(
    benchmark_root: Path, specs: tuple[ConstructionSpec, ...]
) -> dict[str, str]:
    """Authenticate every live task package and return its manifest digest."""

    hashes: dict[str, str] = {}
    for spec in specs:
        if spec.task_id in hashes:
            continue
        path = benchmark_root / "metadata" / "controlled" / f"{spec.task_id}.json"
        _required_file(path, f"current controlled manifest {spec.task_id}")
        manifest = load_manifest(path)
        if manifest.get("label") != f"{spec.task_id}-controlled":
            raise BenchmarkToolError(
                f"current controlled manifest {spec.task_id} has the wrong label"
            )
        for raw_entry in _manifest_list(
            manifest.get("files"), f"current controlled manifest {spec.task_id} files"
        ):
            entry = _manifest_mapping(
                raw_entry, f"current controlled manifest {spec.task_id} file"
            )
            relative = _manifest_string(
                entry.get("path"), f"current controlled manifest {spec.task_id} path"
            )
            staged_source = benchmark_root / relative
            if staged_source.is_symlink():
                raise BenchmarkToolError(
                    f"current controlled source may not be a symlink: {relative}"
                )
        verification = verify_manifest(benchmark_root, manifest)
        if (
            verification.get("ok") is not True
            or verification.get("changed") != []
            or verification.get("missing") != []
            or verification.get("verified") != verification.get("expected")
        ):
            raise BenchmarkToolError(
                f"current controlled manifest {spec.task_id} does not verify"
            )
        hashes[spec.task_id] = sha256_file(path)
    return hashes


def _validate_validation_summary(
    result: Mapping[str, Any], *, condition: str, target_theorem: str
) -> tuple[bool, bool]:
    """Validate one hidden result and return its N-preflight/L-use flags."""

    task_id = str(result.get("task_id"))
    validation = _manifest_mapping(
        result.get("validation"), f"construction result {task_id}/{condition} validation"
    )
    required_validation = {
        "compile_exit_code": 0,
        "compile_timed_out": False,
        "controlled_after_audit_ok": True,
        "controlled_after_compile_ok": True,
        "controlled_after_expected_compile_ok": True,
        "controlled_before_ok": True,
        "controlled_hidden_ok": True,
        "failure_code": None,
        "pass": True,
        "semantic_statement_equal": True,
        "statement_unchanged": True,
        "static_finding_count": 0,
    }
    if any(validation.get(field) != expected for field, expected in required_validation.items()):
        raise BenchmarkToolError(
            f"construction result {task_id}/{condition} did not pass complete hidden validation"
        )
    if not isinstance(validation.get("note"), str) or not validation["note"].strip():
        raise BenchmarkToolError(
            f"construction result {task_id}/{condition} has no validation note"
        )
    dependency = _manifest_mapping(
        validation.get("dependency_audit"),
        f"construction result {task_id}/{condition} dependency audit",
    )
    semantic = _manifest_mapping(
        dependency.get("semantic_type_check"),
        f"construction result {task_id}/{condition} semantic type check",
    )
    if (
        dependency.get("complete") is not True
        or dependency.get("exit_code") != 0
        or dependency.get("format_version") != 2
        or dependency.get("forbidden_dependency_count") != 0
        or dependency.get("missing_helper_modules") != []
        or semantic.get("candidate") != target_theorem
        or semantic.get("equal") is not True
        or not isinstance(semantic.get("expected"), str)
        or not semantic["expected"]
    ):
        raise BenchmarkToolError(
            f"construction result {task_id}/{condition} has an incomplete dependency audit"
        )

    helpers = _manifest_list(
        result.get("helpers"), f"construction result {task_id}/{condition} helpers"
    )
    for index, raw_helper in enumerate(helpers):
        helper = _manifest_mapping(
            raw_helper, f"construction result {task_id}/{condition} helper {index}"
        )
        build = _manifest_mapping(
            helper.get("build"),
            f"construction result {task_id}/{condition} helper {index} build",
        )
        _manifest_string(
            helper.get("path"),
            f"construction result {task_id}/{condition} helper {index} path",
        )
        _manifest_string(
            helper.get("module"),
            f"construction result {task_id}/{condition} helper {index} module",
        )
        _hex_digest(
            helper.get("source_sha256"),
            f"construction result {task_id}/{condition} helper {index}",
        )
        if (
            build.get("exit_code") != 0
            or build.get("olean_created") is not True
            or build.get("timed_out") is not False
            or build.get("system_error") is not None
        ):
            raise BenchmarkToolError(
                f"construction result {task_id}/{condition} has a failed helper build"
            )

    declarations = _manifest_list(
        dependency.get("library_declarations"),
        f"construction result {task_id}/{condition} library declarations",
    )
    if condition == "N":
        preflight = _manifest_mapping(
            result.get("n_preflight"),
            f"construction result {task_id}/N preflight",
        )
        controlled = _manifest_mapping(
            preflight.get("controlled_files_verified_after_staging"),
            f"construction result {task_id}/N controlled staging",
        )
        probe = _manifest_mapping(
            preflight.get("import_probe"),
            f"construction result {task_id}/N import probe",
        )
        if (
            result.get("condition_n_library_arguments_omitted") is not True
            or preflight.get("ok") is not True
            or preflight.get("complete") is not True
            or preflight.get("controlled_manifest_sha256")
            != result.get("manifest_sha256")
            or preflight.get("filesystem_leaks") != []
            or controlled.get("ok") is not True
            or controlled.get("changed") != []
            or controlled.get("missing") != []
            or controlled.get("verified") != controlled.get("expected")
            or type(controlled.get("verified")) is not int
            or controlled["verified"] <= 0
            or probe.get("attempted") is not True
            or probe.get("reliable") is not True
            or probe.get("importable") is not False
            or probe.get("timed_out") is not False
            or probe.get("system_error") is not None
            or dependency.get("library_use") is not False
            or declarations != []
        ):
            raise BenchmarkToolError(
                f"construction result {task_id}/N has an incomplete isolation preflight"
            )
        return True, False

    if (
        result.get("condition_n_library_arguments_omitted") is not False
        or result.get("n_preflight") is not None
        or dependency.get("library_use") is not True
        or not declarations
    ):
        raise BenchmarkToolError(
            f"construction result {task_id}/L has no authenticated NumStability use"
        )
    for index, raw_declaration in enumerate(declarations):
        declaration = _manifest_mapping(
            raw_declaration,
            f"construction result {task_id}/L library declaration {index}",
        )
        name = _manifest_string(
            declaration.get("name"),
            f"construction result {task_id}/L library declaration {index} name",
        )
        module = _manifest_string(
            declaration.get("module"),
            f"construction result {task_id}/L library declaration {index} module",
        )
        if "NumStability" not in name or not module.startswith("NumStability"):
            raise BenchmarkToolError(
                f"construction result {task_id}/L cites a non-NumStability declaration"
            )
    return False, True


def validate_current_construction_evidence(
    environment: ConstructionEnvironment, evidence: Mapping[str, Any]
) -> dict[str, Any]:
    """Authenticate one promotable, complete 20-paper/60-task N/L certificate."""

    raw_root = Path(environment.benchmark_root)
    if raw_root.is_symlink():
        raise BenchmarkToolError("benchmark root may not be a symlink during promotion")
    root = _required_directory(raw_root, "benchmark root")
    central_manifest = _required_file(
        root / CENTRAL_MANIFEST_RELATIVE, "central benchmark manifest"
    )
    specs = tuple(construction_specs(root))
    task_ids = _task_ids(specs)
    paper_ids = _paper_ids(specs)
    if (
        len(specs) != EXPECTED_FULL_RESULT_COUNT
        or len(task_ids) != EXPECTED_FULL_TASK_COUNT
        or len(paper_ids) != EXPECTED_FULL_PAPER_COUNT
    ):
        raise BenchmarkToolError(
            "construction promotion requires exactly 20 papers, 60 tasks, and 120 N/L results"
        )
    if (
        tuple(environment.specs) != specs
        or environment.manifest_task_ids != task_ids
        or environment.manifest_paper_ids != paper_ids
        or environment.selected_paper_ids != paper_ids
    ):
        raise BenchmarkToolError(
            "construction promotion requires the resolved complete current environment"
        )
    expected_top_level = {
        "schema_version",
        "kind",
        "generated_at_utc",
        "execution",
        "pass",
        "record_status",
        "scope",
        "summary",
        "isolation",
        "verification_basis",
        "results",
    }
    if set(evidence) != expected_top_level:
        raise BenchmarkToolError(
            "construction promotion certificate has a noncanonical top-level schema"
        )
    if (
        evidence.get("schema_version") != 1
        or evidence.get("kind") != "highambench-private-construction-check"
        or evidence.get("pass") is not True
        or evidence.get("record_status") != "current_final"
    ):
        raise BenchmarkToolError(
            "construction promotion requires a passing current_final certificate"
        )
    _manifest_string(evidence.get("generated_at_utc"), "construction generation time")

    expected_summary = {
        "expected": EXPECTED_FULL_RESULT_COUNT,
        "checked": EXPECTED_FULL_RESULT_COUNT,
        "passed": EXPECTED_FULL_RESULT_COUNT,
        "condition_n_passed": EXPECTED_FULL_TASK_COUNT,
        "condition_l_passed": EXPECTED_FULL_TASK_COUNT,
    }
    summary = _manifest_mapping(evidence.get("summary"), "construction summary")
    if dict(summary) != expected_summary:
        raise BenchmarkToolError("construction promotion requires exact 120/120 summary counts")

    scope = _manifest_mapping(evidence.get("scope"), "construction scope")
    expected_scope = {
        "central_manifest": CENTRAL_MANIFEST_RELATIVE.as_posix(),
        "central_manifest_sha256": sha256_file(central_manifest),
        "manifest_paper_ids": list(paper_ids),
        "manifest_available_task_ids": list(task_ids),
        "selected_paper_ids": list(paper_ids),
        "selected_task_ids": list(task_ids),
        "complete_manifest_scope": True,
    }
    if dict(scope) != expected_scope:
        raise BenchmarkToolError(
            "construction promotion scope is not bound to the complete current manifest"
        )
    execution = _manifest_mapping(evidence.get("execution"), "construction execution")
    _positive_integer(execution.get("jobs"), "construction jobs")
    if execution.get("result_order") != "central manifest order, N then L per task":
        raise BenchmarkToolError("construction promotion has the wrong result order")

    required_isolation = {
        "condition_l_numstability_mounts_configured": True,
        "condition_n_numstability_mounts_configured": False,
        "condition_n_preflight_after_complete_controlled_staging": True,
        "controlled_task_staged_under": "task/",
        "fresh_workspace_per_result": True,
        "private_gold_staged_as": "Submission.lean",
        "private_helper_oleans_reused": False,
        "validator_hidden_rebuild": True,
    }
    isolation = _manifest_mapping(evidence.get("isolation"), "construction isolation")
    if dict(isolation) != required_isolation:
        raise BenchmarkToolError("construction promotion lacks its required isolation controls")

    basis = _manifest_mapping(
        evidence.get("verification_basis"), "construction verification basis"
    )
    expected_basis = verification_basis(environment)
    tools = _manifest_mapping(basis.get("tools"), "construction tool digests")
    if set(tools) != set(CONSTRUCTION_TOOL_RELATIVES):
        raise BenchmarkToolError("construction promotion has the wrong validator tool set")
    for relative in CONSTRUCTION_TOOL_RELATIVES:
        expected = sha256_file(
            _required_file(root / relative, f"current construction tool {relative}")
        )
        if _hex_digest(tools.get(relative), f"construction tool {relative}") != expected:
            raise BenchmarkToolError(
                f"construction tool changed after certification: {relative}"
            )
    if dict(basis) != expected_basis:
        raise BenchmarkToolError(
            "construction verification basis does not exactly match the current environment"
        )

    controlled_hashes = _current_controlled_manifest_hashes(root, specs)
    raw_results = _manifest_list(evidence.get("results"), "construction results")
    if len(raw_results) != EXPECTED_FULL_RESULT_COUNT:
        raise BenchmarkToolError("construction promotion requires exactly 120 results")
    n_preflights = 0
    l_library_dependencies = 0
    for index, (raw_result, spec) in enumerate(zip(raw_results, specs, strict=True)):
        result = _manifest_mapping(raw_result, f"construction result {index}")
        expected_identity = {
            "task_id": spec.task_id,
            "paper_id": spec.paper_id,
            "tier": spec.tier,
            "condition": spec.condition,
            "target_theorem": spec.target_theorem,
        }
        if any(result.get(field) != value for field, value in expected_identity.items()):
            raise BenchmarkToolError(
                f"construction result {index} does not match central-manifest N/L order"
            )
        if (
            result.get("pass") is not True
            or result.get("reasons") != []
            or result.get("manifest_sha256") != controlled_hashes[spec.task_id]
        ):
            raise BenchmarkToolError(
                f"construction result {spec.task_id}/{spec.condition} is failed or stale"
            )
        _hex_digest(
            result.get("gold_source_sha256"),
            f"construction result {spec.task_id}/{spec.condition} gold proof",
        )
        n_ok, l_ok = _validate_validation_summary(
            result,
            condition=spec.condition,
            target_theorem=spec.target_theorem,
        )
        n_preflights += int(n_ok)
        l_library_dependencies += int(l_ok)
    if (
        n_preflights != EXPECTED_FULL_TASK_COUNT
        or l_library_dependencies != EXPECTED_FULL_TASK_COUNT
    ):
        raise BenchmarkToolError(
            "construction promotion requires 60 N preflights and 60 L library dependencies"
        )
    return {
        "paper_count": len(paper_ids),
        "task_count": len(task_ids),
        "result_count": len(raw_results),
        "condition_n_preflight_count": n_preflights,
        "condition_l_library_dependency_count": l_library_dependencies,
        "central_manifest_sha256": sha256_file(central_manifest),
        "controlled_manifest_sha256": controlled_hashes,
    }


def _construction_pointer_documents(certificate_sha256: str) -> dict[Path, dict[str, Any]]:
    return {
        CONDITION_N_POINTER_RELATIVE: {
            "schema_version": SCHEMA_VERSION,
            "kind": "highambench-condition-n-preflight-evidence-pointer",
            "status": "current complete-corpus construction evidence",
            "current_evidence": CURRENT_CONSTRUCTION_EVIDENCE_PROJECT_PATH,
            "current_evidence_sha256": certificate_sha256,
            "reason": (
                "The complete construction record contains one fresh N preflight for "
                "each of all sixty tasks. Each preflight scans the fully staged "
                "controlled task before private proof material is copied, verifies "
                "the controlled manifest, and confirms with a real Lean import probe "
                "that NumStability is unavailable."
            ),
            "current_result": {
                "condition_n_tasks_checked": EXPECTED_FULL_TASK_COUNT,
                "complete_staged_task_scans_passed": EXPECTED_FULL_TASK_COUNT,
                "reliable_failed_import_probes": EXPECTED_FULL_TASK_COUNT,
                "filesystem_leaks": 0,
            },
        },
        LIBRARY_DEPENDENCY_POINTER_RELATIVE: {
            "schema_version": SCHEMA_VERSION,
            "kind": "highambench-library-dependency-evidence-pointer",
            "status": "current complete-corpus construction evidence",
            "current_evidence": CURRENT_CONSTRUCTION_EVIDENCE_PROJECT_PATH,
            "current_evidence_sha256": certificate_sha256,
            "reason": (
                "The current evidence rebuilds and audits every T1, T2, and T3 proof "
                "in both N and L against the complete sixty-task construction snapshot."
            ),
            "current_result": {
                "proofs_checked": EXPECTED_FULL_RESULT_COUNT,
                "proofs_passed": EXPECTED_FULL_RESULT_COUNT,
                "condition_n_library_use": False,
                "condition_l_passed_proofs_using_numstability": EXPECTED_FULL_TASK_COUNT,
                "dependency_audit_format": 2,
                "forbidden_dependencies": 0,
            },
        },
    }


def _stage_promotion_payload(path: Path, payload: bytes, *, mode: int) -> Path:
    with tempfile.NamedTemporaryFile(
        prefix=f".{path.name}.promote-",
        dir=path.parent,
        delete=False,
    ) as stream:
        temporary = Path(stream.name)
        stream.write(payload)
        stream.flush()
        os.fsync(stream.fileno())
    os.chmod(temporary, mode)
    return temporary


def _replace_promoted_documents(payloads: Mapping[Path, bytes]) -> None:
    """Stage every payload first, then replace all destinations with rollback."""

    if not payloads:
        raise BenchmarkToolError("construction promotion has no documents")
    raw_parents = {path.parent for path in payloads}
    if len(raw_parents) != 1:
        raise BenchmarkToolError("construction promotion documents must share one directory")
    raw_evidence_dir = next(iter(raw_parents))
    if raw_evidence_dir.is_symlink() or not raw_evidence_dir.is_dir():
        raise BenchmarkToolError("construction evidence directory is missing or unsafe")
    evidence_dir = raw_evidence_dir.resolve()

    staged: dict[Path, Path] = {}
    backups: dict[Path, Path | None] = {}
    replaced: list[Path] = []
    try:
        for destination, payload in payloads.items():
            if destination.parent.resolve() != evidence_dir:
                raise BenchmarkToolError("construction promotion destination escapes evidence directory")
            if destination.is_symlink():
                raise BenchmarkToolError(
                    f"construction promotion destination may not be a symlink: {destination}"
                )
            if destination.exists() and not destination.is_file():
                raise BenchmarkToolError(
                    f"construction promotion destination is not a regular file: {destination}"
                )
            mode = destination.stat().st_mode & 0o777 if destination.exists() else 0o644
            staged[destination] = _stage_promotion_payload(
                destination, payload, mode=mode
            )
            backups[destination] = (
                _stage_promotion_payload(
                    destination,
                    destination.read_bytes(),
                    mode=mode,
                )
                if destination.exists()
                else None
            )

        for destination in payloads:
            if destination.is_symlink() or (
                destination.exists() and not destination.is_file()
            ):
                raise BenchmarkToolError(
                    f"construction promotion destination changed while staging: {destination}"
                )
            os.replace(staged[destination], destination)
            replaced.append(destination)
        directory_fd = os.open(evidence_dir, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)
    except Exception as error:
        rollback_errors: list[str] = []
        for destination in reversed(replaced):
            backup = backups.get(destination)
            try:
                if backup is None:
                    destination.unlink(missing_ok=True)
                else:
                    os.replace(backup, destination)
                    backups[destination] = None
            except OSError as rollback_error:
                rollback_errors.append(f"{destination}: {rollback_error}")
        if rollback_errors:
            raise BenchmarkToolError(
                "construction promotion failed and rollback was incomplete: "
                + "; ".join(rollback_errors)
            ) from error
        if isinstance(error, BenchmarkToolError):
            raise
        raise BenchmarkToolError(f"construction promotion failed: {error}") from error
    finally:
        for temporary in (*staged.values(), *(item for item in backups.values() if item)):
            temporary.unlink(missing_ok=True)


def _reject_duplicate_json_keys(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def promote_current_evidence(
    environment: ConstructionEnvironment, candidate_path: Path
) -> dict[str, Any]:
    """Validate and transactionally promote one complete construction certificate."""

    candidate = Path(candidate_path)
    if candidate.is_symlink() or not candidate.is_file():
        raise BenchmarkToolError(
            "construction promotion candidate must be a regular non-symlink file"
        )
    root = Path(environment.benchmark_root).resolve()
    metadata_dir = root / "metadata"
    evidence_dir = metadata_dir / "evidence"
    if metadata_dir.is_symlink() or evidence_dir.is_symlink():
        raise BenchmarkToolError(
            "construction promotion metadata paths may not contain symlinked directories"
        )
    destinations = (
        root / CURRENT_CONSTRUCTION_EVIDENCE_RELATIVE,
        root / CONDITION_N_POINTER_RELATIVE,
        root / LIBRARY_DEPENDENCY_POINTER_RELATIVE,
    )
    resolved_candidate = candidate.resolve()
    if resolved_candidate in {path.resolve() for path in destinations}:
        raise BenchmarkToolError(
            "construction promotion candidate must be a separate temporary file"
        )
    try:
        raw = candidate.read_bytes()
        evidence = json.loads(
            raw.decode("utf-8"), object_pairs_hook=_reject_duplicate_json_keys
        )
    except (OSError, UnicodeDecodeError, json.JSONDecodeError, ValueError) as error:
        raise BenchmarkToolError(
            f"construction promotion candidate is invalid JSON: {error}"
        ) from error
    certificate = _manifest_mapping(evidence, "construction promotion candidate")
    validation = validate_current_construction_evidence(environment, certificate)
    certificate_payload = _canonical_json_bytes(certificate)
    certificate_sha256 = hashlib.sha256(certificate_payload).hexdigest()
    pointer_documents = _construction_pointer_documents(certificate_sha256)
    payloads = {
        destinations[0]: certificate_payload,
        destinations[1]: _canonical_json_bytes(
            pointer_documents[CONDITION_N_POINTER_RELATIVE]
        ),
        destinations[2]: _canonical_json_bytes(
            pointer_documents[LIBRARY_DEPENDENCY_POINTER_RELATIVE]
        ),
    }
    _replace_promoted_documents(payloads)
    return {
        "status": "current_final",
        "certificate_path": CURRENT_CONSTRUCTION_EVIDENCE_RELATIVE.as_posix(),
        "certificate_sha256": certificate_sha256,
        "pointer_paths": [
            CONDITION_N_POINTER_RELATIVE.as_posix(),
            LIBRARY_DEPENDENCY_POINTER_RELATIVE.as_posix(),
        ],
        **validation,
    }


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve().parents[1]
    parser.add_argument("--project-root", type=Path, required=True)
    parser.add_argument("--benchmark-root", type=Path, default=here)
    parser.add_argument(
        "--private-gold",
        "--private-gold-root",
        dest="private_gold",
        type=Path,
        required=True,
        help=(
            "private_gold root containing one directory per selected paper; a "
            "direct paper directory is accepted for a single-paper check"
        ),
    )
    parser.add_argument(
        "--paper-id",
        action="append",
        help=(
            "limit the construction check to this paper id (repeatable); omitting "
            "the option requires gold material for every manifest-available task"
        ),
    )
    parser.add_argument("--toolchain-root", type=Path, required=True)
    parser.add_argument("--packages-root", type=Path, required=True)
    parser.add_argument("--shared-olean-root", type=Path, required=True)
    parser.add_argument("--library-source", type=Path, required=True)
    parser.add_argument("--library-root-file", type=Path, required=True)
    parser.add_argument("--library-olean", type=Path, required=True)
    parser.add_argument("--hidden-parent", type=Path)
    parser.add_argument("--bwrap", type=Path, default=Path("/bin/bwrap"))
    parser.add_argument("--shared-root-relative", default="task/shared")
    parser.add_argument("--timeout-seconds", type=float, default=180.0)
    parser.add_argument(
        "--jobs",
        type=int,
        default=1,
        help="number of independent construction workspaces to validate concurrently",
    )
    parser.add_argument("--output", type=Path)
    parser.add_argument(
        "--promote-current",
        action="store_true",
        help=(
            "after a successful complete 20-paper/60-task check written to a "
            "separate --output file, independently authenticate and transactionally "
            "promote its 120/120 certificate plus both derived evidence pointers"
        ),
    )
    return parser


def _requested_scope(args: argparse.Namespace) -> dict[str, Any]:
    """Describe the requested manifest scope even if material resolution fails."""

    benchmark_root = _required_directory(args.benchmark_root, "benchmark root")
    all_specs = construction_specs(benchmark_root)
    selected_specs = (
        all_specs
        if not args.paper_id
        else construction_specs(benchmark_root, paper_ids=args.paper_id)
    )
    return _scope_record(
        central_manifest=_required_file(
            benchmark_root / CENTRAL_MANIFEST_RELATIVE,
            "central benchmark manifest",
        ),
        manifest_task_ids=_task_ids(all_specs),
        manifest_paper_ids=_paper_ids(all_specs),
        selected_specs=selected_specs,
        selected_paper_ids=_paper_ids(selected_specs),
    )


def main() -> int:
    args = make_parser().parse_args()
    if args.timeout_seconds <= 0:
        print("construction-check error: timeout must be positive", file=sys.stderr)
        return 2
    if args.jobs <= 0:
        print("construction-check error: jobs must be positive", file=sys.stderr)
        return 2
    if args.promote_current:
        if args.output is None:
            print(
                "construction-check error: --promote-current requires a separate --output file",
                file=sys.stderr,
            )
            return 2
        if args.paper_id:
            print(
                "construction-check error: --promote-current forbids partial --paper-id checks",
                file=sys.stderr,
            )
            return 2
        output = Path(args.output)
        if output.is_symlink() or output.exists():
            print(
                "construction-check error: promoted --output must be a new non-symlink file",
                file=sys.stderr,
            )
            return 2
        parent = output.parent
        if parent.is_symlink() or not parent.is_dir():
            print(
                "construction-check error: promoted --output parent must be an existing non-symlink directory",
                file=sys.stderr,
            )
            return 2
    try:
        environment = resolve_environment(args)
        evidence = run_checks(environment, jobs=args.jobs)
    except (OSError, BenchmarkToolError, ValueError) as error:
        evidence = {
            "schema_version": 1,
            "kind": "highambench-private-construction-check",
            "generated_at_utc": utc_now(),
            "pass": False,
            "configuration_error": str(error),
        }
        try:
            evidence["scope"] = _requested_scope(args)
        except (OSError, BenchmarkToolError, ValueError):
            # The configuration error itself may be a missing or malformed
            # central manifest, in which case no trustworthy scope exists.
            pass
        if args.output:
            write_json(args.output, evidence)
        else:
            print(json.dumps(evidence, indent=2, sort_keys=True))
        return 2
    if args.output:
        write_json(args.output, evidence)
    else:
        print(json.dumps(evidence, indent=2, sort_keys=True))
    if args.promote_current:
        try:
            promoted = promote_current_evidence(environment, args.output)
        except (OSError, BenchmarkToolError, ValueError) as error:
            print(f"construction-check promotion error: {error}", file=sys.stderr)
            return 2
        print(json.dumps({"promotion": promoted}, indent=2, sort_keys=True))
    return 0 if evidence["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
