#!/usr/bin/env python3
"""Validate private construction proofs for manifest-available benchmark tasks.

This command is a release check, not a benchmark run.  It stages only one
released task package in each fresh temporary workspace and copies the matching
private proof to ``Submission.lean``.  The private source directory is never
mounted by either the benchmark agent adapter or the isolated Lean adapter.

The task matrix and theorem names come from ``metadata/manifest.json``.  P01's
T1 and T2 construction proofs import one private helper module; that helper is
copied as source and compiled afresh inside the isolated Lean adapter, so no
private ``.olean`` file is reused.  Every submission then goes through the
normal hidden validator, including its isolated compilation and transitive
dependency audit.
"""

from __future__ import annotations

import argparse
from collections.abc import Iterable, Mapping
from dataclasses import dataclass
import json
from pathlib import Path
import platform
import shutil
import sys
from typing import Any, Callable

try:
    from .common import (
        BenchmarkToolError,
        run_captured,
        sha256_file,
        temporary_directory,
        utc_now,
        write_json,
    )
    from .hashes import load_manifest, stage_manifest_files, verify_manifest
    from .preflight import run_preflight
    from .validator import ValidationConfig, validate
except ImportError:  # Direct script execution.
    from common import (  # type: ignore
        BenchmarkToolError,
        run_captured,
        sha256_file,
        temporary_directory,
        utc_now,
        write_json,
    )
    from hashes import load_manifest, stage_manifest_files, verify_manifest  # type: ignore
    from preflight import run_preflight  # type: ignore
    from validator import ValidationConfig, validate  # type: ignore


P01_HELPERS = {
    "N": ("CommonN.lean", "CommonN", "HighamBench.GoldN.gammaValid_mono"),
    "L": ("CommonL.lean", "CommonL", "HighamBench.GoldL.standardProxy_u"),
}
CENTRAL_MANIFEST_RELATIVE = Path("metadata/manifest.json")

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
    helper_filename: str | None
    helper_module: str | None
    helper_target: str | None


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


def _helper_for(
    paper_id: str, tier: str, condition: str
) -> tuple[str, str, str] | None:
    # Helpers are private proof implementation details, not benchmark metadata.
    # Preserve the established P01 construction layout while allowing later
    # papers to use self-contained proofs by default.
    if paper_id == "P01" and tier in ("T1", "T2"):
        return P01_HELPERS[condition]
    return None


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
                helper = _helper_for(paper_id, tier, condition)
                specs.append(
                    ConstructionSpec(
                        task_id=task_id,
                        paper_id=paper_id,
                        tier=tier,
                        condition=condition,
                        target_theorem=target_theorem,
                        canonical_relative=canonical_relative,
                        gold_filename=f"{tier}_{condition}.lean",
                        helper_filename=helper[0] if helper else None,
                        helper_module=helper[1] if helper else None,
                        helper_target=helper[2] if helper else None,
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
    """Normalize a private-gold root, retaining direct-P01 compatibility."""

    root = _required_directory(private_gold_root, "private gold root")
    if len(selected_paper_ids) == 1 and root.name == selected_paper_ids[0]:
        return root.parent.resolve()
    if root.name in selected_paper_ids:
        raise BenchmarkToolError(
            "a direct paper private-gold directory can only be used when that "
            "single paper is selected"
        )
    return root


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
    # ``measure_validation.py`` predates the selector and is intentionally a
    # P01-only historical measurement.  Namespaces produced by this module's
    # parser always have ``paper_id``; a caller without the attribute keeps the
    # old P01 scope instead of silently expanding that frozen measurement.
    selected_arg = getattr(args, "paper_id", ("P01",))
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
    checked_helpers: set[tuple[str, str]] = set()
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
        if spec.helper_filename is not None:
            helper_key = (spec.paper_id, spec.helper_filename)
            if helper_key not in checked_helpers:
                checked_helpers.add(helper_key)
                helper_path = (
                    private_gold_root / spec.paper_id / spec.helper_filename
                )
                if helper_path.is_symlink() or not helper_path.is_file():
                    missing_material.append(
                        f"{spec.paper_id}/{spec.condition} helper ({helper_path})"
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

    shared_files = _exact_regular_files(environment.shared_olean_root)
    if shared_files != {"HighamBench/Definitions.olean"}:
        raise BenchmarkToolError(
            "shared olean root must contain exactly HighamBench/Definitions.olean"
        )
    shared_olean = environment.shared_olean_root / "HighamBench" / "Definitions.olean"

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
            "relative_file": "HighamBench/Definitions.olean",
            "sha256": sha256_file(shared_olean),
            "exact_file_count": 1,
            "condition_n_absence_scan": _binary_marker_scan(
                environment.shared_olean_root,
                {"HighamBench/Definitions.olean"},
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
        str(environment.shared_olean_root),
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
                    "helper": None,
                    "condition_n_library_arguments_omitted": True,
                    "n_preflight": n_preflight,
                    "validation": None,
                }

        # Private proof material is copied only after the public N-package
        # absence check.  It is never part of what that check scans.
        submission = workspace / "Submission.lean"
        shutil.copy2(gold_path, submission)

        helper_build: dict[str, Any] | None = None
        helper_digest: str | None = None
        local_sources: list[str] = []
        if spec.helper_filename is not None:
            assert spec.helper_module is not None and spec.helper_target is not None
            helper_source = private_paper_root / spec.helper_filename
            staged_helper = workspace / spec.helper_filename
            shutil.copy2(helper_source, staged_helper)
            helper_digest = sha256_file(staged_helper)
            local_sources.append(spec.helper_filename)

            # The adapter's audit action first performs an explicit `lean -o`.
            # We use it here to create the helper olean inside the same N/L
            # namespace that will later compile the submission.  The audit of
            # the helper is an additional check; the normal submission audit
            # still runs below through the validator.
            helper_command = isolated_lean_command(
                environment,
                action="build-audit",
                condition=spec.condition,
                workspace=workspace,
                source=staged_helper,
                submission_module=spec.helper_module,
                target_theorem=spec.helper_target,
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
                    "helper": {
                        "module": spec.helper_module,
                        "source_sha256": helper_digest,
                        "build": helper_build,
                    },
                    "condition_n_library_arguments_omitted": spec.condition == "N",
                    "n_preflight": n_preflight,
                    "validation": None,
                }

        compile_command = isolated_lean_command(
            environment,
            action="olean",
            condition=spec.condition,
            workspace="{workspace}",
            source="{checked_submission}",
        )
        audit_command = isolated_lean_command(
            environment,
            action="audit",
            condition=spec.condition,
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
            "helper": (
                None
                if spec.helper_filename is None
                else {
                    "module": spec.helper_module,
                    "source_sha256": helper_digest,
                    "build": helper_build,
                }
            ),
            "condition_n_library_arguments_omitted": spec.condition == "N",
            "n_preflight": n_preflight,
            "validation": summary,
        }


def run_checks(
    environment: ConstructionEnvironment,
    *,
    command_runner: CommandRunner = run_captured,
    validator_fn: Validator = validate,
    preflight_fn: Preflight = run_preflight,
) -> dict[str, Any]:
    basis = verification_basis(environment)
    results: list[dict[str, Any]] = []
    for spec in environment.specs:
        try:
            result = check_one(
                environment,
                spec,
                command_runner=command_runner,
                validator_fn=validator_fn,
                preflight_fn=preflight_fn,
            )
        except (OSError, BenchmarkToolError, ValueError) as error:
            result = {
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
        results.append(result)

    passed = sum(bool(result.get("pass")) for result in results)
    n_results = [result for result in results if result["condition"] == "N"]
    l_results = [result for result in results if result["condition"] == "L"]
    expected = len(environment.specs)
    return {
        "schema_version": 1,
        "kind": "highambench-private-construction-check",
        "generated_at_utc": utc_now(),
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
    parser.add_argument("--output", type=Path)
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
    try:
        environment = resolve_environment(args)
        evidence = run_checks(environment)
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
    return 0 if evidence["pass"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
