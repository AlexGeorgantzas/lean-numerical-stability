#!/usr/bin/env python3
"""Validate private construction proofs for manifest-available benchmark tasks.

This command is a release check, not a benchmark run.  It stages only one
released task package in each fresh temporary workspace and copies the matching
private proof to ``Submission.lean``.  The private source directory is never
mounted by either the benchmark agent adapter or the isolated Lean adapter.

With ``--paper-local-evidence`` and exactly one ``--paper-id``, the task matrix
and theorem/declaration names come only from that paper's ``paper.json`` and
``task.json`` records.  A complete pass publishes an authenticated construction
receipt and refreshes only that paper's registration.  The legacy corpus mode
continues to read ``metadata/manifest.json`` and may publish corpus evidence
only through its separate explicit promotion option.

Any private helper modules imported by a proof are discovered from that paper's
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
        truncate_text,
        utc_now,
        write_json,
    )
    from .hashes import load_manifest, stage_manifest_files, verify_manifest
    from .preflight import MISSING_IMPORT_MARKERS, run_preflight
    from .validator import ValidationConfig, extract_imports, sanitize_lean, validate
    from . import paper_registry
    from .finalize_paper import finalize_paper as finalize_paper_bundle
except ImportError:  # Direct script execution.
    from common import (  # type: ignore
        BenchmarkToolError,
        SCHEMA_VERSION,
        run_captured,
        sha256_file,
        temporary_directory,
        truncate_text,
        utc_now,
        write_json,
    )
    from hashes import load_manifest, stage_manifest_files, verify_manifest  # type: ignore
    from preflight import MISSING_IMPORT_MARKERS, run_preflight  # type: ignore
    from validator import (  # type: ignore
        ValidationConfig,
        extract_imports,
        sanitize_lean,
        validate,
    )
    import paper_registry  # type: ignore
    from finalize_paper import finalize_paper as finalize_paper_bundle  # type: ignore


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
T4_TASK_SCHEMA_VERSION = "highambench-task-0.4"
PRIVATE_PROOF_KIND = "private-proof"
T4_SKELETON_KIND = "designated-hole-skeleton"
T4_PRIVATE_PROOF_KIND = "t4-private-proof"

CONSTRUCTION_TOOL_RELATIVES = (
    "tools/check_construction.py",
    "tools/common.py",
    "tools/hashes.py",
    "tools/lean_isolated.py",
    "tools/preflight.py",
    "tools/validator.py",
    "tools/dependency_audit.lean",
)
PAPER_LOCAL_TOOL_RELATIVES = (
    "tools/finalize_paper.py",
    "tools/paper_registry.py",
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
class ControlledSorry:
    placeholder_id: str
    declaration_id: str
    lean_name: str
    marker: str
    line: int
    column: int


@dataclass(frozen=True)
class ControlledDeclarationSource:
    lean_name: str
    source_file: str
    source_line: int


@dataclass(frozen=True)
class ConstructionSpec:
    task_id: str
    paper_id: str
    tier: str
    condition: str
    target_theorem: str | None
    canonical_relative: str
    gold_filename: str | None
    construction_kind: str = PRIVATE_PROOF_KIND
    required_declarations: tuple[str, ...] = ()
    controlled_declaration_sources: tuple[ControlledDeclarationSource, ...] = ()
    controlled_sorries: tuple[ControlledSorry, ...] = ()


@dataclass(frozen=True)
class ConstructionEnvironment:
    project_root: Path
    benchmark_root: Path
    private_gold_root: Path | None
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
    paper_local: bool = False


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


def _controlled_source_relative(value: str, *, task_id: str) -> str:
    """Normalize one task-record controlled owner to benchmark-root-relative form."""

    source = Path(value)
    prefix = Path("paper_bencmark/highambench")
    if source.is_absolute() or source.as_posix() != value:
        raise BenchmarkToolError(
            f"{task_id} controlled declaration source is not canonical: {value}"
        )
    try:
        relative = source.relative_to(prefix)
    except ValueError as error:
        raise BenchmarkToolError(
            f"{task_id} controlled declaration source is outside the benchmark: {value}"
        ) from error
    if any(part in ("", ".", "..") for part in relative.parts):
        raise BenchmarkToolError(
            f"{task_id} controlled declaration source escapes its root: {value}"
        )
    return relative.as_posix()


def _t4_construction_metadata(
    root: Path,
    *,
    paper_id: str,
    task_id: str,
    canonical_relative: str,
    lean_target: Mapping[str, Any],
) -> tuple[
    tuple[str, ...],
    tuple[ControlledDeclarationSource, ...],
    tuple[ControlledSorry, ...],
]:
    """Load the plural declaration and designated-hole contract for one T4 task."""

    task_path = root / "tasks" / paper_id / "T4" / "task.json"
    if task_path.is_symlink() or not task_path.is_file():
        raise BenchmarkToolError(f"{task_id} has no regular schema-0.4 task record")
    try:
        task_value = json.loads(task_path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise BenchmarkToolError(f"{task_id} task record is unreadable: {error}") from error
    task = _manifest_mapping(task_value, f"{task_id} task record")
    if (
        task.get("schema_version") != T4_TASK_SCHEMA_VERSION
        or task.get("task_id") != task_id
        or task.get("paper_id") != paper_id
        or task.get("tier") != "T4"
    ):
        raise BenchmarkToolError(f"{task_id} is not a matching schema-0.4 T4 task")

    validation = _manifest_mapping(
        task.get("validation"), f"{task_id} validation"
    )
    controlled_target = _manifest_string(
        validation.get("controlled_target_file"),
        f"{task_id} controlled target file",
    )
    if _canonical_target_relative(
        controlled_target, paper_id=paper_id, tier="T4"
    ) != canonical_relative:
        raise BenchmarkToolError(
            f"{task_id} controlled target file disagrees with the manifest"
        )

    raw_required = _manifest_list(
        validation.get("required_declarations"),
        f"{task_id} required declarations",
    )
    required = tuple(
        _manifest_string(value, f"{task_id} required declaration {index}")
        for index, value in enumerate(raw_required)
    )
    if not required or len(set(required)) != len(required):
        raise BenchmarkToolError(
            f"{task_id} required declarations must be nonempty and unique"
        )
    raw_declarations = _manifest_list(
        task.get("declarations"), f"{task_id} declarations"
    )
    declaration_names: list[str] = []
    declaration_sources: list[ControlledDeclarationSource] = []
    for index, value in enumerate(raw_declarations):
        declaration = _manifest_mapping(value, f"{task_id} declaration {index}")
        lean_name = _manifest_string(
            declaration.get("lean_name"),
            f"{task_id} declaration {index} Lean name",
        )
        source_file = _controlled_source_relative(
            _manifest_string(
                declaration.get("controlled_source_file"),
                f"{task_id} declaration {index} controlled source file",
            ),
            task_id=task_id,
        )
        source_line = declaration.get("controlled_source_line")
        if type(source_line) is not int or source_line <= 0:
            raise BenchmarkToolError(
                f"{task_id} declaration {index} has an invalid controlled source line"
            )
        declaration_names.append(lean_name)
        declaration_sources.append(
            ControlledDeclarationSource(
                lean_name=lean_name,
                source_file=source_file,
                source_line=source_line,
            )
        )
    declaration_names_tuple = tuple(declaration_names)
    if declaration_names_tuple != required:
        raise BenchmarkToolError(
            f"{task_id} required declarations do not match declaration order"
        )

    for field in ("declarations", "required_declarations"):
        if field not in lean_target:
            continue
        raw_manifest_names = _manifest_list(
            lean_target.get(field), f"central manifest {task_id} {field}"
        )
        manifest_names = tuple(
            _manifest_string(
                value, f"central manifest {task_id} {field} {index}"
            )
            for index, value in enumerate(raw_manifest_names)
        )
        if manifest_names != required:
            raise BenchmarkToolError(
                f"central manifest {task_id} {field} disagrees with task.json"
            )
    if lean_target.get("declaration") is not None:
        raise BenchmarkToolError(
            f"central manifest {task_id} must not squeeze T4 into singular declaration"
        )

    raw_sorries = _manifest_list(
        validation.get("controlled_sorries"), f"{task_id} controlled sorries"
    )
    sorries: list[ControlledSorry] = []
    for index, raw_sorry in enumerate(raw_sorries, start=1):
        sorry = _manifest_mapping(raw_sorry, f"{task_id} controlled sorry {index}")
        line = sorry.get("line")
        column = sorry.get("column")
        if (
            sorry.get("placeholder_order") != index
            or type(line) is not int
            or line <= 0
            or type(column) is not int
            or column <= 0
        ):
            raise BenchmarkToolError(
                f"{task_id} controlled sorry {index} has invalid order/location"
            )
        placeholder_id = _manifest_string(
            sorry.get("placeholder_id"),
            f"{task_id} controlled sorry {index} placeholder",
        )
        marker = _manifest_string(
            sorry.get("marker"), f"{task_id} controlled sorry {index} marker"
        )
        if marker != f"-- PROOF_START {placeholder_id}":
            raise BenchmarkToolError(
                f"{task_id} controlled sorry {index} has a noncanonical marker"
            )
        sorries.append(
            ControlledSorry(
                placeholder_id=placeholder_id,
                declaration_id=_manifest_string(
                    sorry.get("declaration_id"),
                    f"{task_id} controlled sorry {index} declaration ID",
                ),
                lean_name=_manifest_string(
                    sorry.get("lean_name"),
                    f"{task_id} controlled sorry {index} Lean name",
                ),
                marker=marker,
                line=line,
                column=column,
            )
        )
    if not sorries or len({item.placeholder_id for item in sorries}) != len(sorries):
        raise BenchmarkToolError(
            f"{task_id} controlled sorries must be nonempty and unique"
        )
    if any(item.lean_name not in required for item in sorries):
        raise BenchmarkToolError(
            f"{task_id} controlled sorry names an unknown required declaration"
        )
    proof_names = {item.lean_name for item in sorries}
    if any(
        source.lean_name in proof_names
        and source.source_file != canonical_relative
        for source in declaration_sources
    ):
        raise BenchmarkToolError(
            f"{task_id} proof declarations must be owned by the canonical target"
        )
    return required, tuple(declaration_sources), tuple(sorries)


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
            target_file = _manifest_string(
                lean_target.get("file"), f"central manifest {task_id} target file"
            )
            canonical_relative = _canonical_target_relative(
                target_file, paper_id=paper_id, tier=tier
            )
            if requested is not None and paper_id not in requested:
                continue

            construction_kind = PRIVATE_PROOF_KIND
            target_theorem: str | None
            gold_filename: str | None
            required_declarations: tuple[str, ...]
            controlled_declaration_sources: tuple[ControlledDeclarationSource, ...]
            controlled_sorries: tuple[ControlledSorry, ...]
            if tier == "T4":
                (
                    required_declarations,
                    controlled_declaration_sources,
                    controlled_sorries,
                ) = _t4_construction_metadata(
                    root,
                    paper_id=paper_id,
                    task_id=task_id,
                    canonical_relative=canonical_relative,
                    lean_target=lean_target,
                )
                construction_kind = T4_PRIVATE_PROOF_KIND
                # The plural validator retains a singular compatibility value
                # for command rendering.  It audits every controlled proof
                # declaration through ``required_declarations`` and
                # ``controlled_sorries`` below.
                target_theorem = controlled_sorries[0].lean_name
                gold_filename = "T4_{condition}.lean"
            else:
                declaration = _manifest_string(
                    lean_target.get("declaration"),
                    f"central manifest {task_id} Lean declaration",
                )
                target_theorem = (
                    declaration
                    if "." in declaration
                    else f"HighamBench.{declaration}"
                )
                gold_filename = f"{tier}_{{condition}}.lean"
                required_declarations = (target_theorem,)
                controlled_declaration_sources = ()
                controlled_sorries = ()

            for condition in ("N", "L"):
                specs.append(
                    ConstructionSpec(
                        task_id=task_id,
                        paper_id=paper_id,
                        tier=tier,
                        condition=condition,
                        target_theorem=target_theorem,
                        canonical_relative=canonical_relative,
                        gold_filename=(
                            gold_filename.format(condition=condition)
                            if gold_filename is not None
                            else None
                        ),
                        construction_kind=construction_kind,
                        required_declarations=required_declarations,
                        controlled_declaration_sources=(
                            controlled_declaration_sources
                        ),
                        controlled_sorries=controlled_sorries,
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


def _json_mapping_file(path: Path, label: str) -> Mapping[str, Any]:
    if path.is_symlink() or not path.is_file():
        raise BenchmarkToolError(f"{label} must be a regular non-symlink file: {path}")
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, UnicodeDecodeError, json.JSONDecodeError) as error:
        raise BenchmarkToolError(f"{label} is unreadable: {error}") from error
    return _manifest_mapping(value, label)


def paper_construction_specs(
    benchmark_root: Path, paper_id: str
) -> list[ConstructionSpec]:
    """Discover one complete N/L matrix only from that paper's owned records."""

    root = Path(benchmark_root).resolve()
    if re.fullmatch(r"P[0-9]+", paper_id) is None:
        raise BenchmarkToolError(f"invalid paper id: {paper_id!r}")
    paper_root = root / "tasks" / paper_id
    if paper_root.is_symlink() or not paper_root.is_dir():
        raise BenchmarkToolError(f"paper task root is missing or unsafe: {paper_root}")
    paper = _json_mapping_file(
        paper_root / "paper.json", f"{paper_id} paper record"
    )
    if paper.get("paper_id") != paper_id:
        raise BenchmarkToolError(f"{paper_id} paper record has the wrong paper_id")
    frozen = paper.get("classification_frozen_before_runs")
    if not isinstance(frozen, bool):
        raise BenchmarkToolError(
            f"{paper_id} classification_frozen_before_runs must be boolean"
        )
    raw_included = _manifest_list(
        paper.get("included_tasks"), f"{paper_id} included_tasks"
    )
    included = tuple(
        _manifest_string(item, f"{paper_id} included task {index}")
        for index, item in enumerate(raw_included)
    )
    tier_directories = sorted(
        (
            path
            for path in paper_root.iterdir()
            if path.is_dir() and re.fullmatch(r"T[0-9]+", path.name)
        ),
        key=lambda path: (int(path.name[1:]), path.name),
    )
    expected_included = tuple(f"{paper_id}-{path.name}" for path in tier_directories)
    if not expected_included or included != expected_included:
        raise BenchmarkToolError(
            f"{paper_id} included_tasks must exactly match its task directories: "
            f"{list(expected_included)}"
        )

    specs: list[ConstructionSpec] = []
    for task_id, task_root in zip(included, tier_directories, strict=True):
        tier = task_root.name
        task = _json_mapping_file(task_root / "task.json", f"{task_id} task record")
        if (
            task.get("task_id") != task_id
            or task.get("paper_id") != paper_id
            or task.get("tier") != tier
            or task.get("classification_frozen_before_runs") is not frozen
        ):
            raise BenchmarkToolError(f"{task_id} identity/readiness disagrees with its path")
        target = task_root / "Target.lean"
        if target.is_symlink() or not target.is_file():
            raise BenchmarkToolError(f"{task_id} target is missing or unsafe")
        canonical_relative = f"tasks/{paper_id}/{tier}/Target.lean"
        validation = _manifest_mapping(task.get("validation"), f"{task_id} validation")
        controlled_target = _manifest_string(
            validation.get("controlled_target_file"),
            f"{task_id} controlled target file",
        )
        if _canonical_target_relative(
            controlled_target, paper_id=paper_id, tier=tier
        ) != canonical_relative:
            raise BenchmarkToolError(
                f"{task_id} controlled target does not match its paper-owned path"
            )

        if tier == "T4":
            (
                required_declarations,
                declaration_sources,
                controlled_sorries,
            ) = _t4_construction_metadata(
                root,
                paper_id=paper_id,
                task_id=task_id,
                canonical_relative=canonical_relative,
                lean_target={},
            )
            target_theorem = controlled_sorries[0].lean_name
            construction_kind = T4_PRIVATE_PROOF_KIND
            gold_pattern = "T4_{condition}.lean"
        else:
            declaration = _manifest_string(
                validation.get("required_declaration"),
                f"{task_id} required declaration",
            )
            target_theorem = (
                declaration if "." in declaration else f"HighamBench.{declaration}"
            )
            required_declarations = (target_theorem,)
            declaration_sources = ()
            controlled_sorries = ()
            construction_kind = PRIVATE_PROOF_KIND
            gold_pattern = f"{tier}_{{condition}}.lean"

        for condition in ("N", "L"):
            specs.append(
                ConstructionSpec(
                    task_id=task_id,
                    paper_id=paper_id,
                    tier=tier,
                    condition=condition,
                    target_theorem=target_theorem,
                    canonical_relative=canonical_relative,
                    gold_filename=gold_pattern.format(condition=condition),
                    construction_kind=construction_kind,
                    required_declarations=required_declarations,
                    controlled_declaration_sources=declaration_sources,
                    controlled_sorries=controlled_sorries,
                )
            )
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


def _controlled_sorry_records(spec: ConstructionSpec) -> list[dict[str, Any]]:
    return [
        {
            "placeholder_order": index,
            "placeholder_id": item.placeholder_id,
            "declaration_id": item.declaration_id,
            "lean_name": item.lean_name,
            "marker": item.marker,
            "line": item.line,
            "column": item.column,
        }
        for index, item in enumerate(spec.controlled_sorries, start=1)
    ]


def _controlled_declaration_source_records(
    spec: ConstructionSpec,
) -> list[dict[str, Any]]:
    return [
        {
            "lean_name": item.lean_name,
            "controlled_source_file": item.source_file,
            "controlled_source_line": item.source_line,
        }
        for item in spec.controlled_declaration_sources
    ]


def _controlled_manifest_path(
    environment: ConstructionEnvironment, spec: ConstructionSpec
) -> Path:
    if environment.paper_local:
        return (
            environment.benchmark_root
            / "metadata"
            / "papers"
            / spec.paper_id
            / "controlled"
            / f"{spec.tier}.json"
        )
    return (
        environment.benchmark_root
        / "metadata"
        / "controlled"
        / f"{spec.task_id}.json"
    )


def _paper_scope_record(environment: ConstructionEnvironment) -> dict[str, Any]:
    paper_id = environment.selected_paper_ids[0]
    paper_record = environment.benchmark_root / "tasks" / paper_id / "paper.json"
    return {
        "scope_kind": "paper-local",
        "paper_id": paper_id,
        "paper_record": f"tasks/{paper_id}/paper.json",
        "paper_record_sha256": sha256_file(paper_record),
        "task_ids": list(_task_ids(environment.specs)),
        "complete_paper_scope": True,
    }


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
    selected_arg = getattr(args, "paper_id", None)
    paper_local = bool(getattr(args, "paper_local_evidence", False))
    if paper_local:
        if not selected_arg or len(selected_arg) != 1:
            raise BenchmarkToolError(
                "--paper-local-evidence requires exactly one --paper-id P0X"
            )
        paper_id = str(selected_arg[0])
        specs = paper_construction_specs(benchmark_root, paper_id)
        all_specs = specs
        selected_paper_ids = (paper_id,)
        manifest_paper_ids = selected_paper_ids
        scope_source = _required_file(
            benchmark_root / "tasks" / paper_id / "paper.json",
            f"{paper_id} paper record",
        )
    else:
        all_specs = construction_specs(benchmark_root)
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
        scope_source = _required_file(
            benchmark_root / CENTRAL_MANIFEST_RELATIVE,
            "central benchmark manifest",
        )
    proof_paper_ids = _paper_ids(
        spec
        for spec in specs
        if spec.construction_kind in (PRIVATE_PROOF_KIND, T4_PRIVATE_PROOF_KIND)
    )
    private_gold_root: Path | None = None
    if proof_paper_ids:
        if args.private_gold is None:
            raise BenchmarkToolError(
                "private gold root is required when selected tasks exist"
            )
        private_gold_root = _private_gold_root(args.private_gold, proof_paper_ids)
    hidden_parent: Path | None = None
    if args.hidden_parent is not None:
        args.hidden_parent.mkdir(parents=True, exist_ok=True)
        hidden_parent = _required_directory(args.hidden_parent, "hidden workspace parent")

    environment = ConstructionEnvironment(
        project_root=project_root,
        benchmark_root=benchmark_root,
        private_gold_root=private_gold_root,
        central_manifest=scope_source,
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
        paper_local=paper_local,
    )

    missing_material: list[str] = []
    for spec in specs:
        _required_file(
            _controlled_manifest_path(environment, spec),
            f"{spec.task_id} controlled manifest",
        )
        if private_gold_root is None or spec.gold_filename is None:
            raise BenchmarkToolError(
                f"{spec.task_id}/{spec.condition} has no private proof configuration"
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


def _paper_local_bundle_basis(
    environment: ConstructionEnvironment,
) -> tuple[dict[str, dict[str, str]], set[str], dict[str, Any]]:
    """Authenticate exactly one paper-owned bundle without corpus metadata."""

    if len(environment.selected_paper_ids) != 1:
        raise BenchmarkToolError(
            "paper-local bundle authentication requires exactly one selected paper"
        )
    paper_id = environment.selected_paper_ids[0]
    if environment.manifest_paper_ids != (paper_id,):
        raise BenchmarkToolError(
            "paper-local bundle authentication must not include sibling papers"
        )
    source = _required_file(
        environment.benchmark_root
        / "shared"
        / "HighamBench"
        / f"{paper_id}Definitions.lean",
        f"{paper_id} definitions",
    )
    definition_source = {
        "path": f"shared/HighamBench/{paper_id}Definitions.lean",
        "sha256": sha256_file(source),
        "bytes": source.stat().st_size,
    }
    artifact = paper_registry._validate_bundle_receipt(  # noqa: SLF001
        environment.benchmark_root,
        paper_id=paper_id,
        definition_source=definition_source,
    )
    if artifact.get("status") != "authenticated":
        raise BenchmarkToolError(
            f"{paper_id} has no authenticated paper-local bundle receipt"
        )
    raw_olean = _manifest_mapping(
        _manifest_list(artifact.get("olean_files"), f"{paper_id} bundle oleans")[0],
        f"{paper_id} bundle olean",
    )
    relative = _manifest_string(raw_olean.get("path"), f"{paper_id} bundle olean path")
    bundle_root = environment.shared_olean_root / paper_id
    actual_files = _exact_regular_files(bundle_root)
    if actual_files != {relative}:
        raise BenchmarkToolError(
            f"shared olean bundle {paper_id} is not the exact one-file paper bundle "
            f"(extra={sorted(actual_files - {relative})}, "
            f"missing={sorted({relative} - actual_files)})"
        )
    olean = _required_file(bundle_root / relative, f"{paper_id} definitions olean")
    expected_hash = _hex_digest(raw_olean.get("sha256"), f"{paper_id} bundle olean")
    expected_bytes = raw_olean.get("bytes")
    if (
        sha256_file(olean) != expected_hash
        or type(expected_bytes) is not int
        or expected_bytes < 0
        or olean.stat().st_size != expected_bytes
    ):
        raise BenchmarkToolError(f"{paper_id} bundle olean hash/size is stale")
    bundled_relative = f"{paper_id}/{relative}"
    return (
        {paper_id: {relative: expected_hash}},
        {bundled_relative},
        _manifest_mapping(artifact.get("receipt"), f"{paper_id} bundle receipt"),
    )


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

    if environment.paper_local:
        (
            shared_olean_bundles,
            expected_shared_files,
            bundle_receipt,
        ) = _paper_local_bundle_basis(environment)
        shared_absence_scan = _binary_marker_scan(
            environment.shared_olean_root, expected_shared_files
        )
        if not shared_absence_scan["ok"]:
            raise BenchmarkToolError(
                "paper-local shared olean leaks a condition-N marker: "
                f"{shared_absence_scan['matches'][:8]}"
            )
        tool_hashes: dict[str, str] = {}
        for relative in (*CONSTRUCTION_TOOL_RELATIVES, *PAPER_LOCAL_TOOL_RELATIVES):
            path = _required_file(
                environment.benchmark_root / relative,
                f"paper-local construction tool {relative}",
            )
            tool_hashes[relative] = sha256_file(path)
        paper_id = environment.selected_paper_ids[0]
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
                "bundle_receipts": {paper_id: bundle_receipt},
                "exact_file_count": len(expected_shared_files),
                "condition_n_absence_scan": shared_absence_scan,
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
    bundle_paper_ids = environment.selected_paper_ids
    expected_shared_files: set[str] = set()
    expected_local_files: dict[str, set[str]] = {
        paper_id: set() for paper_id in bundle_paper_ids
    }
    shared_olean_bundles: dict[str, dict[str, str]] = {}
    for paper_id in bundle_paper_ids:
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
            expected_local_files[paper_id].add(relative)
            actual = sha256_file(environment.shared_olean_root / bundled_relative)
            if actual != expected:
                raise BenchmarkToolError(
                    f"shared olean {paper_id}/{relative} has the wrong SHA-256"
                )
            bundle_hashes[relative] = actual
        shared_olean_bundles[paper_id] = bundle_hashes
    if bundle_paper_ids == environment.manifest_paper_ids:
        shared_files = _exact_regular_files(environment.shared_olean_root)
        if shared_files != expected_shared_files:
            raise BenchmarkToolError(
                "shared olean root does not exactly match environment metadata "
                f"(extra={sorted(shared_files - expected_shared_files)}, "
                f"missing={sorted(expected_shared_files - shared_files)})"
            )
    else:
        # A paper-local check authenticates only its selected bundle roots.
        # Sibling papers may be rebuilt concurrently and are deliberately not
        # traversed, hashed, or included in this check's identity.
        for paper_id in bundle_paper_ids:
            bundle_root = environment.shared_olean_root / paper_id
            actual_local = _exact_regular_files(bundle_root)
            expected_local = expected_local_files[paper_id]
            if actual_local != expected_local:
                raise BenchmarkToolError(
                    f"shared olean bundle {paper_id} does not exactly match "
                    "environment metadata "
                    f"(extra={sorted(actual_local - expected_local)}, "
                    f"missing={sorted(expected_local - actual_local)})"
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
    audit_pairs_file: str | Path | None = None,
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
        plural_audit = audit_pairs_file is not None
        if submission_module is None or plural_audit == (target_theorem is not None):
            raise BenchmarkToolError(
                "isolated audit command needs a module and exactly one of "
                "a target theorem or an audit-pairs file"
            )
        command.extend(
            [
                "--audit-helper",
                str(environment.audit_helper),
                "--submission-module",
                submission_module,
            ]
        )
        if plural_audit:
            if expected_module is None or expected_theorem is not None:
                raise BenchmarkToolError(
                    "plural semantic audit needs an expected module but not an "
                    "expected theorem"
                )
            command.extend(
                [
                    "--audit-pairs-file",
                    str(audit_pairs_file),
                    "--expected-module",
                    expected_module,
                    "--local-modules-file",
                    "{local_modules_file}",
                ]
            )
        else:
            assert target_theorem is not None
            command.extend(["--target-theorem", target_theorem])
        if not plural_audit and (
            expected_module is not None or expected_theorem is not None
        ):
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
    raw_audits = parsed.get("audits")
    plural_audits = (
        [item for item in raw_audits if isinstance(item, dict)]
        if isinstance(raw_audits, list)
        else []
    )
    parsed_records = plural_audits if isinstance(raw_audits, list) else [parsed]
    parsed_complete = (
        bool(parsed_records)
        and (
            not isinstance(raw_audits, list)
            or len(parsed_records) == len(raw_audits)
        )
        and all(
            item.get("ok") is True
            and not item.get("forbidden_dependencies")
            and not item.get("missing_helper_modules")
            for item in parsed_records
        )
    )
    complete = bool(
        validation.get("library_audit_complete")
        and audit.get("system_error") is None
        and not audit.get("timed_out")
        and audit.get("exit_code") == 0
        and parsed_complete
    )
    semantic_checks = [item.get("type_check") for item in parsed_records]
    library_declarations = validation.get("library_declarations", [])
    summary = {
        "complete": complete,
        "exit_code": audit.get("exit_code"),
        "format_version": (
            parsed_records[0].get("format_version")
            if parsed_records
            and len({item.get("format_version") for item in parsed_records}) == 1
            else None
        ),
        "forbidden_dependency_count": sum(
            len(item.get("forbidden_dependencies", [])) for item in parsed_records
        ),
        "local_modules": sorted(
            {
                module
                for item in parsed_records
                for module in item.get("local_modules", [])
                if isinstance(module, str)
            }
        ),
        "missing_helper_modules": sorted(
            {
                module
                for item in parsed_records
                for module in item.get("missing_helper_modules", [])
                if isinstance(module, str)
            }
        ),
        "semantic_type_check": semantic_checks[0] if semantic_checks else None,
        "library_use": validation.get("library_use"),
        "library_declarations": library_declarations,
    }
    if isinstance(raw_audits, list):
        summary.update(
            audit_count=len(parsed_records),
            semantic_type_checks=semantic_checks,
        )
    return summary


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
    raw_required = validation.get("required_declarations")
    plural = isinstance(raw_required, list)
    statement_checks = (
        validation.get("statement_checks")
        if isinstance(validation.get("statement_checks"), list)
        else []
    )
    controlled_source_bindings = (
        validation.get("controlled_source_bindings")
        if isinstance(validation.get("controlled_source_bindings"), list)
        else []
    )
    semantic_checks = (
        validation.get("semantic_statement_checks")
        if isinstance(validation.get("semantic_statement_checks"), list)
        else []
    )
    proof_declarations = (
        validation.get("proof_declarations")
        if isinstance(validation.get("proof_declarations"), list)
        else []
    )
    controlled_sorries = (
        validation.get("controlled_sorries")
        if isinstance(validation.get("controlled_sorries"), list)
        else []
    )
    proof_hole_check = (
        validation.get("proof_hole_check")
        if isinstance(validation.get("proof_hole_check"), dict)
        else {}
    )
    hole_checks = (
        proof_hole_check.get("holes")
        if isinstance(proof_hole_check.get("holes"), list)
        else []
    )
    summary = {
        "pass": bool(validation.get("pass")),
        "failure_code": validation.get("failure_code"),
        "note": validation.get("note", ""),
        "controlled_before_ok": bool(controlled_before.get("ok")),
        "controlled_hidden_ok": bool(controlled_hidden.get("ok")),
        "controlled_after_compile_ok": bool(controlled_after_compile.get("ok")),
        "controlled_after_expected_compile_ok": bool(
            controlled_after_expected.get("ok")
        ),
        "controlled_after_audit_ok": bool(controlled_after_audit.get("ok")),
        "semantic_statement_equal": (
            len(semantic_checks) == len(proof_declarations)
            and bool(semantic_checks)
            and all(
                isinstance(item, Mapping) and item.get("equal") is True
                for item in semantic_checks
            )
            if plural
            else semantic.get("equal") is True
        ),
        "statement_unchanged": (
            len(statement_checks) == len(raw_required)
            and all(
                isinstance(item, Mapping) and item.get("ok") is True
                for item in statement_checks
            )
            if plural
            else bool(statement.get("ok"))
        ),
        "static_finding_count": len(validation.get("static_findings", [])),
        "compile_exit_code": compile_result.get("exit_code"),
        "compile_timed_out": bool(compile_result.get("timed_out")),
        "dependency_audit": _audit_summary(validation),
    }
    if plural:
        summary.update(
            required_declaration_count=len(raw_required),
            required_declarations_checked=sum(
                isinstance(item, Mapping) and item.get("ok") is True
                for item in statement_checks
            ),
            controlled_source_bindings_checked=len(controlled_source_bindings),
            controlled_sorry_count=len(controlled_sorries),
            controlled_sorries_checked=sum(
                isinstance(item, Mapping) and item.get("ok") is True
                for item in hole_checks
            ),
            proof_declaration_count=len(proof_declarations),
            proof_declarations_audited=len(semantic_checks),
            proof_holes_discharged=(
                proof_hole_check.get("ok") is True
                and proof_hole_check.get("submitted_sorry_count") == 0
            ),
        )
    return summary


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


def _source_location(text: str, offset: int) -> tuple[int, int]:
    line = text.count("\n", 0, offset) + 1
    previous_newline = text.rfind("\n", 0, offset)
    return line, offset - previous_newline


def _validate_t4_skeleton_source(
    source: Path, spec: ConstructionSpec
) -> list[dict[str, Any]]:
    """Return fail-closed static findings for a designated-hole T4 target."""

    try:
        text = source.read_text(encoding="utf-8")
    except (OSError, UnicodeDecodeError) as error:
        return [{"kind": "unreadable target", "detail": str(error)}]
    sanitized = sanitize_lean(text, erase_strings=True)
    findings: list[dict[str, Any]] = []
    observed_sorries = [
        _source_location(sanitized, match.start())
        for match in re.finditer(r"\bsorry\b", sanitized)
    ]
    expected_sorries = [(item.line, item.column) for item in spec.controlled_sorries]
    if observed_sorries != expected_sorries:
        findings.append(
            {
                "kind": "designated sorry mismatch",
                "expected": [list(item) for item in expected_sorries],
                "observed": [list(item) for item in observed_sorries],
            }
        )
    lines = text.splitlines()
    for item in spec.controlled_sorries:
        marker_occurrences = sum(line.strip() == item.marker for line in lines)
        marker_line = item.line - 1
        previous = lines[marker_line - 1].strip() if 0 < marker_line <= len(lines) else None
        if marker_occurrences != 1 or previous != item.marker:
            findings.append(
                {
                    "kind": "designated marker mismatch",
                    "placeholder_id": item.placeholder_id,
                    "expected_marker": item.marker,
                    "marker_occurrences": marker_occurrences,
                    "sorry_line": item.line,
                }
            )
    for kind, pattern in (
        ("admit", r"\badmit\b"),
        ("sorryAx", r"\bsorryAx\b"),
        ("axiom declaration", r"\baxiom\b"),
        ("constant declaration", r"\bconstant\b"),
        ("unsafe declaration or command", r"\bunsafe\b"),
        ("opaque declaration", r"\bopaque\b"),
    ):
        if re.search(pattern, sanitized):
            findings.append({"kind": kind})
    return findings


def _paper_scoped_module_contract(
    environment: ConstructionEnvironment, paper_id: str
) -> tuple[tuple[str, ...], tuple[str, ...], tuple[str, ...]]:
    """Return the trusted, unavailable, and foreign modules for one bundle.

    Every paper bundle contains exactly its own definitions module. The
    paper-local path explicitly rejects both retired shared cores; its exact
    one-file bundle authentication makes every unlisted foreign paper module
    unavailable without reading mutable sibling-paper records. The legacy
    corpus path additionally probes every foreign module named by its manifest.
    """

    if re.fullmatch(r"P[0-9]+", paper_id) is None:
        raise BenchmarkToolError(f"invalid paper id for module isolation: {paper_id}")
    if paper_id not in environment.manifest_paper_ids:
        raise BenchmarkToolError(
            f"module-isolation paper is absent from the resolved scope: {paper_id}"
        )
    allowed = (f"HighamBench.{paper_id}Definitions",)
    if environment.paper_local:
        if environment.manifest_paper_ids != (paper_id,):
            raise BenchmarkToolError(
                "paper-local module isolation must contain exactly its selected paper"
            )
        return allowed, ("HighamBench.Core", "HighamBench.SemanticCore"), ()
    foreign_paper_modules = tuple(
        f"HighamBench.{other_paper_id}Definitions"
        for other_paper_id in environment.manifest_paper_ids
        if other_paper_id != paper_id
    )
    if not foreign_paper_modules:
        raise BenchmarkToolError(
            f"module isolation for {paper_id} has no foreign paper modules to test"
        )
    unavailable = (
        "HighamBench.Core",
        "HighamBench.SemanticCore",
        *foreign_paper_modules,
    )
    return allowed, unavailable, foreign_paper_modules


def _reports_missing_import(output: str, module: str) -> bool:
    """Recognize supported Lean diagnostics that specifically name a missing module."""

    lowered = output.lower()
    if module.lower() not in lowered:
        return False
    return any(marker in lowered for marker in MISSING_IMPORT_MARKERS) or (
        "object file" in lowered and "does not exist" in lowered
    )


def _paper_module_isolation_probe(
    environment: ConstructionEnvironment,
    spec: ConstructionSpec,
    workspace: Path,
    *,
    command_runner: CommandRunner,
) -> dict[str, Any]:
    """Compile positive and negative imports against one paper's trusted bundle."""

    allowed, unavailable, foreign_paper_modules = _paper_scoped_module_contract(
        environment, spec.paper_id
    )
    attempts: list[dict[str, Any]] = []
    obligations = (
        *((module, True) for module in allowed),
        *((module, False) for module in unavailable),
    )
    for index, (module, expected_importable) in enumerate(obligations, start=1):
        source_text = f"import {module}\n#check True\n"
        source = workspace / f"HighamBenchPaperModuleProbe_{index:02d}.lean"
        source.write_text(source_text, encoding="utf-8")
        command = isolated_lean_command(
            environment,
            action="compile",
            condition=spec.condition,
            paper_id=spec.paper_id,
            workspace=workspace,
            source=source,
        )
        completed = command_runner(
            command,
            cwd=environment.project_root,
            timeout_seconds=environment.timeout_seconds,
        )
        raw_output = completed.get("output")
        result_shape_valid = (
            type(completed.get("exit_code")) is int
            and completed.get("timed_out") is False
            and completed.get("system_error") is None
            and isinstance(raw_output, str)
        )
        full_output = raw_output if isinstance(raw_output, str) else ""
        output, output_truncated = truncate_text(full_output, 20_000)
        missing_import_diagnostic = (
            result_shape_valid
            and completed["exit_code"] != 0
            and _reports_missing_import(full_output, module)
        )
        if (
            result_shape_valid
            and completed["exit_code"] == 0
            and not output_truncated
        ):
            reliable = True
            importable: bool | None = True
        elif missing_import_diagnostic and not output_truncated:
            reliable = True
            importable = False
        else:
            reliable = False
            importable = None
        attempts.append(
            {
                "module": module,
                "expected_importable": expected_importable,
                "source_sha256": hashlib.sha256(source_text.encode("utf-8")).hexdigest(),
                "attempted": True,
                "reliable": reliable,
                "importable": importable,
                "exit_code": completed.get("exit_code"),
                "timed_out": completed.get("timed_out"),
                "system_error": completed.get("system_error"),
                "output": output,
                "output_sha256": hashlib.sha256(full_output.encode("utf-8")).hexdigest(),
                "output_truncated": output_truncated,
                "missing_import_diagnostic": missing_import_diagnostic,
            }
        )

    allowed_attempts = attempts[: len(allowed)]
    unavailable_attempts = attempts[len(allowed) :]
    allowed_passed = sum(
        attempt["reliable"] is True and attempt["importable"] is True
        for attempt in allowed_attempts
    )
    unavailable_rejected = sum(
        attempt["reliable"] is True and attempt["importable"] is False
        for attempt in unavailable_attempts
    )
    return {
        "schema_version": 1,
        "paper_id": spec.paper_id,
        "condition": spec.condition,
        "allowed_modules": list(allowed),
        "unavailable_modules": list(unavailable),
        "foreign_paper_modules": list(foreign_paper_modules),
        "attempt_count": len(attempts),
        "allowed_imports_passed": allowed_passed,
        "unavailable_imports_rejected": unavailable_rejected,
        "pass": (
            allowed_passed == len(allowed)
            and unavailable_rejected == len(unavailable)
        ),
        "attempts": attempts,
    }


def _t4_skeleton_result(
    environment: ConstructionEnvironment,
    spec: ConstructionSpec,
    *,
    command_runner: CommandRunner,
    preflight_fn: Preflight,
) -> dict[str, Any]:
    """Compile one controlled T4 placeholder skeleton without private proof material."""

    manifest_path = _controlled_manifest_path(environment, spec)
    manifest = load_manifest(manifest_path)
    with temporary_directory(
        environment.hidden_parent,
        prefix=f"highambench-skeleton-{spec.task_id}-{spec.condition}-",
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

        controlled_target = task_root / spec.canonical_relative
        findings = _validate_t4_skeleton_source(controlled_target, spec)
        target_sha256 = sha256_file(controlled_target)
        reasons: list[str] = []
        if spec.condition == "N" and (
            not isinstance(n_preflight, Mapping) or not n_preflight.get("ok")
        ):
            reasons.append(
                "the complete staged condition-N package failed its library-absence preflight"
            )
        if findings:
            reasons.append(
                "the controlled T4 target does not match its exact designated-hole contract"
            )

        module_isolation = _paper_module_isolation_probe(
            environment,
            spec,
            workspace,
            command_runner=command_runner,
        )
        if module_isolation["pass"] is not True:
            reasons.append(
                "the paper-scoped trusted bundle failed its allowed/foreign module import probes"
            )

        completed: dict[str, Any] | None = None
        olean_created = False
        if not reasons:
            probe_source = workspace / "HighamBenchT4SkeletonCheck.lean"
            original = controlled_target.read_text(encoding="utf-8")
            checks = "".join(
                f"\n#check {name}\n" for name in spec.required_declarations
            )
            probe_source.write_text(original + checks, encoding="utf-8")
            command = isolated_lean_command(
                environment,
                action="olean",
                condition=spec.condition,
                paper_id=spec.paper_id,
                workspace=workspace,
                source=probe_source,
            )
            completed = command_runner(
                command,
                cwd=environment.project_root,
                timeout_seconds=environment.timeout_seconds,
            )
            olean_created = probe_source.with_suffix(".olean").is_file()
            if (
                completed.get("system_error") is not None
                or completed.get("timed_out")
                or completed.get("exit_code") != 0
                or not olean_created
            ):
                reasons.append(
                    "the designated-hole T4 skeleton failed its isolated Lean build"
                )

        compile_exit_code = completed.get("exit_code") if completed is not None else None
        compile_timed_out = (
            bool(completed.get("timed_out")) if completed is not None else False
        )
        compile_system_error = (
            completed.get("system_error") if completed is not None else None
        )
        validation = {
            "pass": not reasons,
            "failure_code": None if not reasons else "SKELETON_INVALID",
            "note": (
                "all required declarations and exactly the designated T4 holes compiled"
                if not reasons
                else "; ".join(reasons)
            ),
            "compile_exit_code": compile_exit_code,
            "compile_timed_out": compile_timed_out,
            "compile_system_error": compile_system_error,
            "olean_created": olean_created,
            "required_declaration_count": len(spec.required_declarations),
            "required_declarations_checked": (
                len(spec.required_declarations) if not reasons else 0
            ),
            "controlled_sorry_count": len(spec.controlled_sorries),
            "controlled_sorries_checked": (
                len(spec.controlled_sorries) if not findings else 0
            ),
            "static_finding_count": len(findings),
            "static_findings": findings,
        }
        return {
            "task_id": spec.task_id,
            "paper_id": spec.paper_id,
            "tier": spec.tier,
            "condition": spec.condition,
            "construction_kind": T4_SKELETON_KIND,
            "required_declarations": list(spec.required_declarations),
            "controlled_declaration_sources": (
                _controlled_declaration_source_records(spec)
            ),
            "controlled_sorries": _controlled_sorry_records(spec),
            "pass": not reasons,
            "reasons": reasons,
            "manifest_sha256": sha256_file(manifest_path),
            "target_source_sha256": target_sha256,
            "helpers": [],
            "paper_module_isolation": module_isolation,
            "condition_n_library_arguments_omitted": spec.condition == "N",
            "n_preflight": n_preflight,
            "validation": validation,
        }


def check_one(
    environment: ConstructionEnvironment,
    spec: ConstructionSpec,
    *,
    command_runner: CommandRunner = run_captured,
    validator_fn: Validator = validate,
    preflight_fn: Preflight = run_preflight,
) -> dict[str, Any]:
    controlled_skeleton: dict[str, Any] | None = None
    if spec.construction_kind == T4_PRIVATE_PROOF_KIND:
        controlled_skeleton = _t4_skeleton_result(
            environment,
            spec,
            command_runner=command_runner,
            preflight_fn=preflight_fn,
        )
        if controlled_skeleton.get("pass") is not True:
            return {
                "task_id": spec.task_id,
                "paper_id": spec.paper_id,
                "tier": spec.tier,
                "condition": spec.condition,
                "construction_kind": T4_PRIVATE_PROOF_KIND,
                "required_declarations": list(spec.required_declarations),
                "controlled_declaration_sources": (
                    _controlled_declaration_source_records(spec)
                ),
                "controlled_sorries": _controlled_sorry_records(spec),
                "pass": False,
                "reasons": [
                    "the separate controlled T4 designated-hole skeleton gate failed"
                ],
                "manifest_sha256": controlled_skeleton.get("manifest_sha256"),
                "helpers": [],
                "condition_n_library_arguments_omitted": spec.condition == "N",
                "n_preflight": controlled_skeleton.get("n_preflight"),
                "controlled_skeleton": controlled_skeleton,
                "validation": None,
            }
    if (
        spec.construction_kind not in (PRIVATE_PROOF_KIND, T4_PRIVATE_PROOF_KIND)
        or environment.private_gold_root is None
        or spec.gold_filename is None
        or spec.target_theorem is None
    ):
        raise BenchmarkToolError(
            f"{spec.task_id}/{spec.condition} has an invalid construction mode"
        )
    manifest_path = _controlled_manifest_path(environment, spec)
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
                    "construction_kind": spec.construction_kind,
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
                    **(
                        {
                            "required_declarations": list(spec.required_declarations),
                            "controlled_declaration_sources": (
                                _controlled_declaration_source_records(spec)
                            ),
                            "controlled_sorries": _controlled_sorry_records(spec),
                            "controlled_skeleton": controlled_skeleton,
                        }
                        if controlled_skeleton is not None
                        else {}
                    ),
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
                    "construction_kind": spec.construction_kind,
                    "target_theorem": spec.target_theorem,
                    "pass": False,
                    "reasons": ["the private helper failed its isolated fresh build"],
                    "manifest_sha256": sha256_file(manifest_path),
                    "gold_source_sha256": sha256_file(gold_path),
                    "helpers": helper_records,
                    "condition_n_library_arguments_omitted": spec.condition == "N",
                    "n_preflight": n_preflight,
                    **(
                        {
                            "required_declarations": list(spec.required_declarations),
                            "controlled_declaration_sources": (
                                _controlled_declaration_source_records(spec)
                            ),
                            "controlled_sorries": _controlled_sorry_records(spec),
                            "controlled_skeleton": controlled_skeleton,
                        }
                        if controlled_skeleton is not None
                        else {}
                    ),
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
            target_theorem=(
                None
                if spec.construction_kind == T4_PRIVATE_PROOF_KIND
                else spec.target_theorem
            ),
            audit_pairs_file=(
                "{audit_pairs_file}"
                if spec.construction_kind == T4_PRIVATE_PROOF_KIND
                else None
            ),
            expected_module="{expected_module}",
            expected_theorem=(
                None
                if spec.construction_kind == T4_PRIVATE_PROOF_KIND
                else "{expected_theorem}"
            ),
        )
        validation = validator_fn(
            ValidationConfig(
                workspace=workspace,
                submission_relative="Submission.lean",
                canonical_relative=f"task/{spec.canonical_relative}",
                target_theorem=spec.target_theorem,
                compile_command=compile_command,
                condition=spec.condition,
                required_declarations=(
                    spec.required_declarations
                    if spec.construction_kind == T4_PRIVATE_PROOF_KIND
                    else ()
                ),
                required_declaration_sources=(
                    tuple(
                        item.source_file
                        for item in spec.controlled_declaration_sources
                    )
                    if spec.construction_kind == T4_PRIVATE_PROOF_KIND
                    else ()
                ),
                required_declaration_source_lines=(
                    tuple(
                        item.source_line
                        for item in spec.controlled_declaration_sources
                    )
                    if spec.construction_kind == T4_PRIVATE_PROOF_KIND
                    else ()
                ),
                controlled_sorries=(
                    _controlled_sorry_records(spec)
                    if spec.construction_kind == T4_PRIVATE_PROOF_KIND
                    else ()
                ),
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
            "construction_kind": spec.construction_kind,
            "target_theorem": spec.target_theorem,
            "pass": not reasons,
            "reasons": reasons,
            "manifest_sha256": sha256_file(manifest_path),
            "gold_source_sha256": sha256_file(gold_path),
            "helpers": helper_records,
            "condition_n_library_arguments_omitted": spec.condition == "N",
            "n_preflight": n_preflight,
            **(
                {
                    "required_declarations": list(spec.required_declarations),
                    "controlled_declaration_sources": (
                        _controlled_declaration_source_records(spec)
                    ),
                    "controlled_sorries": _controlled_sorry_records(spec),
                    "controlled_skeleton": controlled_skeleton,
                }
                if controlled_skeleton is not None
                else {}
            ),
            "validation": summary,
        }


def _construction_profile(
    specs: Iterable[ConstructionSpec],
) -> dict[str, int]:
    """Count task, declaration, private-proof, and skeleton obligations once."""

    first_by_task: dict[str, ConstructionSpec] = {}
    result_specs = tuple(specs)
    for spec in result_specs:
        first_by_task.setdefault(spec.task_id, spec)
    private_tasks = [
        spec
        for spec in first_by_task.values()
        if spec.construction_kind in (PRIVATE_PROOF_KIND, T4_PRIVATE_PROOF_KIND)
    ]
    t4_tasks = [
        spec
        for spec in first_by_task.values()
        if spec.construction_kind == T4_PRIVATE_PROOF_KIND
    ]
    return {
        "task_count": len(first_by_task),
        "required_declaration_count": sum(
            len(spec.required_declarations) for spec in first_by_task.values()
        ),
        "t4_controlled_sorry_count": sum(
            len(spec.controlled_sorries) for spec in t4_tasks
        ),
        "private_proof_task_count": len(private_tasks),
        "t4_private_proof_task_count": len(t4_tasks),
        "t4_skeleton_task_count": len(t4_tasks),
        "private_proof_result_count": sum(
            spec.construction_kind in (PRIVATE_PROOF_KIND, T4_PRIVATE_PROOF_KIND)
            for spec in result_specs
        ),
        "t4_private_proof_result_count": sum(
            spec.construction_kind == T4_PRIVATE_PROOF_KIND for spec in result_specs
        ),
        "t4_skeleton_result_count": sum(
            spec.construction_kind == T4_PRIVATE_PROOF_KIND for spec in result_specs
        ),
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
            result = {
                "task_id": spec.task_id,
                "paper_id": spec.paper_id,
                "tier": spec.tier,
                "condition": spec.condition,
                "construction_kind": spec.construction_kind,
                "pass": False,
                "reasons": [f"construction check could not run: {error}"],
                "condition_n_library_arguments_omitted": spec.condition == "N",
                "validation": None,
            }
            if spec.target_theorem is not None:
                result["target_theorem"] = spec.target_theorem
            if spec.required_declarations:
                result["required_declarations"] = list(
                    spec.required_declarations
                )
            if spec.controlled_sorries:
                result["controlled_sorries"] = _controlled_sorry_records(spec)
            return result

    if jobs == 1:
        results = [run_one(spec) for spec in environment.specs]
    else:
        with ThreadPoolExecutor(max_workers=jobs) as executor:
            results = list(executor.map(run_one, environment.specs))

    passed = sum(bool(result.get("pass")) for result in results)
    n_results = [result for result in results if result["condition"] == "N"]
    l_results = [result for result in results if result["condition"] == "L"]
    expected = len(environment.specs)
    profile = _construction_profile(environment.specs)
    has_t4 = profile["t4_private_proof_task_count"] > 0
    summary = {
        "expected": expected,
        "checked": len(results),
        "passed": passed,
        "condition_n_passed": sum(bool(item.get("pass")) for item in n_results),
        "condition_l_passed": sum(bool(item.get("pass")) for item in l_results),
    }
    if has_t4:
        summary.update(profile)
    isolation = {
        "fresh_workspace_per_result": True,
        "controlled_task_staged_under": "task/",
        "private_gold_staged_as": "Submission.lean",
        "private_helper_oleans_reused": False,
        "condition_n_numstability_mounts_configured": False,
        "condition_n_preflight_after_complete_controlled_staging": True,
        "condition_l_numstability_mounts_configured": True,
        "validator_hidden_rebuild": True,
    }
    if has_t4:
        isolation.update(
            {
                "t4_private_gold_required": True,
                "t4_private_proofs_plural_validated": True,
                "t4_skeleton_validated_separately": True,
                "t4_skeleton_staged_from_controlled_target": True,
                "t4_designated_sorries_only": True,
            }
        )
    evidence = {
        "schema_version": 4 if environment.paper_local else (3 if has_t4 else 1),
        "kind": "highambench-private-construction-check",
        "generated_at_utc": utc_now(),
        "execution": {
            "jobs": jobs,
            "result_order": (
                "paper record order, N then L per task"
                if environment.paper_local
                else "central manifest order, N then L per task"
            ),
        },
        "pass": passed == len(results) == expected,
        "scope": (
            _paper_scope_record(environment)
            if environment.paper_local
            else _scope_record(
                central_manifest=environment.central_manifest,
                manifest_task_ids=environment.manifest_task_ids,
                manifest_paper_ids=environment.manifest_paper_ids,
                selected_specs=environment.specs,
                selected_paper_ids=environment.selected_paper_ids,
            )
        ),
        "summary": summary,
        "isolation": isolation,
        "verification_basis": basis,
        "results": results,
    }
    if environment.paper_local:
        evidence["record_status"] = (
            "paper_current_final"
            if evidence["pass"] and evidence["scope"]["complete_paper_scope"]
            else "partial_paper_construction_check"
        )
    else:
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
    environment: ConstructionEnvironment, specs: tuple[ConstructionSpec, ...]
) -> dict[str, str]:
    """Authenticate every live task package and return its manifest digest."""

    hashes: dict[str, str] = {}
    for spec in specs:
        if spec.task_id in hashes:
            continue
        path = _controlled_manifest_path(environment, spec)
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
            staged_source = environment.benchmark_root / relative
            if staged_source.is_symlink():
                raise BenchmarkToolError(
                    f"current controlled source may not be a symlink: {relative}"
                )
        verification = verify_manifest(environment.benchmark_root, manifest)
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
    result: Mapping[str, Any],
    *,
    condition: str,
    target_theorem: str,
    required_declarations: tuple[str, ...] = (),
    controlled_sorries: tuple[ControlledSorry, ...] = (),
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
    if required_declarations:
        proof_declarations = [item.lean_name for item in controlled_sorries]
        plural_validation = {
            "required_declaration_count": len(required_declarations),
            "required_declarations_checked": len(required_declarations),
            "controlled_source_bindings_checked": len(required_declarations),
            "controlled_sorry_count": len(controlled_sorries),
            "controlled_sorries_checked": len(controlled_sorries),
            "proof_declaration_count": len(proof_declarations),
            "proof_declarations_audited": len(proof_declarations),
            "proof_holes_discharged": True,
        }
        if any(
            validation.get(field) != expected
            for field, expected in plural_validation.items()
        ):
            raise BenchmarkToolError(
                f"construction result {task_id}/{condition} did not validate "
                "every T4 declaration and controlled proof hole"
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
    if required_declarations:
        proof_declarations = [item.lean_name for item in controlled_sorries]
        semantic_checks = _manifest_list(
            dependency.get("semantic_type_checks"),
            f"construction result {task_id}/{condition} semantic type checks",
        )
        if (
            dependency.get("audit_count") != len(proof_declarations)
            or len(semantic_checks) != len(proof_declarations)
        ):
            raise BenchmarkToolError(
                f"construction result {task_id}/{condition} does not contain one "
                "dependency audit per T4 proof declaration"
            )
        for index, (raw_semantic, lean_name) in enumerate(
            zip(semantic_checks, proof_declarations, strict=True)
        ):
            semantic_check = _manifest_mapping(
                raw_semantic,
                f"construction result {task_id}/{condition} semantic check {index}",
            )
            if (
                semantic_check.get("candidate") != lean_name
                or semantic_check.get("equal") is not True
                or not isinstance(semantic_check.get("expected"), str)
                or not semantic_check["expected"]
            ):
                raise BenchmarkToolError(
                    f"construction result {task_id}/{condition} has an incomplete "
                    "T4 declaration audit"
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


def _validate_paper_module_isolation_record(
    environment: ConstructionEnvironment,
    spec: ConstructionSpec,
    raw_record: Any,
) -> None:
    """Authenticate every positive and negative paper-bundle import attempt."""

    label = f"construction result {spec.task_id}/{spec.condition} module isolation"
    record = _manifest_mapping(raw_record, label)
    allowed, unavailable, foreign_paper_modules = _paper_scoped_module_contract(
        environment, spec.paper_id
    )
    expected_record_keys = {
        "schema_version",
        "paper_id",
        "condition",
        "allowed_modules",
        "unavailable_modules",
        "foreign_paper_modules",
        "attempt_count",
        "allowed_imports_passed",
        "unavailable_imports_rejected",
        "pass",
        "attempts",
    }
    if set(record) != expected_record_keys:
        raise BenchmarkToolError(f"{label} has a noncanonical schema")
    if (
        record.get("schema_version") != 1
        or record.get("paper_id") != spec.paper_id
        or record.get("condition") != spec.condition
        or record.get("allowed_modules") != list(allowed)
        or record.get("unavailable_modules") != list(unavailable)
        or record.get("foreign_paper_modules") != list(foreign_paper_modules)
        or record.get("attempt_count") != len(allowed) + len(unavailable)
        or record.get("allowed_imports_passed") != len(allowed)
        or record.get("unavailable_imports_rejected") != len(unavailable)
        or record.get("pass") is not True
    ):
        raise BenchmarkToolError(f"{label} does not satisfy the exact paper scope")

    attempts = _manifest_list(record.get("attempts"), f"{label} attempts")
    obligations = (
        *((module, True) for module in allowed),
        *((module, False) for module in unavailable),
    )
    if len(attempts) != len(obligations):
        raise BenchmarkToolError(f"{label} has the wrong attempt count")
    expected_attempt_keys = {
        "module",
        "expected_importable",
        "source_sha256",
        "attempted",
        "reliable",
        "importable",
        "exit_code",
        "timed_out",
        "system_error",
        "output",
        "output_sha256",
        "output_truncated",
        "missing_import_diagnostic",
    }
    for index, (raw_attempt, obligation) in enumerate(
        zip(attempts, obligations, strict=True), start=1
    ):
        attempt = _manifest_mapping(raw_attempt, f"{label} attempt {index}")
        module, expected_importable = obligation
        output = attempt.get("output")
        source_text = f"import {module}\n#check True\n"
        if set(attempt) != expected_attempt_keys:
            raise BenchmarkToolError(f"{label} attempt {index} has a noncanonical schema")
        if (
            attempt.get("module") != module
            or attempt.get("expected_importable") is not expected_importable
            or attempt.get("source_sha256")
            != hashlib.sha256(source_text.encode("utf-8")).hexdigest()
            or attempt.get("attempted") is not True
            or attempt.get("reliable") is not True
            or attempt.get("importable") is not expected_importable
            or type(attempt.get("exit_code")) is not int
            or attempt.get("timed_out") is not False
            or attempt.get("system_error") is not None
            or not isinstance(output, str)
            or attempt.get("output_sha256")
            != hashlib.sha256(
                (output if isinstance(output, str) else "").encode("utf-8")
            ).hexdigest()
            or attempt.get("output_truncated") is not False
        ):
            raise BenchmarkToolError(f"{label} attempt {index} is incomplete or stale")
        if expected_importable:
            if (
                attempt.get("exit_code") != 0
                or attempt.get("missing_import_diagnostic") is not False
            ):
                raise BenchmarkToolError(
                    f"{label} did not import allowed module {module}"
                )
            continue
        if (
            attempt.get("exit_code") == 0
            or attempt.get("missing_import_diagnostic") is not True
            or not _reports_missing_import(output, module)
        ):
            raise BenchmarkToolError(
                f"{label} did not prove unavailable module {module} absent"
            )


def _validate_t4_skeleton_record(
    environment: ConstructionEnvironment,
    result: Mapping[str, Any],
    spec: ConstructionSpec,
) -> tuple[bool, bool]:
    """Authenticate one promoted T4 skeleton result; return N/skeleton flags."""

    label = f"construction result {spec.task_id}/{spec.condition} T4 skeleton"
    root = environment.benchmark_root
    if (
        result.get("construction_kind") != T4_SKELETON_KIND
        or result.get("required_declarations")
        != list(spec.required_declarations)
        or result.get("controlled_declaration_sources")
        != _controlled_declaration_source_records(spec)
        or result.get("controlled_sorries") != _controlled_sorry_records(spec)
        or result.get("helpers") != []
        or result.get("target_source_sha256")
        != sha256_file(root / spec.canonical_relative)
    ):
        raise BenchmarkToolError(f"{label} does not match task.json and Target.lean")
    _validate_paper_module_isolation_record(
        environment,
        spec,
        result.get("paper_module_isolation"),
    )
    validation = _manifest_mapping(result.get("validation"), f"{label} validation")
    if (
        validation.get("pass") is not True
        or validation.get("failure_code") is not None
        or validation.get("compile_exit_code") != 0
        or validation.get("compile_timed_out") is not False
        or validation.get("compile_system_error") is not None
        or validation.get("olean_created") is not True
        or validation.get("required_declaration_count")
        != len(spec.required_declarations)
        or validation.get("required_declarations_checked")
        != len(spec.required_declarations)
        or validation.get("controlled_sorry_count")
        != len(spec.controlled_sorries)
        or validation.get("controlled_sorries_checked")
        != len(spec.controlled_sorries)
        or validation.get("static_finding_count") != 0
        or validation.get("static_findings") != []
        or not isinstance(validation.get("note"), str)
        or not validation["note"].strip()
    ):
        raise BenchmarkToolError(f"{label} did not pass its exact compile/hole gate")

    if spec.condition == "N":
        preflight = _manifest_mapping(
            result.get("n_preflight"), f"{label} N preflight"
        )
        controlled = _manifest_mapping(
            preflight.get("controlled_files_verified_after_staging"),
            f"{label} controlled staging",
        )
        probe = _manifest_mapping(
            preflight.get("import_probe"), f"{label} import probe"
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
        ):
            raise BenchmarkToolError(f"{label} has an incomplete isolation preflight")
        return True, True
    if (
        result.get("condition_n_library_arguments_omitted") is not False
        or result.get("n_preflight") is not None
    ):
        raise BenchmarkToolError(f"{label} has invalid L-side isolation metadata")
    return False, True


def _validate_t4_promoted_result(
    environment: ConstructionEnvironment,
    result: Mapping[str, Any],
    spec: ConstructionSpec,
) -> tuple[bool, bool, bool]:
    """Authenticate combined T4 private-proof and separate skeleton evidence."""

    label = f"construction result {spec.task_id}/{spec.condition} T4 private proof"
    if (
        result.get("construction_kind") != T4_PRIVATE_PROOF_KIND
        or result.get("target_theorem") != spec.target_theorem
        or result.get("required_declarations") != list(spec.required_declarations)
        or result.get("controlled_declaration_sources")
        != _controlled_declaration_source_records(spec)
        or result.get("controlled_sorries") != _controlled_sorry_records(spec)
    ):
        raise BenchmarkToolError(
            f"{label} does not match its plural declaration/hole contract"
        )
    _hex_digest(result.get("gold_source_sha256"), f"{label} source")
    skeleton = _manifest_mapping(
        result.get("controlled_skeleton"), f"{label} controlled skeleton"
    )
    if (
        skeleton.get("task_id") != spec.task_id
        or skeleton.get("paper_id") != spec.paper_id
        or skeleton.get("tier") != spec.tier
        or skeleton.get("condition") != spec.condition
        or skeleton.get("pass") is not True
        or skeleton.get("reasons") != []
        or skeleton.get("manifest_sha256") != result.get("manifest_sha256")
    ):
        raise BenchmarkToolError(
            f"{label} has failed, stale, or mismatched controlled-skeleton evidence"
        )
    skeleton_n_ok, skeleton_ok = _validate_t4_skeleton_record(
        environment, skeleton, spec
    )
    assert spec.target_theorem is not None
    proof_n_ok, proof_l_ok = _validate_validation_summary(
        result,
        condition=spec.condition,
        target_theorem=spec.target_theorem,
        required_declarations=spec.required_declarations,
        controlled_sorries=spec.controlled_sorries,
    )
    if skeleton_n_ok != proof_n_ok:
        raise BenchmarkToolError(
            f"{label} has inconsistent N/L identity across its two gates"
        )
    return proof_n_ok, proof_l_ok, skeleton_ok


def validate_current_construction_evidence(
    environment: ConstructionEnvironment, evidence: Mapping[str, Any]
) -> dict[str, Any]:
    """Authenticate one complete current N/L construction certificate."""

    raw_root = Path(environment.benchmark_root)
    if raw_root.is_symlink():
        raise BenchmarkToolError("benchmark root may not be a symlink during promotion")
    root = _required_directory(raw_root, "benchmark root")
    if environment.paper_local:
        if len(environment.selected_paper_ids) != 1:
            raise BenchmarkToolError(
                "paper-local evidence requires exactly one selected paper"
            )
        paper_id = environment.selected_paper_ids[0]
        scope_source = _required_file(
            root / "tasks" / paper_id / "paper.json", f"{paper_id} paper record"
        )
        specs = tuple(paper_construction_specs(root, paper_id))
        expected_schema = 4
        expected_status = "paper_current_final"
        expected_order = "paper record order, N then L per task"
    else:
        scope_source = _required_file(
            root / CENTRAL_MANIFEST_RELATIVE, "central benchmark manifest"
        )
        specs = tuple(construction_specs(root))
        expected_schema = None
        expected_status = "current_final"
        expected_order = "central manifest order, N then L per task"
    task_ids = _task_ids(specs)
    paper_ids = _paper_ids(specs)
    profile = _construction_profile(specs)
    has_t4 = profile["t4_private_proof_task_count"] > 0
    expected_results = len(specs)
    if expected_results != len(task_ids) * 2:
        raise BenchmarkToolError(
            "construction manifest must yield exactly one N and one L result per task"
        )
    if (
        tuple(environment.specs) != specs
        or environment.manifest_task_ids != task_ids
        or environment.manifest_paper_ids != paper_ids
        or environment.selected_paper_ids != paper_ids
    ):
        raise BenchmarkToolError(
            "construction evidence requires the resolved complete current scope"
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
    expected_schema = expected_schema if expected_schema is not None else (3 if has_t4 else 1)
    if (
        evidence.get("schema_version") != expected_schema
        or evidence.get("kind") != "highambench-private-construction-check"
        or evidence.get("pass") is not True
        or evidence.get("record_status") != expected_status
    ):
        raise BenchmarkToolError(
            f"construction evidence requires a passing {expected_status} certificate"
        )
    _manifest_string(evidence.get("generated_at_utc"), "construction generation time")

    expected_summary: dict[str, Any] = {
        "expected": expected_results,
        "checked": expected_results,
        "passed": expected_results,
        "condition_n_passed": len(task_ids),
        "condition_l_passed": len(task_ids),
    }
    if has_t4:
        expected_summary.update(profile)
    summary = _manifest_mapping(evidence.get("summary"), "construction summary")
    if dict(summary) != expected_summary:
        raise BenchmarkToolError(
            f"construction promotion requires exact {expected_results}/{expected_results} "
            "schema-aware summary counts"
        )

    scope = _manifest_mapping(evidence.get("scope"), "construction scope")
    expected_scope = (
        _paper_scope_record(environment)
        if environment.paper_local
        else _scope_record(
            central_manifest=scope_source,
            manifest_task_ids=task_ids,
            manifest_paper_ids=paper_ids,
            selected_specs=specs,
            selected_paper_ids=paper_ids,
        )
    )
    if dict(scope) != expected_scope:
        raise BenchmarkToolError(
            "construction evidence scope is not bound to the complete current scope"
        )
    execution = _manifest_mapping(evidence.get("execution"), "construction execution")
    _positive_integer(execution.get("jobs"), "construction jobs")
    if execution.get("result_order") != expected_order:
        raise BenchmarkToolError("construction promotion has the wrong result order")

    required_isolation: dict[str, Any] = {
        "condition_l_numstability_mounts_configured": True,
        "condition_n_numstability_mounts_configured": False,
        "condition_n_preflight_after_complete_controlled_staging": True,
        "controlled_task_staged_under": "task/",
        "fresh_workspace_per_result": True,
        "private_gold_staged_as": "Submission.lean",
        "private_helper_oleans_reused": False,
        "validator_hidden_rebuild": True,
    }
    if has_t4:
        required_isolation.update(
            {
                "t4_private_gold_required": True,
                "t4_private_proofs_plural_validated": True,
                "t4_skeleton_validated_separately": True,
                "t4_skeleton_staged_from_controlled_target": True,
                "t4_designated_sorries_only": True,
            }
        )
    isolation = _manifest_mapping(evidence.get("isolation"), "construction isolation")
    if dict(isolation) != required_isolation:
        raise BenchmarkToolError("construction promotion lacks its required isolation controls")

    basis = _manifest_mapping(
        evidence.get("verification_basis"), "construction verification basis"
    )
    expected_basis = verification_basis(environment)
    tools = _manifest_mapping(basis.get("tools"), "construction tool digests")
    tool_relatives = (
        (*CONSTRUCTION_TOOL_RELATIVES, *PAPER_LOCAL_TOOL_RELATIVES)
        if environment.paper_local
        else CONSTRUCTION_TOOL_RELATIVES
    )
    if set(tools) != set(tool_relatives):
        raise BenchmarkToolError("construction promotion has the wrong validator tool set")
    for relative in tool_relatives:
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

    controlled_hashes = _current_controlled_manifest_hashes(environment, specs)
    raw_results = _manifest_list(evidence.get("results"), "construction results")
    if len(raw_results) != expected_results:
        raise BenchmarkToolError(
            f"construction promotion requires exactly {expected_results} results"
        )
    n_preflights = 0
    l_library_dependencies = 0
    t4_skeleton_results = 0
    for index, (raw_result, spec) in enumerate(zip(raw_results, specs, strict=True)):
        result = _manifest_mapping(raw_result, f"construction result {index}")
        expected_identity = {
            "task_id": spec.task_id,
            "paper_id": spec.paper_id,
            "tier": spec.tier,
            "condition": spec.condition,
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
        if spec.construction_kind == T4_PRIVATE_PROOF_KIND:
            n_ok, l_ok, skeleton_ok = _validate_t4_promoted_result(
                environment, result, spec
            )
            n_preflights += int(n_ok)
            l_library_dependencies += int(l_ok)
            t4_skeleton_results += int(skeleton_ok)
            continue

        if result.get("target_theorem") != spec.target_theorem:
            raise BenchmarkToolError(
                f"construction result {index} has the wrong target theorem"
            )
        _hex_digest(
            result.get("gold_source_sha256"),
            f"construction result {spec.task_id}/{spec.condition} gold proof",
        )
        assert spec.target_theorem is not None
        n_ok, l_ok = _validate_validation_summary(
            result,
            condition=spec.condition,
            target_theorem=spec.target_theorem,
        )
        n_preflights += int(n_ok)
        l_library_dependencies += int(l_ok)
    if (
        n_preflights != len(task_ids)
        or l_library_dependencies != profile["private_proof_task_count"]
        or t4_skeleton_results != profile["t4_skeleton_result_count"]
    ):
        raise BenchmarkToolError(
            "construction promotion has incomplete N preflights, L proof dependencies, "
            "or T4 skeleton builds"
        )
    validation = {
        "paper_count": len(paper_ids),
        "task_count": len(task_ids),
        "required_declaration_count": profile["required_declaration_count"],
        "t4_controlled_sorry_count": profile["t4_controlled_sorry_count"],
        "private_proof_task_count": profile["private_proof_task_count"],
        "t4_private_proof_task_count": profile["t4_private_proof_task_count"],
        "t4_skeleton_task_count": profile["t4_skeleton_task_count"],
        "result_count": len(raw_results),
        "condition_n_preflight_count": n_preflights,
        "condition_l_library_dependency_count": l_library_dependencies,
        "t4_skeleton_result_count": t4_skeleton_results,
        "controlled_manifest_sha256": controlled_hashes,
    }
    if environment.paper_local:
        validation["paper_record_sha256"] = sha256_file(scope_source)
    else:
        validation["central_manifest_sha256"] = sha256_file(scope_source)
    return validation


def publish_paper_construction_evidence(
    environment: ConstructionEnvironment,
    evidence: Mapping[str, Any],
    *,
    evidence_validator: Callable[
        [ConstructionEnvironment, Mapping[str, Any]], dict[str, Any]
    ] = validate_current_construction_evidence,
    registry_planner: Callable[[Path, str], Any] = paper_registry.plan_paper_registration,
    registry_finalizer: Callable[..., dict[str, Any]] = paper_registry.finalize_paper,
) -> dict[str, Any]:
    """Publish one deeply validated paper certificate and refresh its registration."""

    if not environment.paper_local or len(environment.selected_paper_ids) != 1:
        raise BenchmarkToolError(
            "paper-local construction publication requires exactly one paper-local scope"
        )
    paper_id = environment.selected_paper_ids[0]
    root = Path(environment.benchmark_root).resolve()
    validation = evidence_validator(environment, evidence)
    plan = registry_planner(root, paper_id)
    registration = _manifest_mapping(
        plan.registration, f"{paper_id} prospective registration"
    )
    if registration.get("paper_id") != paper_id:
        raise BenchmarkToolError("paper registry returned the wrong paper identity")
    if registration.get("phase") != "construction":
        raise BenchmarkToolError(
            "construction evidence must be published before measurement-ready promotion"
        )

    task_ids = tuple(
        _manifest_string(item, f"{paper_id} registration task id")
        for item in _manifest_list(
            registration.get("task_ids"), f"{paper_id} registration task ids"
        )
    )
    if task_ids != _task_ids(environment.specs):
        raise BenchmarkToolError(
            f"{paper_id} registry task scope changed after construction checking"
        )
    task_record_sha256: dict[str, str] = {}
    controlled_manifest_sha256: dict[str, str] = {}
    for raw_task in _manifest_list(
        registration.get("tasks"), f"{paper_id} registration tasks"
    ):
        task = _manifest_mapping(raw_task, f"{paper_id} registration task")
        task_id = _manifest_string(task.get("task_id"), f"{paper_id} task id")
        task_record = _manifest_mapping(
            task.get("task_record"), f"{task_id} task record binding"
        )
        controlled = _manifest_mapping(
            task.get("controlled_manifest"), f"{task_id} controlled binding"
        )
        task_record_sha256[task_id] = _hex_digest(
            task_record.get("sha256"), f"{task_id} task record"
        )
        controlled_manifest_sha256[task_id] = _hex_digest(
            controlled.get("sha256"), f"{task_id} controlled manifest"
        )
    if tuple(task_record_sha256) != task_ids or tuple(controlled_manifest_sha256) != task_ids:
        raise BenchmarkToolError(f"{paper_id} registry task bindings are incomplete")
    if validation.get("controlled_manifest_sha256") != controlled_manifest_sha256:
        raise BenchmarkToolError(
            f"{paper_id} controlled manifests changed after construction checking"
        )

    definition_source = _manifest_mapping(
        registration.get("definition_source"), f"{paper_id} definition source"
    )
    paper_record = _manifest_mapping(
        registration.get("paper_record"), f"{paper_id} paper record"
    )
    definition_source_sha256 = _hex_digest(
        definition_source.get("sha256"), f"{paper_id} definition source"
    )
    paper_record_sha256 = _hex_digest(
        paper_record.get("sha256"), f"{paper_id} paper record"
    )
    if validation.get("paper_record_sha256") != paper_record_sha256:
        raise BenchmarkToolError(
            f"{paper_id} paper record changed after construction checking"
        )

    certificate = dict(evidence)
    certificate_digest = hashlib.sha256(
        json.dumps(
            certificate,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        ).encode("utf-8")
    ).hexdigest()
    receipt = {
        "schema_version": paper_registry.CONSTRUCTION_EVIDENCE_SCHEMA,
        "kind": paper_registry.CONSTRUCTION_EVIDENCE_KIND,
        "paper_id": paper_id,
        "pass": True,
        "task_ids": list(task_ids),
        "definition_source_sha256": definition_source_sha256,
        "paper_record_sha256": paper_record_sha256,
        "task_record_sha256": task_record_sha256,
        "controlled_manifest_sha256": controlled_manifest_sha256,
        "certificate_sha256": certificate_digest,
        "certificate": certificate,
        "validation": validation,
    }
    receipt_payload = _canonical_json_bytes(receipt)
    destination = root / "metadata" / "papers" / paper_id / "construction.json"
    _replace_promoted_documents({destination: receipt_payload})
    registry_result = registry_finalizer(root, paper_id, mode="write")
    current = registry_planner(root, paper_id).registration
    construction = _manifest_mapping(
        _manifest_mapping(current, f"{paper_id} current registration").get(
            "readiness_artifacts"
        ),
        f"{paper_id} readiness artifacts",
    ).get("construction")
    if not isinstance(construction, Mapping) or construction.get("status") != "authenticated":
        raise BenchmarkToolError(
            f"{paper_id} registry did not authenticate its construction evidence"
        )
    written = [f"metadata/papers/{paper_id}/construction.json"]
    written.extend(str(item) for item in registry_result.get("written", []))
    if any(not item.startswith(f"metadata/papers/{paper_id}/") for item in written):
        raise BenchmarkToolError("paper-local construction publication escaped its paper")
    return {
        "status": "authenticated",
        "paper_id": paper_id,
        "receipt_path": f"metadata/papers/{paper_id}/construction.json",
        "receipt_sha256": hashlib.sha256(receipt_payload).hexdigest(),
        "certificate_sha256": certificate_digest,
        "paper_snapshot_sha256": registry_result["paper_snapshot_sha256"],
        "written": written,
    }


def _construction_pointer_documents(
    certificate_sha256: str, validation: Mapping[str, Any]
) -> dict[Path, dict[str, Any]]:
    task_count = int(validation["task_count"])
    result_count = int(validation["result_count"])
    proof_task_count = int(validation["private_proof_task_count"])
    skeleton_task_count = int(validation["t4_skeleton_task_count"])
    t4_skeleton_result_count = int(validation["t4_skeleton_result_count"])
    n_reason = (
        "The complete construction record contains one fresh N preflight for "
        f"each of all {task_count} tasks. Each preflight scans the fully staged "
        "controlled task before private proof material or a generated skeleton "
        "check is introduced, verifies the controlled manifest, and confirms "
        "with a real Lean import probe that NumStability is unavailable."
    )
    l_reason = (
        f"The current evidence rebuilds and audits {proof_task_count} private "
        "task proofs per condition"
        + (
            f", including plural validation for {skeleton_task_count} T4 task(s), "
            "and separately compiles each T4 designated-hole skeleton per condition"
            if skeleton_task_count
            else ""
        )
        + " against the complete current construction snapshot."
    )
    library_result: dict[str, Any] = {
        "proofs_checked": proof_task_count * 2,
        "proofs_passed": proof_task_count * 2,
        "condition_n_library_use": False,
        "condition_l_passed_proofs_using_numstability": proof_task_count,
        "dependency_audit_format": 2,
        "forbidden_dependencies": 0,
    }
    if skeleton_task_count:
        library_result.update(
            {
                "total_construction_results_checked": result_count,
                "t4_skeleton_results_passed": t4_skeleton_result_count,
                "t4_controlled_sorry_count": validation[
                    "t4_controlled_sorry_count"
                ],
                "required_declaration_count": validation[
                    "required_declaration_count"
                ],
            }
        )
    return {
        CONDITION_N_POINTER_RELATIVE: {
            "schema_version": SCHEMA_VERSION,
            "kind": "highambench-condition-n-preflight-evidence-pointer",
            "status": "current complete-corpus construction evidence",
            "current_evidence": CURRENT_CONSTRUCTION_EVIDENCE_PROJECT_PATH,
            "current_evidence_sha256": certificate_sha256,
            "reason": n_reason,
            "current_result": {
                "condition_n_tasks_checked": task_count,
                "complete_staged_task_scans_passed": task_count,
                "reliable_failed_import_probes": task_count,
                "filesystem_leaks": 0,
            },
        },
        LIBRARY_DEPENDENCY_POINTER_RELATIVE: {
            "schema_version": SCHEMA_VERSION,
            "kind": "highambench-library-dependency-evidence-pointer",
            "status": "current complete-corpus construction evidence",
            "current_evidence": CURRENT_CONSTRUCTION_EVIDENCE_PROJECT_PATH,
            "current_evidence_sha256": certificate_sha256,
            "reason": l_reason,
            "current_result": library_result,
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
    pointer_documents = _construction_pointer_documents(certificate_sha256, validation)
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
        help=(
            "private_gold root containing one directory per selected paper and "
            "proof-complete T*_N.lean/T*_L.lean files, including T4_N.lean and "
            "T4_L.lean"
        ),
    )
    parser.add_argument(
        "--paper-id",
        action="append",
        help=(
            "limit the construction check to this paper id (repeatable); omitting "
            "the option checks every manifest-available private N/L proof and any "
            "separate T4 controlled skeleton gate"
        ),
    )
    parser.add_argument(
        "--paper-local-evidence",
        action="store_true",
        help=(
            "with exactly one --paper-id, discover only that paper's paper.json/task.json "
            "records, build its one-file definitions bundle, run its private N/L checks, "
            "and publish metadata/papers/P0X/construction.json plus its paper-local "
            "registration; this mode never reads metadata/manifest.json or writes "
            "corpus evidence"
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
            "after a successful complete manifest check written to a separate "
            "--output file, independently authenticate and transactionally promote "
            "its schema-aware N/L certificate plus both derived evidence pointers"
        ),
    )
    return parser


def _requested_scope(args: argparse.Namespace) -> dict[str, Any]:
    """Describe the requested manifest scope even if material resolution fails."""

    benchmark_root = _required_directory(args.benchmark_root, "benchmark root")
    if getattr(args, "paper_local_evidence", False):
        if not args.paper_id or len(args.paper_id) != 1:
            raise BenchmarkToolError(
                "--paper-local-evidence requires exactly one --paper-id P0X"
            )
        paper_id = str(args.paper_id[0])
        specs = tuple(paper_construction_specs(benchmark_root, paper_id))
        paper_record = _required_file(
            benchmark_root / "tasks" / paper_id / "paper.json",
            f"{paper_id} paper record",
        )
        return {
            "scope_kind": "paper-local",
            "paper_id": paper_id,
            "paper_record": f"tasks/{paper_id}/paper.json",
            "paper_record_sha256": sha256_file(paper_record),
            "task_ids": list(_task_ids(specs)),
            "complete_paper_scope": True,
        }
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
    if args.paper_local_evidence:
        if not args.paper_id or len(args.paper_id) != 1:
            print(
                "construction-check error: --paper-local-evidence requires exactly one --paper-id P0X",
                file=sys.stderr,
            )
            return 2
        if args.promote_current:
            print(
                "construction-check error: --paper-local-evidence cannot use --promote-current",
                file=sys.stderr,
            )
            return 2
        if args.output is not None:
            print(
                "construction-check error: --paper-local-evidence forbids --output; "
                "it writes only the authenticated paper-local receipt",
                file=sys.stderr,
            )
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
        bundle_preparation: dict[str, Any] | None = None
        if args.paper_local_evidence:
            paper_id = str(args.paper_id[0])
            bundle_preparation = finalize_paper_bundle(
                args.benchmark_root,
                paper_id,
                phase="construction",
                project_root=args.project_root,
                mode="write",
            )
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
    if args.paper_local_evidence and evidence["pass"]:
        try:
            publication = publish_paper_construction_evidence(environment, evidence)
        except (OSError, BenchmarkToolError, ValueError) as error:
            print(
                f"construction-check paper-local publication error: {error}",
                file=sys.stderr,
            )
            return 2
        print(
            json.dumps(
                {"bundle_preparation": bundle_preparation, "publication": publication},
                indent=2,
                sort_keys=True,
            )
        )
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
