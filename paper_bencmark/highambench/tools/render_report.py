#!/usr/bin/env python3
"""Build a detailed, standalone HighamBench construction report.

The short table renderer in ``analyze.py`` is useful for machine-facing result
artifacts. This program builds the longer report for every paper and task in
the current manifest. It deliberately refuses a partial or stale analysis: the
report is an end product, not a way to make an unfinished matrix look complete.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
from typing import Any, Iterable, Mapping, Sequence

try:
    from .common import FAILURE_CODES, BenchmarkToolError, read_json
    from .hashes import load_manifest, verify_manifest
except ImportError:  # Direct script execution.
    from common import FAILURE_CODES, BenchmarkToolError, read_json  # type: ignore
    from hashes import load_manifest, verify_manifest  # type: ignore


class ReportError(BenchmarkToolError):
    """The requested final report cannot be made from the supplied records."""


CONSTRUCTION_TOOL_PATHS = (
    "tools/check_construction.py",
    "tools/common.py",
    "tools/hashes.py",
    "tools/lean_isolated.py",
    "tools/preflight.py",
    "tools/validator.py",
    "tools/dependency_audit.lean",
)
PRUNED_LIBRARY_OLEAN_ROOT = (
    "paper_bencmark/scratch_pad/highambench_environment/numstability_olean"
)
PACKAGES_RUNTIME_ROOT = (
    "paper_bencmark/scratch_pad/highambench_environment/packages_runtime"
)
PACKAGE_COMPILED_SUPPORT_SUFFIXES = (
    ".olean.server",
    ".olean.private",
    ".ir",
)


def _package_runtime_file_kind(relative: str) -> str | None:
    if relative == "mathlib/Mathlib.lean" or (
        relative.startswith("mathlib/Mathlib/") and relative.endswith(".lean")
    ):
        return "source"
    if "/.lake/build/lib/lean/" not in relative:
        return None
    if relative.endswith(".olean"):
        return "olean"
    if relative.endswith(PACKAGE_COMPILED_SUPPORT_SUFFIXES):
        return "compiled_support"
    return None


@dataclass(frozen=True)
class ReportInputs:
    benchmark_root: Path
    config: Mapping[str, Any]
    environment: Mapping[str, Any]
    manifest: Mapping[str, Any]
    run_order: Mapping[str, Any]
    papers: tuple[Mapping[str, Any], ...]
    tasks: tuple[Mapping[str, Any], ...]
    evidence: Mapping[str, Mapping[str, Any]]
    construction_check: Mapping[str, Any]
    freeze_check: Mapping[str, Any]
    release_manifest: Mapping[str, Any]
    compiled_environment_summary: Mapping[str, Any]
    packages_runtime_manifest: Mapping[str, Any]
    source_manifest: Mapping[str, Any]
    compiled_manifest: Mapping[str, Any]
    reviews: tuple[Mapping[str, Any], ...]
    analysis: Mapping[str, Any]
    shared_source: str


def _object(path: Path, label: str) -> Mapping[str, Any]:
    if not path.is_file():
        raise ReportError(f"missing {label}: {path}")
    value = read_json(path)
    if not isinstance(value, Mapping):
        raise ReportError(f"{label} must be a JSON object: {path}")
    return value


def _document_digest(value: Mapping[str, Any]) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def _file_digest(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _hex_digest(value: Any) -> bool:
    return isinstance(value, str) and len(value) == 64 and all(
        character in "0123456789abcdef" for character in value
    )


def _relative_path(value: Any, label: str) -> Path:
    if not isinstance(value, str) or not value:
        raise ReportError(f"{label} has no file path")
    path = Path(value)
    if path.is_absolute() or any(part in ("", ".", "..") for part in path.parts):
        raise ReportError(f"{label} has an unsafe file path: {value}")
    return path


def _find_repository_file(root: Path, raw_path: Any, label: str) -> Path:
    relative = _relative_path(raw_path, label)
    candidates = (root, root.parent, root.parent.parent)
    found: list[Path] = []
    for base in candidates:
        candidate = (base / relative).resolve()
        try:
            candidate.relative_to(base.resolve())
        except ValueError:
            continue
        if candidate.is_file() and candidate not in found:
            found.append(candidate)
    if not found:
        raise ReportError(f"cannot find {label}: {relative}")
    if len(found) > 1:
        raise ReportError(f"{label} is ambiguous below the benchmark ancestors: {relative}")
    return found[0]


def _require_sha_match(path: Path, expected: Any, label: str) -> None:
    if not _hex_digest(expected):
        raise ReportError(f"{label} has no valid recorded SHA-256")
    actual = _file_digest(path)
    if actual != expected:
        raise ReportError(
            f"{label} changed after it was frozen: expected {expected}, found {actual}"
        )


def _frozen_artifact(
    root: Path,
    frozen: Mapping[str, Any],
    environment_copy: Mapping[str, Any],
    *,
    path_field: str,
    digest_field: str,
    label: str,
) -> tuple[Path, Mapping[str, Any]]:
    raw_path = frozen.get(path_field)
    expected = frozen.get(digest_field)
    if raw_path != environment_copy.get(path_field):
        raise ReportError(f"{label} path disagrees across frozen metadata")
    if expected != environment_copy.get(digest_field):
        raise ReportError(f"{label} SHA-256 disagrees across frozen metadata")
    path = _find_repository_file(root, raw_path, label)
    _require_sha_match(path, expected, label)
    return path, _object(path, label)


def _find_freeze_check(analysis_path: Path) -> tuple[Path, Mapping[str, Any]]:
    analysis = analysis_path.resolve()
    candidates = []
    for candidate in (
        analysis.parent / "freeze_check.json",
        analysis.parent.parent / "freeze_check.json",
    ):
        candidate = candidate.resolve()
        if candidate.is_file() and candidate not in candidates:
            candidates.append(candidate)
    if len(candidates) != 1:
        raise ReportError(
            "the analysis must have exactly one adjacent authenticated freeze_check.json"
        )
    return candidates[0], _object(candidates[0], "frozen-run verification")


def _controlled_manifest(path: Path, label: str) -> Mapping[str, Any]:
    try:
        return load_manifest(path)
    except BenchmarkToolError as error:
        raise ReportError(f"invalid {label}: {error}") from error


def _resolve_construction_check(
    root: Path,
    evidence_dir: Path,
    library_probe: Mapping[str, Any],
) -> Mapping[str, Any]:
    """Resolve and authenticate the complete construction evidence.

    ``library_dependency_probe.json`` is intentionally a small pointer now.
    Its target must remain inside the benchmark's evidence directory, and its
    recorded byte digest is checked before the target JSON is trusted.
    """

    pointer_kind = "highambench-library-dependency-evidence-pointer"
    check_kind = "highambench-private-construction-check"
    kind = library_probe.get("kind")
    if kind == check_kind:
        # A direct record is accepted here, but the same complete verification
        # basis and complete manifest-result checks are still required below.
        return library_probe
    if kind != pointer_kind:
        raise ReportError(
            "library_dependency_probe.json is neither a construction check nor its current pointer"
        )

    target = _find_repository_file(
        root,
        library_probe.get("current_evidence"),
        "current library construction evidence",
    )
    evidence_root = evidence_dir.resolve()
    try:
        target.relative_to(evidence_root)
    except ValueError as error:
        raise ReportError(
            "current library construction evidence must remain inside metadata/evidence"
        ) from error
    pointer_path = (evidence_dir / "library_dependency_probe.json").resolve()
    if target == pointer_path or target.suffix != ".json":
        raise ReportError("current library construction evidence has an unsafe target")

    _require_sha_match(
        target,
        library_probe.get("current_evidence_sha256"),
        "current library construction evidence",
    )
    check = _object(target, "current library construction evidence")
    if check.get("kind") != check_kind:
        raise ReportError(
            "current library construction evidence is not a highambench-private-construction-check"
        )
    return check


def _task_records(
    manifest: Mapping[str, Any],
) -> tuple[list[str], list[tuple[str, Mapping[str, Any]]]]:
    papers = manifest.get("papers")
    if not isinstance(papers, list) or not papers or not all(
        isinstance(paper, Mapping) for paper in papers
    ):
        raise ReportError("the report requires a nonempty manifest paper list")
    paper_ids: list[str] = []
    task_records: list[tuple[str, Mapping[str, Any]]] = []
    seen_tasks: set[Any] = set()
    for paper in papers:
        assert isinstance(paper, Mapping)
        paper_id = paper.get("paper_id")
        if not isinstance(paper_id, str) or not paper_id or paper_id in paper_ids:
            raise ReportError("manifest paper IDs must be distinct and nonempty")
        paper_ids.append(paper_id)
        targets = paper.get("targets")
        if not isinstance(targets, list) or not targets or not all(
            isinstance(item, Mapping) for item in targets
        ):
            raise ReportError(f"manifest paper {paper_id} has no usable target list")
        seen_tiers: set[Any] = set()
        for target in targets:
            assert isinstance(target, Mapping)
            if target.get("availability") != "available":
                continue
            tier = target.get("tier")
            task_id = target.get("task_id")
            if (
                not isinstance(tier, str)
                or task_id != f"{paper_id}-{tier}"
                or task_id in seen_tasks
                or tier in seen_tiers
            ):
                raise ReportError(f"manifest has an invalid or repeated task for {paper_id}")
            seen_tiers.add(tier)
            seen_tasks.add(task_id)
            task_records.append((paper_id, target))
    if not task_records:
        raise ReportError("the manifest has no available tasks")
    return paper_ids, task_records


def load_report_inputs(benchmark_root: Path, analysis_path: Path) -> ReportInputs:
    """Read every input used by the report and perform construction checks."""

    root = benchmark_root.resolve()
    if not root.is_dir():
        raise ReportError(f"benchmark root is not a directory: {root}")
    metadata = root / "metadata"
    config = _object(metadata / "config.json", "configuration metadata")
    environment = _object(metadata / "environment.json", "environment metadata")
    manifest = _object(metadata / "manifest.json", "benchmark manifest")
    run_order = _object(metadata / "run_order.json", "run-order metadata")
    analysis = _object(analysis_path.resolve(), "analysis output")

    frozen = config.get("frozen_environment")
    lean_environment = environment.get("lean")
    runtime_environment = environment.get("runtime")
    if not isinstance(frozen, Mapping):
        raise ReportError("configuration metadata has no frozen environment")
    if not isinstance(lean_environment, Mapping):
        raise ReportError("environment metadata has no Lean environment record")
    if not isinstance(runtime_environment, Mapping):
        raise ReportError("environment metadata has no runtime record")

    release_path, _ = _frozen_artifact(
        root,
        frozen,
        environment,
        path_field="release_manifest",
        digest_field="release_manifest_sha256",
        label="evaluation release manifest",
    )
    source_path, _ = _frozen_artifact(
        root,
        frozen,
        lean_environment,
        path_field="numstability_source_manifest",
        digest_field="numstability_source_manifest_sha256",
        label="NumStability source manifest",
    )
    compiled_path, _ = _frozen_artifact(
        root,
        frozen,
        lean_environment,
        path_field="numstability_compiled_manifest",
        digest_field="numstability_compiled_manifest_sha256",
        label="pruned NumStability compiled manifest",
    )
    _, compiled_environment_summary = _frozen_artifact(
        root,
        frozen,
        lean_environment,
        path_field="compiled_environment_summary",
        digest_field="compiled_environment_summary_sha256",
        label="compiled Lean environment summary",
    )
    packages_runtime_path, _ = _frozen_artifact(
        root,
        frozen,
        runtime_environment,
        path_field="packages_runtime_manifest",
        digest_field="packages_runtime_manifest_sha256",
        label="pruned package-runtime manifest",
    )
    _, freeze_check = _find_freeze_check(analysis_path)
    release_manifest = _controlled_manifest(release_path, "evaluation release manifest")
    source_manifest = _controlled_manifest(source_path, "NumStability source manifest")
    compiled_manifest = _controlled_manifest(
        compiled_path, "pruned NumStability compiled manifest"
    )
    packages_runtime_manifest = _controlled_manifest(
        packages_runtime_path, "pruned package-runtime manifest"
    )

    paper_ids, manifest_tasks = _task_records(manifest)
    papers = tuple(
        _object(root / "tasks" / paper_id / "paper.json", f"{paper_id} paper metadata")
        for paper_id in paper_ids
    )
    tasks: list[Mapping[str, Any]] = []
    for paper_id, target in manifest_tasks:
        tier = target.get("tier")
        task_id = target.get("task_id")
        task = _object(
            root / "tasks" / paper_id / str(tier) / "task.json",
            f"{task_id} task metadata",
        )
        if (
            task.get("task_id") != task_id
            or task.get("paper_id") != paper_id
            or task.get("tier") != tier
        ):
            raise ReportError(f"{task_id} task metadata disagrees with the manifest")
        tasks.append(task)

    evidence_dir = metadata / "evidence"
    evidence_paths = sorted(evidence_dir.glob("*.json")) if evidence_dir.is_dir() else []
    evidence = {path.stem: _object(path, f"construction evidence {path.name}") for path in evidence_paths}
    if "library_dependency_probe" not in evidence:
        raise ReportError("missing required construction evidence: library_dependency_probe.json")
    if not any(name.startswith("exact_target_search") for name in evidence):
        raise ReportError("missing exact-target-search construction evidence")
    construction_check = _resolve_construction_check(
        root,
        evidence_dir,
        evidence["library_dependency_probe"],
    )

    review_dir = metadata / "reviews"
    review_paths = sorted(review_dir.glob("*.json")) if review_dir.is_dir() else []
    if len(review_paths) < 2:
        raise ReportError("at least two independent review records are required")
    all_reviews = tuple(_object(path, f"review record {path.name}") for path in review_paths)
    reviews = tuple(
        review
        for review in all_reviews
        if review.get("record_status") in (None, "current_final")
    )
    if len(reviews) < 2:
        raise ReportError(
            "at least two current final review records are required; construction snapshots do not count"
        )

    raw_shared_entries = manifest.get("controlled_shared_files")
    if not isinstance(raw_shared_entries, list) or not raw_shared_entries:
        raise ReportError("manifest has no controlled shared Lean files")
    shared_sources: list[str] = []
    for index, raw_entry in enumerate(raw_shared_entries):
        if not isinstance(raw_entry, Mapping):
            raise ReportError(f"controlled shared Lean entry {index} is invalid")
        shared_path = _find_repository_file(
            root, raw_entry.get("path"), f"controlled shared Lean file {index}"
        )
        shared_sources.append(shared_path.read_text(encoding="utf-8"))
    shared_source = "\n".join(shared_sources)

    result = ReportInputs(
        benchmark_root=root,
        config=config,
        environment=environment,
        manifest=manifest,
        run_order=run_order,
        papers=papers,
        tasks=tuple(tasks),
        evidence=evidence,
        construction_check=construction_check,
        freeze_check=freeze_check,
        release_manifest=release_manifest,
        compiled_environment_summary=compiled_environment_summary,
        packages_runtime_manifest=packages_runtime_manifest,
        source_manifest=source_manifest,
        compiled_manifest=compiled_manifest,
        reviews=reviews,
        analysis=analysis,
        shared_source=shared_source,
    )
    validate_report_inputs(result)
    return result


def _require_list(value: Any, label: str) -> list[Any]:
    if not isinstance(value, list):
        raise ReportError(f"incomplete analysis: {label} is not a list")
    return value


def _analysis_tables(analysis: Mapping[str, Any]) -> tuple[
    list[Mapping[str, Any]],
    list[Mapping[str, Any]],
    list[Mapping[str, Any]],
    list[Mapping[str, Any]],
    bool,
]:
    """Return the four result tables and whether they are observational."""

    official = analysis.get("official_scores_valid") is True
    if official:
        raw_tables = (
            analysis.get("condition_summaries"),
            analysis.get("per_task_summaries"),
            analysis.get("paired_comparisons"),
            analysis.get("per_task_paired_comparisons"),
        )
        observational = False
    else:
        pilot = analysis.get("observational_pilot_results")
        if not isinstance(pilot, Mapping):
            raise ReportError(
                "incomplete analysis: invalid official scores require a complete, clearly labeled observational result block"
            )
        label = str(pilot.get("label", "")).lower()
        if "observational" not in label or "not" not in label or "score" not in label:
            raise ReportError("incomplete analysis: the observational result block lacks its warning label")
        raw_tables = (
            pilot.get("condition_summaries"),
            pilot.get("per_task_summaries"),
            pilot.get("paired_comparisons"),
            pilot.get("per_task_paired_comparisons"),
        )
        observational = True
    tables: list[list[Mapping[str, Any]]] = []
    for name, raw in zip(
        ("condition summaries", "task summaries", "paired summaries", "task paired summaries"),
        raw_tables,
    ):
        values = _require_list(raw, name)
        if not values or not all(isinstance(row, Mapping) for row in values):
            raise ReportError(f"incomplete analysis: {name} is empty or malformed")
        tables.append(list(values))
    return tables[0], tables[1], tables[2], tables[3], observational


def _check_matrix_coverage(
    inputs: ReportInputs,
    selected_runs: Sequence[Mapping[str, Any]],
    condition_rows: Sequence[Mapping[str, Any]],
    task_rows: Sequence[Mapping[str, Any]],
    pair_rows: Sequence[Mapping[str, Any]],
    task_pair_rows: Sequence[Mapping[str, Any]],
) -> None:
    task_ids = {str(task.get("task_id")) for task in inputs.tasks}
    repetitions = inputs.config.get("repetitions")
    if not isinstance(repetitions, list) or not repetitions:
        raise ReportError("configuration metadata has no repetitions")
    repetition_ids = {
        item.get("id") for item in repetitions if isinstance(item, Mapping) and isinstance(item.get("id"), str)
    }
    if len(repetition_ids) != len(repetitions):
        raise ReportError("configuration metadata has malformed or repeated repetitions")
    expected = {
        (task_id, repetition_id, condition)
        for task_id in task_ids
        for repetition_id in repetition_ids
        for condition in ("N", "L")
    }
    actual = {
        (run.get("task_id"), run.get("repetition_id"), run.get("condition"))
        for run in selected_runs
    }
    if actual != expected or len(selected_runs) != len(expected):
        raise ReportError("incomplete analysis: selected final runs do not cover the fixed task matrix exactly")

    overall_conditions = {
        row.get("condition") for row in condition_rows if row.get("scope") == "overall"
    }
    if overall_conditions != {"N", "L"}:
        raise ReportError("incomplete analysis: overall N and L condition rows are required")
    task_conditions = {(row.get("task_id"), row.get("condition")) for row in task_rows}
    if task_conditions != {(task_id, condition) for task_id in task_ids for condition in ("N", "L")}:
        raise ReportError("incomplete analysis: each task needs both an N and an L summary")
    if "overall" not in {row.get("scope") for row in pair_rows}:
        raise ReportError("incomplete analysis: the overall paired-change row is missing")
    if {row.get("task_id") for row in task_pair_rows} != task_ids:
        raise ReportError("incomplete analysis: each task needs a paired-change row")


def _release_file_hashes(inputs: ReportInputs) -> dict[str, str]:
    files = inputs.release_manifest.get("files")
    if not isinstance(files, list):
        raise ReportError("evaluation release manifest has no file list")
    result: dict[str, str] = {}
    for entry in files:
        if not isinstance(entry, Mapping):
            raise ReportError("evaluation release manifest contains a malformed entry")
        path = entry.get("path")
        digest = entry.get("sha256")
        if not isinstance(path, str) or not _hex_digest(digest) or path in result:
            raise ReportError("evaluation release manifest contains an invalid file identity")
        result[path] = digest
    return result


def _artifact_path_below_benchmark(
    inputs: ReportInputs, raw_path: Any, label: str
) -> str:
    path = _find_repository_file(inputs.benchmark_root, raw_path, label)
    try:
        return path.relative_to(inputs.benchmark_root).as_posix()
    except ValueError as error:
        raise ReportError(f"{label} is not inside the benchmark release") from error


def _validate_tree_summary(record: Any, label: str) -> tuple[int, int]:
    if not isinstance(record, Mapping):
        raise ReportError(f"compiled environment summary has no {label} tree")
    file_count = record.get("file_count")
    total_bytes = record.get("total_bytes")
    if (
        not isinstance(file_count, int)
        or isinstance(file_count, bool)
        or file_count <= 0
        or not isinstance(total_bytes, int)
        or isinstance(total_bytes, bool)
        or total_bytes < 0
        or not _hex_digest(record.get("tree_sha256"))
    ):
        raise ReportError(f"compiled environment summary has an invalid {label} identity")
    return file_count, total_bytes


def _validate_release_and_environment(inputs: ReportInputs) -> None:
    """Check the release manifest and the three separately frozen tree records."""

    try:
        release_check = verify_manifest(inputs.benchmark_root, dict(inputs.release_manifest))
    except BenchmarkToolError as error:
        raise ReportError(f"cannot verify the evaluation release manifest: {error}") from error
    if not release_check.get("ok"):
        raise ReportError(
            "evaluation release files changed after freezing: " + str(release_check)
        )

    frozen = inputs.config.get("frozen_environment")
    lean = inputs.environment.get("lean")
    if not isinstance(frozen, Mapping) or not isinstance(lean, Mapping):
        raise ReportError("frozen Lean environment metadata is missing")
    release_hashes = _release_file_hashes(inputs)
    required_release_paths = set(CONSTRUCTION_TOOL_PATHS)
    for path_field, digest_field, label in (
        (
            "numstability_source_manifest",
            "numstability_source_manifest_sha256",
            "NumStability source manifest",
        ),
        (
            "numstability_compiled_manifest",
            "numstability_compiled_manifest_sha256",
            "pruned NumStability compiled manifest",
        ),
        (
            "compiled_environment_summary",
            "compiled_environment_summary_sha256",
            "compiled Lean environment summary",
        ),
        (
            "packages_runtime_manifest",
            "packages_runtime_manifest_sha256",
            "pruned package-runtime manifest",
        ),
    ):
        relative = _artifact_path_below_benchmark(inputs, frozen.get(path_field), label)
        required_release_paths.add(relative)
        if release_hashes.get(relative) != frozen.get(digest_field):
            raise ReportError(f"evaluation release does not authenticate the {label}")
    missing = sorted(required_release_paths - set(release_hashes))
    if missing:
        raise ReportError(
            "evaluation release omits construction/runtime files: " + ", ".join(missing)
        )

    source_files = inputs.source_manifest.get("files")
    compiled_files = inputs.compiled_manifest.get("files")
    if (
        not isinstance(source_files, list)
        or not source_files
        or not all(
            isinstance(entry, Mapping)
            and (
                entry.get("path") == "NumStability.lean"
                or str(entry.get("path", "")).startswith("NumStability/")
            )
            for entry in source_files
        )
    ):
        raise ReportError("NumStability source manifest is empty or includes another tree")
    if (
        not isinstance(compiled_files, list)
        or not compiled_files
        or not all(
            isinstance(entry, Mapping)
            and str(entry.get("path", "")).startswith("NumStability/")
            for entry in compiled_files
        )
    ):
        raise ReportError("pruned compiled manifest is empty or includes another namespace")

    runtime_files = inputs.packages_runtime_manifest.get("files")
    runtime_paths = {
        str(entry.get("path"))
        for entry in runtime_files
        if isinstance(entry, Mapping)
    } if isinstance(runtime_files, list) else set()
    runtime_kinds = {
        path: _package_runtime_file_kind(path) for path in runtime_paths
    }
    bad_runtime_paths = {
        path for path, kind in runtime_kinds.items() if kind is None
    }
    if (
        not isinstance(runtime_files, list)
        or not runtime_files
        or len(runtime_paths) != len(runtime_files)
        or bad_runtime_paths
        or "mathlib/Mathlib.lean" not in runtime_paths
        or "olean" not in runtime_kinds.values()
        or "compiled_support" not in runtime_kinds.values()
    ):
        raise ReportError(
            "pruned package-runtime manifest is not exactly mathlib source plus "
            "package .olean, .olean.server, .olean.private, and .ir files"
        )

    runtime_environment = inputs.environment.get("runtime")
    python_record = (
        runtime_environment.get("python")
        if isinstance(runtime_environment, Mapping)
        else None
    )
    if (
        not isinstance(python_record, Mapping)
        or not isinstance(frozen.get("python_version"), str)
        or not frozen.get("python_version")
        or frozen.get("python_version") != python_record.get("version")
        or not _hex_digest(frozen.get("python_binary_sha256"))
        or frozen.get("python_binary_sha256") != python_record.get("binary_sha256")
    ):
        raise ReportError("Python executable identity is missing or inconsistent")

    summary = inputs.compiled_environment_summary
    if (
        summary.get("schema_version") != 1
        or summary.get("kind") != "highambench-compiled-environment-summary"
    ):
        raise ReportError("compiled Lean environment summary has the wrong format")
    toolchain_summary = summary.get("toolchain")
    _validate_tree_summary(toolchain_summary, "Lean toolchain")
    if not isinstance(toolchain_summary, Mapping) or toolchain_summary.get(
        "relative_root"
    ) != ".":
        raise ReportError("compiled environment summary does not cover the whole Lean toolchain")
    packages = summary.get("packages")
    if not isinstance(packages, list) or not packages:
        raise ReportError("compiled Lean environment summary has no package trees")
    package_names: set[str] = set()
    for package in packages:
        if not isinstance(package, Mapping) or not isinstance(package.get("package"), str):
            raise ReportError("compiled Lean environment summary has a malformed package")
        name = str(package["package"])
        if name in package_names:
            raise ReportError("compiled Lean environment summary repeats a package")
        package_names.add(name)
        _validate_tree_summary(package, f"{name} package")
    if "mathlib" not in package_names:
        raise ReportError("compiled Lean environment summary does not include mathlib")


def _identity_matches_manifest(
    identity: Any,
    manifest: Mapping[str, Any],
    *,
    expected_relative_path: str,
    expected_sha256: Any,
    label: str,
) -> None:
    files = manifest.get("files")
    if not isinstance(identity, Mapping) or not isinstance(files, list):
        raise ReportError(f"construction evidence has no {label} identity")
    file_count = len(files)
    total_bytes = sum(
        entry.get("bytes", -1) if isinstance(entry, Mapping) else -1 for entry in files
    )
    if (
        identity.get("path") != expected_relative_path
        or identity.get("sha256") != expected_sha256
        or identity.get("label") != manifest.get("label")
        or identity.get("file_count") != file_count
        or identity.get("verified") != file_count
        or identity.get("total_bytes") != total_bytes
        or identity.get("exact_tree") is not True
    ):
        raise ReportError(f"construction evidence has a stale or incomplete {label} identity")


def _validate_construction(inputs: ReportInputs) -> None:
    search_records = [
        record
        for name, record in inputs.evidence.items()
        if name.startswith("exact_target_search")
    ]
    all_findings: list[Mapping[str, Any]] = []
    recorded_hashes: dict[str, Any] = {}
    raw_manifest_shared = inputs.manifest.get("controlled_shared_files")
    if not isinstance(raw_manifest_shared, list):
        raise ReportError("manifest has no controlled shared Lean files")
    manifest_shared: dict[str, Mapping[str, Any]] = {}
    for raw_entry in raw_manifest_shared:
        if not isinstance(raw_entry, Mapping) or not isinstance(raw_entry.get("path"), str):
            raise ReportError("manifest has an invalid controlled shared Lean entry")
        manifest_shared[str(raw_entry["path"])] = raw_entry
    for search in search_records:
        conclusion = search.get("overall_conclusion")
        findings = search.get("task_findings")
        hashes = search.get("fixed_surface_hashes")
        if (
            not isinstance(conclusion, Mapping)
            or conclusion.get("tier_labels_supported_by_library_surface") is not True
            or any(
                value is not True
                for key, value in conclusion.items()
                if key.endswith("exact_targets_absent")
                or key.endswith("semantic_duplicates_absent")
            )
            or not isinstance(findings, list)
            or not findings
            or not all(isinstance(item, Mapping) for item in findings)
            or not isinstance(hashes, Mapping)
        ):
            raise ReportError("an exact-target-search record is incomplete or failed")
        if not all(
            item.get("exact_duplicate_found") is False
            and item.get("semantic_duplicate_found") is False
            for item in findings
        ):
            raise ReportError("an exact or semantic target duplicate was found")
        finding_papers = {
            str(item.get("task_id", "")).split("-", 1)[0]
            for item in findings
        }
        expected_shared = {
            path: entry.get("sha256")
            for path, entry in manifest_shared.items()
            if isinstance(entry.get("paper_ids"), list)
            and finding_papers.intersection(str(value) for value in entry["paper_ids"])
        }
        recorded_shared = hashes.get("shared_files")
        if not isinstance(recorded_shared, list) or any(
            not isinstance(item, Mapping) for item in recorded_shared
        ):
            raise ReportError("a target-absence search used a stale shared Lean surface")
        recorded_shared_map = {
            str(item.get("path")): item.get("sha256") for item in recorded_shared
        }
        if recorded_shared_map != expected_shared:
            raise ReportError("a target-absence search used a stale shared Lean surface")
        all_findings.extend(findings)
        for key, value in hashes.items():
            if key == "shared_files":
                continue
            if key in recorded_hashes:
                raise ReportError(f"target-absence searches repeat {key}")
            recorded_hashes[key] = value

    expected_task_ids = {task.get("task_id") for task in inputs.tasks}
    finding_ids = [item.get("task_id") for item in all_findings]
    if set(finding_ids) != expected_task_ids or len(finding_ids) != len(set(finding_ids)):
        raise ReportError("the target-absence searches do not cover every task exactly once")
    manifest_targets = {item.get("task_id"): item for item in _manifest_targets(inputs)}
    for task_id, target in manifest_targets.items():
        recorded = recorded_hashes.get(str(task_id))
        lean_target = target.get("lean_target")
        if (
            not isinstance(recorded, Mapping)
            or not isinstance(lean_target, Mapping)
            or recorded.get("sha256") != lean_target.get("controlled_file_sha256")
        ):
            raise ReportError(f"the target-absence search used a stale surface for {task_id}")

    check = inputs.construction_check
    summary = check.get("summary")
    results = check.get("results")
    task_count = len(inputs.tasks)
    proof_count = task_count * 2
    if (
        check.get("kind") != "highambench-private-construction-check"
        or check.get("pass") is not True
        or not isinstance(summary, Mapping)
        or summary.get("expected") != proof_count
        or summary.get("checked") != proof_count
        or summary.get("passed") != proof_count
        or summary.get("condition_n_passed") != task_count
        or summary.get("condition_l_passed") != task_count
        or not isinstance(results, list)
        or len(results) != proof_count
        or not all(isinstance(result, Mapping) for result in results)
    ):
        raise ReportError("the private construction check is incomplete or failed")

    construction_isolation = check.get("isolation")
    if (
        not isinstance(construction_isolation, Mapping)
        or construction_isolation.get(
            "condition_n_preflight_after_complete_controlled_staging"
        )
        is not True
        or construction_isolation.get("condition_n_numstability_mounts_configured")
        is not False
        or construction_isolation.get("condition_l_numstability_mounts_configured")
        is not True
    ):
        raise ReportError("construction isolation order or condition mounts are not authenticated")

    basis = check.get("verification_basis")
    if not isinstance(basis, Mapping):
        raise ReportError("private construction check has no authenticated verification basis")
    tool_hashes = basis.get("tools")
    release_hashes = _release_file_hashes(inputs)
    if not isinstance(tool_hashes, Mapping) or set(tool_hashes) != set(
        CONSTRUCTION_TOOL_PATHS
    ):
        raise ReportError("construction evidence does not name the exact checker tool set")
    for relative in CONSTRUCTION_TOOL_PATHS:
        digest = tool_hashes.get(relative)
        if not _hex_digest(digest) or release_hashes.get(relative) != digest:
            raise ReportError(
                f"construction checker {relative} is not authenticated by the release"
            )

    environment_isolation = inputs.environment.get("isolation")
    if not isinstance(environment_isolation, Mapping):
        raise ReportError("environment isolation metadata is missing")
    for relative, field in (
        ("tools/lean_isolated.py", "lean_adapter_sha256"),
        ("tools/validator.py", "validator_sha256"),
        ("tools/dependency_audit.lean", "dependency_audit_sha256"),
    ):
        if tool_hashes.get(relative) != environment_isolation.get(field):
            raise ReportError(f"construction checker {relative} disagrees with the environment")

    frozen = inputs.config.get("frozen_environment")
    lean_environment = inputs.environment.get("lean")
    runtime_environment = inputs.environment.get("runtime")
    runtime_python = (
        runtime_environment.get("python")
        if isinstance(runtime_environment, Mapping)
        else None
    )
    if (
        not isinstance(frozen, Mapping)
        or not isinstance(lean_environment, Mapping)
        or not isinstance(runtime_environment, Mapping)
        or not isinstance(runtime_python, Mapping)
    ):
        raise ReportError("frozen runtime and library identities are missing")

    executables = basis.get("executables")
    python_executable = executables.get("python") if isinstance(executables, Mapping) else None
    bubblewrap = executables.get("bubblewrap") if isinstance(executables, Mapping) else None
    if (
        not isinstance(python_executable, Mapping)
        or not Path(str(python_executable.get("path", ""))).is_absolute()
        or python_executable.get("sha256") != frozen.get("python_binary_sha256")
        or python_executable.get("sha256") != runtime_python.get("binary_sha256")
        or python_executable.get("version") != frozen.get("python_version")
        or python_executable.get("version") != runtime_python.get("version")
        or not isinstance(bubblewrap, Mapping)
        or not Path(str(bubblewrap.get("path", ""))).is_absolute()
        or not _hex_digest(bubblewrap.get("sha256"))
        or bubblewrap.get("sha256")
        != environment_isolation.get("bubblewrap_binary_sha256")
    ):
        raise ReportError("construction executable identities are incomplete or inconsistent")

    source_relative = _artifact_path_below_benchmark(
        inputs, frozen.get("numstability_source_manifest"), "NumStability source manifest"
    )
    compiled_relative = _artifact_path_below_benchmark(
        inputs,
        frozen.get("numstability_compiled_manifest"),
        "pruned NumStability compiled manifest",
    )
    _identity_matches_manifest(
        basis.get("numstability_source"),
        inputs.source_manifest,
        expected_relative_path=source_relative,
        expected_sha256=frozen.get("numstability_source_manifest_sha256"),
        label="NumStability source manifest",
    )
    _identity_matches_manifest(
        basis.get("numstability_compiled"),
        inputs.compiled_manifest,
        expected_relative_path=compiled_relative,
        expected_sha256=frozen.get("numstability_compiled_manifest_sha256"),
        label="pruned NumStability compiled manifest",
    )
    packages_relative = _artifact_path_below_benchmark(
        inputs,
        frozen.get("packages_runtime_manifest"),
        "pruned package-runtime manifest",
    )
    _identity_matches_manifest(
        basis.get("packages_runtime"),
        inputs.packages_runtime_manifest,
        expected_relative_path=packages_relative,
        expected_sha256=frozen.get("packages_runtime_manifest_sha256"),
        label="pruned package-runtime manifest",
    )
    compiled_basis = basis.get("numstability_compiled")
    expected_mount = (
        inputs.benchmark_root.parent.parent / PRUNED_LIBRARY_OLEAN_ROOT
    ).resolve()
    if (
        not isinstance(compiled_basis, Mapping)
        or compiled_basis.get("only_numstability_namespace") is not True
        or not isinstance(compiled_basis.get("mount_root"), str)
        or not Path(str(compiled_basis.get("mount_root", ""))).is_absolute()
        or Path(str(compiled_basis["mount_root"])).resolve() != expected_mount
    ):
        raise ReportError("construction evidence did not use the exact pruned library mount")
    packages_basis = basis.get("packages_runtime")
    packages_manifest_files = inputs.packages_runtime_manifest.get("files")
    packages_manifest_paths = [
        str(entry.get("path"))
        for entry in packages_manifest_files
        if isinstance(entry, Mapping)
    ] if isinstance(packages_manifest_files, list) else []
    packages_source_count = sum(
        _package_runtime_file_kind(path) == "source"
        for path in packages_manifest_paths
    )
    packages_olean_count = sum(
        _package_runtime_file_kind(path) == "olean"
        for path in packages_manifest_paths
    )
    packages_support_count = sum(
        _package_runtime_file_kind(path) == "compiled_support"
        for path in packages_manifest_paths
    )
    expected_packages_mount = (
        inputs.benchmark_root.parent.parent / PACKAGES_RUNTIME_ROOT
    ).resolve()
    if (
        not isinstance(packages_basis, Mapping)
        or packages_basis.get(
            "only_mathlib_source_and_lean_compiled_artifacts"
        ) is not True
        or packages_basis.get("mathlib_source_file_count")
        != packages_source_count
        or packages_basis.get("base_olean_file_count") != packages_olean_count
        or packages_basis.get("compiled_support_file_count")
        != packages_support_count
        or not isinstance(packages_basis.get("mount_root"), str)
        or not Path(str(packages_basis.get("mount_root", ""))).is_absolute()
        or Path(str(packages_basis["mount_root"])).resolve()
        != expected_packages_mount
    ):
        raise ReportError("construction evidence did not use the exact pruned package mount")

    shared_olean = basis.get("shared_olean")
    environment_bundles = lean_environment.get("shared_olean_bundles")
    expected_shared_olean_count = (
        sum(len(bundle) for bundle in environment_bundles.values())
        if isinstance(environment_bundles, Mapping)
        and all(isinstance(bundle, Mapping) for bundle in environment_bundles.values())
        else -1
    )
    if (
        not isinstance(shared_olean, Mapping)
        or not isinstance(shared_olean.get("bundles"), Mapping)
        or dict(shared_olean["bundles"])
        != dict(environment_bundles or {})
        or shared_olean.get("exact_file_count") != expected_shared_olean_count
    ):
        raise ReportError("construction evidence used a stale or non-minimal shared Lean tree")

    freeze_lean = inputs.freeze_check.get("lean")
    if (
        not isinstance(freeze_lean, Mapping)
        or freeze_lean.get("source_files_verified")
        != len(inputs.source_manifest.get("files", []))
        or freeze_lean.get("compiled_files_verified")
        != len(inputs.compiled_manifest.get("files", []))
    ):
        raise ReportError("construction library counts disagree with the frozen run startup")

    task_tiers = {
        str(task.get("task_id")): str(task.get("tier")) for task in inputs.tasks
    }
    expected_results = {
        (task_id, condition)
        for task_id in task_tiers
        for condition in ("N", "L")
    }
    actual_results = {
        (result.get("task_id"), result.get("condition"))
        for result in results
    }
    if actual_results != expected_results or len(actual_results) != len(results):
        raise ReportError(
            "the private construction check does not contain exactly one N and one L proof for every task"
        )

    for result in results:
        task_id = str(result.get("task_id"))
        condition = str(result.get("condition"))
        label = f"{task_id}/{condition} private construction proof"
        validation = result.get("validation")
        audit = validation.get("dependency_audit") if isinstance(validation, Mapping) else None
        if (
            result.get("tier") != task_tiers[task_id]
            or result.get("pass") is not True
            or not isinstance(validation, Mapping)
            or validation.get("pass") is not True
            or type(validation.get("compile_exit_code")) is not int
            or validation.get("compile_exit_code") != 0
            or validation.get("compile_timed_out") is not False
            or validation.get("statement_unchanged") is not True
            or validation.get("controlled_before_ok") is not True
            or validation.get("controlled_hidden_ok") is not True
            or validation.get("failure_code") is not None
            or validation.get("static_finding_count") != 0
            or not isinstance(audit, Mapping)
            or audit.get("complete") is not True
            or type(audit.get("exit_code")) is not int
            or audit.get("exit_code") != 0
            or audit.get("format_version") != 2
            or audit.get("forbidden_dependency_count") != 0
            or audit.get("missing_helper_modules") != []
            or not isinstance(audit.get("library_declarations"), list)
        ):
            raise ReportError(f"{label} has an incomplete compile or dependency record")

        declarations = audit["library_declarations"]
        if condition == "N":
            n_preflight = result.get("n_preflight")
            import_probe = (
                n_preflight.get("import_probe")
                if isinstance(n_preflight, Mapping)
                else None
            )
            staged = (
                n_preflight.get("controlled_files_verified_after_staging")
                if isinstance(n_preflight, Mapping)
                else None
            )
            scan = (
                n_preflight.get("filesystem_scan")
                if isinstance(n_preflight, Mapping)
                else None
            )
            if (
                not isinstance(n_preflight, Mapping)
                or n_preflight.get("ok") is not True
                or n_preflight.get("complete") is not True
                or n_preflight.get("filesystem_leaks") != []
                or n_preflight.get("controlled_manifest_sha256")
                != result.get("manifest_sha256")
                or not _hex_digest(result.get("manifest_sha256"))
                or not isinstance(staged, Mapping)
                or staged.get("ok") is not True
                or not isinstance(staged.get("expected"), int)
                or isinstance(staged.get("expected"), bool)
                or staged.get("expected") <= 0
                or staged.get("verified") != staged.get("expected")
                or staged.get("missing") != []
                or staged.get("changed") != []
                or not isinstance(scan, Mapping)
                or scan.get("root") != "."
                or not isinstance(scan.get("regular_file_count"), int)
                or isinstance(scan.get("regular_file_count"), bool)
                or scan.get("regular_file_count") < staged.get("expected")
                or scan.get("symlink_count") != 0
                or not isinstance(scan.get("markers"), list)
                or "NumStability" not in scan.get("markers")
                or not isinstance(import_probe, Mapping)
                or import_probe.get("attempted") is not True
                or import_probe.get("reliable") is not True
                or import_probe.get("importable") is not False
            ):
                raise ReportError(
                    f"{label} did not scan the complete staged task before private gold was copied"
                )
            if (
                result.get("condition_n_library_arguments_omitted") is not True
                or audit.get("library_use") is not False
                or declarations != []
            ):
                raise ReportError(f"{label} does not prove NumStability was absent")
        elif (
            result.get("condition_n_library_arguments_omitted") is not False
            or audit.get("library_use") is not True
            or not declarations
            or not all(
                isinstance(declaration, Mapping)
                and isinstance(declaration.get("name"), str)
                and declaration.get("name")
                for declaration in declarations
            )
            or not any(
                str(declaration.get("name")).startswith("NumStability.")
                for declaration in declarations
            )
        ):
            raise ReportError(f"{label} does not record real NumStability library use")

    if not inputs.shared_source.strip() or "namespace HighamBench" not in inputs.shared_source:
        raise ReportError("the controlled shared Lean setting is empty or has the wrong namespace")
    if any(
        line.strip().startswith("import NumStability")
        for line in inputs.shared_source.splitlines()
    ):
        raise ReportError("the controlled shared Lean setting imports NumStability")


def _validate_hashes_and_reviews(inputs: ReportInputs) -> None:
    benchmark_ids = {
        inputs.config.get("benchmark_id"),
        inputs.manifest.get("benchmark_id"),
        inputs.run_order.get("benchmark_id"),
    }
    if None in benchmark_ids or len(benchmark_ids) != 1:
        raise ReportError("benchmark_id disagrees across final metadata")
    manifest_paper_ids, _manifest_task_records = _task_records(inputs.manifest)
    if [paper.get("paper_id") for paper in inputs.papers] != manifest_paper_ids:
        raise ReportError("paper metadata disagrees with the manifest")
    if any(
        paper.get("classification_frozen_before_runs") is not True
        for paper in inputs.papers
    ) or any(
        task.get("classification_frozen_before_runs") is not True for task in inputs.tasks
    ):
        raise ReportError("task classifications are not measurement-ready")

    manifest_papers = inputs.manifest["papers"]
    manifest_spec = inputs.manifest.get("specification")
    if not isinstance(manifest_spec, Mapping):
        raise ReportError("benchmark specification metadata is missing")
    for manifest_paper, paper in zip(manifest_papers, inputs.papers):
        manifest_source = manifest_paper.get("source")
        paper_source = paper.get("source")
        paper_spec = paper.get("benchmark_specification")
        if not isinstance(manifest_source, Mapping) or not isinstance(paper_source, Mapping):
            raise ReportError(f"{paper.get('paper_id')} paper source metadata is missing")
        if manifest_source.get("sha256") != paper_source.get("sha256") or not _hex_digest(
            manifest_source.get("sha256")
        ):
            raise ReportError(f"{paper.get('paper_id')} paper SHA-256 disagrees")
        if not isinstance(paper_spec, Mapping):
            raise ReportError(f"{paper.get('paper_id')} specification metadata is missing")
        if manifest_spec.get("sha256") != paper_spec.get("sha256") or not _hex_digest(
            manifest_spec.get("sha256")
        ):
            raise ReportError(f"{paper.get('paper_id')} specification SHA-256 disagrees")

    frozen = inputs.config.get("frozen_environment")
    if not isinstance(frozen, Mapping):
        raise ReportError("configuration metadata has no frozen environment")
    if frozen.get("environment_id") != inputs.environment.get("environment_id"):
        raise ReportError("environment_id disagrees across final metadata")
    if frozen.get("environment_bundle_sha256") != inputs.environment.get(
        "environment_bundle_sha256"
    ) or not _hex_digest(inputs.environment.get("environment_bundle_sha256")):
        raise ReportError("environment bundle SHA-256 is missing or inconsistent")
    corpus_slug = "-".join(paper_id.lower() for paper_id in manifest_paper_ids)
    if frozen.get("environment_id") != (
        f"highambench-{corpus_slug}-" + str(frozen.get("environment_bundle_sha256"))[:16]
    ):
        raise ReportError("environment_id is not derived from the frozen environment bundle")
    prompt_path = inputs.benchmark_root / "agent_prompt.md"
    if not prompt_path.is_file():
        raise ReportError(f"missing fixed agent prompt: {prompt_path}")
    _require_sha_match(prompt_path, frozen.get("prompt_sha256"), "fixed agent prompt")

    shared_entries = inputs.manifest.get("controlled_shared_files")
    if not isinstance(shared_entries, list) or not shared_entries:
        raise ReportError("manifest must bind controlled shared Lean files")
    for index, shared_entry in enumerate(shared_entries):
        if not isinstance(shared_entry, Mapping):
            raise ReportError(f"controlled shared Lean entry {index} is invalid")
        shared_path = _find_repository_file(
            inputs.benchmark_root,
            shared_entry.get("path"),
            f"controlled shared Lean file {index}",
        )
        _require_sha_match(
            shared_path,
            shared_entry.get("sha256"),
            f"controlled shared Lean file {index}",
        )

    for _paper_id, target in _manifest_task_records:
        lean_target = target.get("lean_target")
        if not isinstance(lean_target, Mapping):
            raise ReportError(f"manifest task {target.get('task_id')} has no Lean target binding")
        target_path = _find_repository_file(
            inputs.benchmark_root,
            lean_target.get("file"),
            f"controlled target {target.get('task_id')}",
        )
        _require_sha_match(
            target_path,
            lean_target.get("controlled_file_sha256"),
            f"controlled target {target.get('task_id')}",
        )

    task_ids = {task.get("task_id") for task in inputs.tasks}
    review_coverage = {task_id: 0 for task_id in task_ids}
    review_ids: set[Any] = set()
    unfinished_words = (
        "preliminary",
        "pending",
        "provisional",
        "blocked",
        "not release-ready",
        "fail",
    )
    for review in inputs.reviews:
        review_id = review.get("review_id")
        if not isinstance(review_id, str) or not review_id or review_id in review_ids:
            raise ReportError("review records need distinct nonempty review_id values")
        review_ids.add(review_id)
        overall_status = review.get("overall_status")
        if not isinstance(overall_status, str) or not overall_status or any(
            word in overall_status.lower() for word in unfinished_words
        ):
            raise ReportError(f"review {review_id} is not final: {overall_status!r}")
        task_reviews = review.get("task_reviews")
        covered = {
            item.get("task_id") for item in task_reviews if isinstance(item, Mapping)
        } if isinstance(task_reviews, list) else set()
        if not covered or not covered.issubset(task_ids) or len(covered) != len(task_reviews):
            raise ReportError(f"review {review_id} has invalid task coverage")
        for task_review in task_reviews:
            assert isinstance(task_review, Mapping)
            task_id = task_review.get("task_id")
            review_coverage[task_id] += 1
            outcome = task_review.get("review_outcome", task_review.get("outcome"))
            if not isinstance(outcome, str) or not outcome or any(
                word in outcome.lower() for word in unfinished_words
            ):
                raise ReportError(
                    f"review {review_id} has an unfinished outcome for {task_review.get('task_id')}: {outcome!r}"
                )
            checks = task_review.get("checks")
            if isinstance(checks, Mapping):
                for name, record in checks.items():
                    status = (
                        record.get("status")
                        if isinstance(record, Mapping)
                        else "pass" if isinstance(record, str) and record.lower().startswith("pass") else None
                    )
                    if status != "pass":
                        raise ReportError(
                            f"review {review_id} check {task_review.get('task_id')}/{name} is not a final pass"
                        )
    missing_reviews = sorted(
        str(task_id) for task_id, count in review_coverage.items() if count < 2
    )
    if missing_reviews:
        raise ReportError(
            "each task requires two final review passes; missing: " + ", ".join(missing_reviews)
        )


def _validate_freeze_link(inputs: ReportInputs, result_check: Mapping[str, Any]) -> None:
    """Authenticate the startup check used by every accepted run."""

    freeze = inputs.freeze_check
    digest = _document_digest(freeze)
    if not _hex_digest(result_check.get("freeze_check_sha256")) or result_check.get(
        "freeze_check_sha256"
    ) != digest:
        raise ReportError("analysis is not linked to the adjacent frozen-run verification")
    frozen = inputs.config.get("frozen_environment")
    lean_environment = inputs.environment.get("lean")
    if not isinstance(frozen, Mapping) or not isinstance(lean_environment, Mapping):
        raise ReportError("frozen environment metadata is missing")
    if (
        freeze.get("schema_version") != 1
        or freeze.get("kind") != "highambench-frozen-run-verification"
        or freeze.get("ok") is not True
        or freeze.get("benchmark_id") != inputs.config.get("benchmark_id")
        or freeze.get("environment_id") != frozen.get("environment_id")
        or freeze.get("environment_bundle_sha256")
        != frozen.get("environment_bundle_sha256")
    ):
        raise ReportError("the frozen-run verification has the wrong identity or status")

    expected_metadata = {
        "config": _document_digest(inputs.config),
        "environment": _document_digest(inputs.environment),
        "manifest": _document_digest(inputs.manifest),
        "run_order": _document_digest(inputs.run_order),
    }
    recorded_metadata = freeze.get("metadata_document_sha256")
    if not isinstance(recorded_metadata, Mapping) or any(
        recorded_metadata.get(name) != value for name, value in expected_metadata.items()
    ):
        raise ReportError("the frozen-run verification cites stale metadata")

    release = freeze.get("release_manifest")
    release_relative = _artifact_path_below_benchmark(
        inputs, frozen.get("release_manifest"), "evaluation release manifest"
    )
    release_count = len(inputs.release_manifest.get("files", []))
    release_verification = (
        release.get("verification") if isinstance(release, Mapping) else None
    )
    if (
        not isinstance(release, Mapping)
        or release.get("path") != release_relative
        or release.get("sha256") != frozen.get("release_manifest_sha256")
        or release.get("file_count") != release_count
        or not isinstance(release_verification, Mapping)
        or release_verification.get("ok") is not True
        or release_verification.get("expected") != release_count
        or release_verification.get("verified") != release_count
        or release_verification.get("missing") != []
        or release_verification.get("changed") != []
    ):
        raise ReportError("the frozen-run verification has incomplete release evidence")

    compiled = freeze.get("compiled_environment_summary")
    packages = inputs.compiled_environment_summary.get("packages")
    toolchain = inputs.compiled_environment_summary.get("toolchain")
    package_file_count = (
        sum(
            package.get("file_count", -1) if isinstance(package, Mapping) else -1
            for package in packages
        )
        if isinstance(packages, list)
        else -1
    )
    if (
        not isinstance(compiled, Mapping)
        or compiled.get("path") != frozen.get("compiled_environment_summary")
        or compiled.get("sha256") != frozen.get("compiled_environment_summary_sha256")
        or not isinstance(toolchain, Mapping)
        or compiled.get("toolchain_file_count") != toolchain.get("file_count")
        or not isinstance(packages, list)
        or compiled.get("package_count") != len(packages)
        or compiled.get("package_file_count") != package_file_count
    ):
        raise ReportError("the frozen-run verification has incomplete compiled-tree evidence")

    freeze_lean = freeze.get("lean")
    freeze_agent = freeze.get("agent")
    freeze_python = freeze.get("python")
    freeze_packages = freeze.get("packages_runtime")
    token_control = freeze.get("token_control")
    freeze_limits = freeze.get("limits")
    freeze_bubblewrap = freeze.get("bubblewrap")
    freeze_host = freeze.get("host_class")
    isolation = inputs.environment.get("isolation")
    environment_host = inputs.environment.get("host_class")
    limits = inputs.config.get("limits")
    if (
        not isinstance(freeze_lean, Mapping)
        or freeze_lean.get("version") != lean_environment.get("version")
        or freeze_lean.get("commit") != lean_environment.get("commit")
        or freeze_lean.get("binary_sha256") != lean_environment.get("binary_sha256")
        or freeze_lean.get("mathlib_commit") != lean_environment.get("mathlib_commit")
        or freeze_lean.get("numstability_commit")
        != lean_environment.get("numstability_commit")
        or not isinstance(freeze_agent, Mapping)
        or freeze_agent.get("id") != frozen.get("agent_id")
        or freeze_agent.get("version") != frozen.get("agent_version")
        or freeze_agent.get("binary_sha256") != frozen.get("agent_binary_sha256")
        or freeze_agent.get("model") != frozen.get("model_version")
        or freeze_agent.get("reasoning_effort")
        != frozen.get("model_reasoning_effort")
        or not isinstance(freeze_python, Mapping)
        or freeze_python.get("version") != frozen.get("python_version")
        or freeze_python.get("binary_sha256") != frozen.get("python_binary_sha256")
        or not isinstance(token_control, Mapping)
        or token_control.get("feature") != "rollout_budget"
        or not isinstance(token_control.get("feature_row"), str)
        or not str(token_control.get("feature_row", "")).startswith("rollout_budget ")
        or token_control.get("strict_config") is not True
        or not isinstance(limits, Mapping)
        or token_control.get("limit_tokens") != limits.get("total_model_tokens")
        or token_control.get("prefill_token_weight") != 1
        or token_control.get("sampling_token_weight") != 1
        or not isinstance(freeze_limits, Mapping)
        or freeze_limits.get("wall_clock_seconds") != limits.get("wall_clock_seconds")
        or freeze_limits.get("total_model_tokens") != limits.get("total_model_tokens")
        or not isinstance(freeze_bubblewrap, Mapping)
        or not isinstance(isolation, Mapping)
        or freeze_bubblewrap.get("version") != isolation.get("bubblewrap_version")
        or freeze_bubblewrap.get("binary_sha256")
        != isolation.get("bubblewrap_binary_sha256")
    ):
        raise ReportError("the frozen-run verification disagrees with the compiled setup")

    runtime = inputs.environment.get("runtime")
    runtime_python = runtime.get("python") if isinstance(runtime, Mapping) else None
    runtime_files = inputs.packages_runtime_manifest.get("files")
    packages_verification = (
        freeze_packages.get("verification")
        if isinstance(freeze_packages, Mapping)
        else None
    )
    packages_count = len(runtime_files) if isinstance(runtime_files, list) else -1
    source_count = sum(
        str(entry.get("path", "")).endswith(".lean")
        for entry in runtime_files
        if isinstance(entry, Mapping)
    ) if isinstance(runtime_files, list) else -1
    olean_count = sum(
        str(entry.get("path", "")).endswith(".olean")
        for entry in runtime_files
        if isinstance(entry, Mapping)
    ) if isinstance(runtime_files, list) else -1
    compiled_support_count = sum(
        str(entry.get("path", "")).endswith(PACKAGE_COMPILED_SUPPORT_SUFFIXES)
        for entry in runtime_files
        if isinstance(entry, Mapping)
    ) if isinstance(runtime_files, list) else -1
    if (
        not isinstance(runtime, Mapping)
        or not isinstance(runtime_python, Mapping)
        or freeze_python != runtime_python
        or not isinstance(freeze_packages, Mapping)
        or freeze_packages.get("path") != frozen.get("packages_runtime_manifest")
        or freeze_packages.get("sha256")
        != frozen.get("packages_runtime_manifest_sha256")
        or freeze_packages.get("file_count") != packages_count
        or freeze_packages.get("source_file_count") != source_count
        or freeze_packages.get("olean_file_count") != olean_count
        or freeze_packages.get("compiled_support_file_count")
        != compiled_support_count
        or source_count + olean_count + compiled_support_count != packages_count
        or not isinstance(packages_verification, Mapping)
        or packages_verification.get("ok") is not True
        or packages_verification.get("expected") != packages_count
        or packages_verification.get("verified") != packages_count
        or packages_verification.get("missing") != []
        or packages_verification.get("changed") != []
    ):
        raise ReportError("the frozen-run verification has incomplete pruned-package evidence")
    host_fields = {
        "kernel",
        "virtualization",
        "processor",
        "online_logical_cpus",
        "visible_memory_bytes",
    }
    if (
        not isinstance(freeze_host, Mapping)
        or not isinstance(environment_host, Mapping)
        or set(freeze_host) != host_fields
        or any(environment_host.get(field) != freeze_host.get(field) for field in host_fields)
    ):
        raise ReportError("the frozen-run verification disagrees with the measured host")

    selected = result_check.get("selected_final_record_count")
    network_runs = result_check.get("network_violation_run_count")
    integrity_failures = result_check.get("network_integrity_failure_count")
    if (
        not isinstance(selected, int)
        or isinstance(selected, bool)
        or not isinstance(network_runs, int)
        or isinstance(network_runs, bool)
        or network_runs < 0
        or network_runs > selected
        or integrity_failures != 0
    ):
        raise ReportError("result set has incomplete or failed network-marker evidence")


def validate_report_inputs(inputs: ReportInputs) -> None:
    """Reject stale metadata, weak construction evidence, or partial measurements."""

    _validate_hashes_and_reviews(inputs)
    _validate_release_and_environment(inputs)
    analysis = inputs.analysis
    if analysis.get("kind") != "highambench-analysis":
        raise ReportError("incomplete analysis: input is not a highambench-analysis document")
    if analysis.get("malformed_input_lines") != []:
        raise ReportError("incomplete analysis: malformed input lines were not ruled out")
    check = analysis.get("result_set_check")
    if not isinstance(check, Mapping) or check.get("ok") is not True:
        raise ReportError("incomplete analysis: the result-set completeness check did not pass")
    _validate_freeze_link(inputs, check)
    _validate_construction(inputs)
    if check.get("system_error_handling_complete") is not True:
        raise ReportError("incomplete analysis: system-error rerun handling is unresolved")
    if analysis.get("pair_problems") != []:
        raise ReportError("incomplete analysis: paired-run problems remain")

    recorded_digests = check.get("metadata_document_sha256")
    if not isinstance(recorded_digests, Mapping):
        raise ReportError("incomplete analysis: frozen metadata digests are missing")
    current_digests = {
        "config": _document_digest(inputs.config),
        "manifest": _document_digest(inputs.manifest),
        "run_order": _document_digest(inputs.run_order),
    }
    if any(recorded_digests.get(name) != digest for name, digest in current_digests.items()):
        raise ReportError("stale analysis: config, manifest, or run order changed after analysis")

    expected_agents = check.get("expected_agents")
    expected_per_agent = check.get("expected_final_runs_per_agent")
    selected_count = check.get("selected_final_record_count")
    if (
        not isinstance(expected_agents, int)
        or isinstance(expected_agents, bool)
        or expected_agents <= 0
        or not isinstance(expected_per_agent, int)
        or isinstance(expected_per_agent, bool)
        or expected_per_agent <= 0
        or selected_count != expected_agents * expected_per_agent
    ):
        raise ReportError("incomplete analysis: final record count does not equal the planned matrix")

    per_run = _require_list(analysis.get("per_run_results"), "per-run results")
    if not all(isinstance(run, Mapping) for run in per_run):
        raise ReportError("incomplete analysis: per-run results are malformed")
    if analysis.get("input_run_count") != len(per_run):
        raise ReportError("incomplete analysis: raw run count disagrees with the per-run table")
    selected_ids = check.get("selected_final_run_ids")
    if (
        not isinstance(selected_ids, list)
        or len(selected_ids) != selected_count
        or len(set(selected_ids)) != len(selected_ids)
    ):
        raise ReportError("incomplete analysis: selected final run IDs are missing or repeated")
    runs_by_id = {run.get("run_id"): run for run in per_run if isinstance(run.get("run_id"), str)}
    if any(run_id not in runs_by_id for run_id in selected_ids):
        raise ReportError("incomplete analysis: a selected final run is absent from per-run results")
    selected_runs = [runs_by_id[run_id] for run_id in selected_ids]

    condition_rows, task_rows, pair_rows, task_pair_rows, observational = _analysis_tables(analysis)
    reference = check.get("reference_compliant") is True
    if reference != (analysis.get("official_scores_valid") is True):
        raise ReportError("incomplete analysis: official-score status is inconsistent")
    if observational:
        if check.get("analysis_profile") != "observational_pilot":
            raise ReportError("incomplete analysis: non-reference data lacks the observational profile")
        pilot = analysis["observational_pilot_results"]
        if pilot.get("official_scores_valid") is not False or pilot.get("run_count") != selected_count:
            raise ReportError("incomplete analysis: observational run count or score label is inconsistent")
        reasons = pilot.get("nonreference_reasons")
        if not isinstance(reasons, list) or not reasons:
            raise ReportError("incomplete analysis: observational data has no recorded protocol reasons")
        for rows in (condition_rows, task_rows, pair_rows, task_pair_rows):
            if any(row.get("result_status") != "observational_not_reference_score" for row in rows):
                raise ReportError("incomplete analysis: an observational row lacks its non-score label")
        if any(
            analysis.get(name) != []
            for name in (
                "condition_summaries",
                "per_task_summaries",
                "paired_comparisons",
                "per_task_paired_comparisons",
            )
        ):
            raise ReportError("incomplete analysis: invalid official-score tables must remain empty")
    elif check.get("analysis_profile") != "reference":
        raise ReportError("incomplete analysis: official data lacks the reference profile")

    _check_matrix_coverage(
        inputs, selected_runs, condition_rows, task_rows, pair_rows, task_pair_rows
    )
    paper_count = len(inputs.papers)
    informative_bootstrap = paper_count > 1
    for row in (*pair_rows, *task_pair_rows):
        bootstrap = row.get("bootstrap")
        if (
            not isinstance(bootstrap, Mapping)
            or bootstrap.get("paper_count") != paper_count
            or bootstrap.get("informative") is not informative_bootstrap
            or (paper_count == 1 and not bootstrap.get("note"))
        ):
            raise ReportError(
                "incomplete analysis: paired bootstrap metadata disagrees with the paper corpus"
            )

    deviations = inputs.environment.get("known_reference_protocol_deviations")
    if not isinstance(deviations, list) or not all(isinstance(item, str) for item in deviations):
        raise ReportError("environment metadata has no reference-protocol deviation list")
    joined = " ".join(deviations).lower()
    for topic in ("seed", "oci", "provider connection", "token"):
        if topic not in joined:
            raise ReportError(f"environment metadata does not explain the {topic} deviation")


def latex_escape(value: Any) -> str:
    if value is None:
        return "--"
    text = str(value).translate(
        str.maketrans(
            {
                "–": "--",
                "—": "---",
                "’": "'",
                "“": '"',
                "”": '"',
                "×": " x ",
                "≤": " less than or equal to ",
                "≥": " greater than or equal to ",
                "γ": "gamma",
                "Ŝ": "S-hat",
            }
        )
    )
    replacements = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
    }
    return "".join(replacements.get(character, character) for character in text)


def _hash_tex(value: Any) -> str:
    if not isinstance(value, str):
        return "--"
    chunks = [latex_escape(value[index : index + 8]) for index in range(0, len(value), 8)]
    return r"\texttt{" + r"\allowbreak{}".join(chunks) + "}"


def _inline_code(value: Any) -> str:
    text = latex_escape(value)
    text = text.replace(".", r".\allowbreak{}")
    return r"\texttt{" + text + "}"


def _ascii_lean(source: str) -> str:
    replacements = {
        "ℕ": "Nat",
        "ℝ": "Real",
        "∀": "forall",
        "∃": "exists",
        "→": "->",
        "≤": "<=",
        "≥": ">=",
        "∧": "/\\",
        "∨": "\\/",
        "∑": "sum",
        "δ": "delta",
        "α": "alpha",
        "β": "beta",
        "γ": "gamma",
        "ₙ": "_n",
        "Ŝ": "S_hat",
        "…": "...",
    }
    for old, new in replacements.items():
        source = source.replace(old, new)
    source = "".join(character if ord(character) < 128 else "?" for character in source)
    # Do not let source text terminate the LaTeX listing that contains it.
    return source.replace(r"\end{lstlisting}", r"\end {lstlisting}")


def _fmt_number(value: Any, digits: int = 3) -> str:
    if value is None:
        return "--"
    if isinstance(value, bool):
        return "yes" if value else "no"
    if isinstance(value, float):
        return f"{value:.{digits}f}"
    return str(value)


def _fmt_rate(value: Any) -> str:
    if not isinstance(value, (int, float)) or isinstance(value, bool):
        return "--"
    return f"{100 * float(value):.1f}\\%"


def _fmt_delta(value: Any, *, scale: float = 1.0, digits: int = 1) -> str:
    if not isinstance(value, (int, float)) or isinstance(value, bool):
        return "--"
    return f"{scale * float(value):+.{digits}f}"


def _range(row: Mapping[str, Any], metric: str, *, scale: float = 1.0, digits: int = 1) -> str:
    bootstrap = row.get("bootstrap")
    ranges = bootstrap.get("ranges") if isinstance(bootstrap, Mapping) else None
    interval = ranges.get(metric) if isinstance(ranges, Mapping) else None
    if not isinstance(interval, Mapping):
        return "--"
    low, high = interval.get("low"), interval.get("high")
    if not all(isinstance(value, (int, float)) and not isinstance(value, bool) for value in (low, high)):
        return "--"
    return f"[{scale * float(low):.{digits}f}, {scale * float(high):.{digits}f}]"


def _longtable(
    caption: str,
    specification: str,
    headers: Sequence[str],
    rows: Iterable[Sequence[str]],
    *,
    size: str = "small",
) -> list[str]:
    header = " & ".join(headers) + r" \\"
    lines = [
        rf"\begin{{{size}}}",
        rf"\begin{{longtable}}{{{specification}}}",
        rf"\caption{{{caption}}}\\",
        r"\toprule",
        header,
        r"\midrule",
        r"\endfirsthead",
        r"\toprule",
        header,
        r"\midrule",
        r"\endhead",
    ]
    for row in rows:
        lines.append(" & ".join(row) + r" \\")
    lines.extend([r"\bottomrule", r"\end{longtable}", rf"\end{{{size}}}"])
    return lines


def _manifest_targets(inputs: ReportInputs) -> list[Mapping[str, Any]]:
    return [target for _paper_id, target in _task_records(inputs.manifest)[1]]


def _condition_values(row: Mapping[str, Any], observational: bool) -> tuple[Any, ...]:
    if observational:
        return (
            row.get("observational_runs"),
            row.get("observed_passes"),
            row.get("observed_pass_rate"),
            row.get("median_observed_seconds"),
            row.get("median_observed_model_tokens"),
            row.get("observed_passed_library_use"),
        )
    return (
        row.get("scored_runs"),
        row.get("passes"),
        row.get("pass_rate"),
        row.get("median_scored_seconds"),
        row.get("median_model_tokens"),
        row.get("passed_library_use"),
    )


def _pair_values(row: Mapping[str, Any], observational: bool) -> tuple[Any, Any, Any]:
    if observational:
        return (
            row.get("observed_pass_rate_change"),
            row.get("median_observed_paired_time_change"),
            row.get("median_observed_paired_token_change"),
        )
    return (
        row.get("pass_rate_change"),
        row.get("median_paired_time_change"),
        row.get("median_paired_token_change"),
    )


def render_report(inputs: ReportInputs) -> str:
    """Render a validated input bundle as one standalone LaTeX document."""

    # Validate again so callers cannot construct a ReportInputs object by hand
    # and bypass the final-matrix refusal.
    validate_report_inputs(inputs)
    analysis = inputs.analysis
    check = analysis["result_set_check"]
    conditions, tasks, pairs, task_pairs, observational = _analysis_tables(analysis)
    selected_ids = set(check["selected_final_run_ids"])
    selected_runs = [
        run for run in analysis["per_run_results"] if run.get("run_id") in selected_ids
    ]
    manifest_papers = list(inputs.manifest["papers"])
    paper_records = {str(paper["paper_id"]): paper for paper in inputs.papers}
    paper_count = len(manifest_papers)
    task_count = len(inputs.tasks)
    repetitions = inputs.config.get("repetitions", [])
    pair_count = task_count * len(repetitions)
    run_count = pair_count * 2
    specification = inputs.manifest["specification"]
    frozen = inputs.config["frozen_environment"]
    environment = inputs.environment
    isolation = environment.get("isolation", {})
    limits = inputs.config.get("limits", {})

    lines: list[str] = [
        r"\documentclass[10pt]{article}",
        r"\usepackage[margin=0.68in]{geometry}",
        r"\usepackage[T1]{fontenc}",
        r"\usepackage[utf8]{inputenc}",
        r"\usepackage{amsmath,amssymb}",
        r"\usepackage{array,booktabs,longtable,tabularx}",
        r"\usepackage[table]{xcolor}",
        r"\usepackage{listings}",
        r"\usepackage[hidelinks]{hyperref}",
        r"\setlength{\LTpre}{4pt}",
        r"\setlength{\LTpost}{8pt}",
        r"\setlength{\parindent}{0pt}",
        r"\setlength{\parskip}{5pt}",
        r"\newcolumntype{P}[1]{>{\raggedright\arraybackslash}p{#1}}",
        r"\lstset{basicstyle=\ttfamily\footnotesize,breaklines=true,columns=fullflexible,keepspaces=true,showstringspaces=false}",
        r"\sloppy",
        r"\title{HighamBench: Construction and Measurement Report}",
        r"\author{Benchmark construction and annotation performed by Codex at the project owner's request}",
        r"\date{}",
        r"\begin{document}",
        r"\maketitle",
    ]

    if observational:
        lines.extend(
            [
                r"\begin{center}",
                r"\fcolorbox{red!70!black}{red!5}{\parbox{0.92\linewidth}{\centering\textbf{OBSERVATIONAL ONLY---NOT AN OFFICIAL HIGHAMBENCH SCORE.} The complete run matrix was measured, but the setup does not meet every reference rule listed later in this report. The numbers may describe this pilot only.}}",
                r"\end{center}",
            ]
        )
    else:
        lines.append(
            r"\begin{center}\fbox{\parbox{0.92\linewidth}{\centering\textbf{Official reference result.} The complete result-set check passed every recorded reference control.}}\end{center}"
        )

    lines.extend(
        [
            r"\section{What was built}",
            "A benchmark is a fixed test used to compare two setups. This benchmark asks whether access to the NumStability library, meaning a reusable collection of Lean definitions and proofs, helps one proof-making agent finish the same Lean tasks. An agent is a program that asks a language model to do the work and can use allowed local tools. A language model is the text-producing service behind the agent. Lean is a language whose checker verifies each proof step.",
            "This measurement snapshot contains "
            + latex_escape(paper_count)
            + " paper(s) and "
            + latex_escape(task_count)
            + " task(s): "
            + "; ".join(
                latex_escape(paper.get("paper_id"))
                + ", ``"
                + latex_escape(
                    paper.get("citation", {}).get(
                        "title", paper_records[str(paper["paper_id"])].get("title")
                    )
                )
                + ".''"
                for paper in manifest_papers
            )
            + " Each paper version is fixed for this measurement snapshot. A theorem is a mathematical claim together with a proof. A task is one fixed theorem statement plus the short paper context needed to understand it. N is the setup with no NumStability files. L is the otherwise matching setup with NumStability available.",
            "Observational means the results describe this exact pilot but do not satisfy every rule needed for an official score.",
            "Codex performed the requested source labeling and both recorded review passes. In this sentence, labeling means choosing the paper result, recording its exact location, and assigning its difficulty type before measurement. The private construction proofs were used only to check that each task was possible. They were never shown during a measured run.",
            r"\subsection{Source identity and fixed fingerprints}",
            "SHA-256 is a 64-character content fingerprint. If checked content changes, its fingerprint should change. Most rows below fingerprint exact file bytes. The environment bundle and frozen-run check first put their JSON data, meaning structured text records, into one fixed key order so harmless spacing does not change the identity. Together these fingerprints tie this report to the exact source and setup.",
        ]
    )
    hash_rows: list[Sequence[str]] = [
        (
            "Paper PDF " + latex_escape(paper.get("paper_id")),
            _hash_tex(paper.get("source", {}).get("sha256")),
            latex_escape(paper.get("source", {}).get("local_path")),
        )
        for paper in manifest_papers
    ] + [
        (
            "Benchmark specification PDF",
            _hash_tex(specification.get("sha256")),
            latex_escape(specification.get("local_path")),
        ),
        (
            "Environment bundle",
            _hash_tex(environment.get("environment_bundle_sha256")),
            latex_escape(environment.get("environment_id")),
        ),
        (
            "Agent prompt",
            _hash_tex(frozen.get("prompt_sha256")),
            "The fixed instructions sent in every run",
        ),
        (
            "Evaluation release",
            _hash_tex(frozen.get("release_manifest_sha256")),
            latex_escape(frozen.get("release_manifest")),
        ),
        (
            "Frozen-run check",
            _hash_tex(_document_digest(inputs.freeze_check)),
            latex_escape("freeze_check.json beside the measured result set"),
        ),
        (
            "Compiled Lean setup",
            _hash_tex(frozen.get("compiled_environment_summary_sha256")),
            latex_escape(frozen.get("compiled_environment_summary")),
        ),
        (
            "Python executable",
            _hash_tex(frozen.get("python_binary_sha256")),
            "Python " + latex_escape(frozen.get("python_version")),
        ),
        (
            "Pruned package view list",
            _hash_tex(frozen.get("packages_runtime_manifest_sha256")),
            latex_escape(frozen.get("packages_runtime_manifest")),
        ),
        (
            "NumStability source list",
            _hash_tex(frozen.get("numstability_source_manifest_sha256")),
            latex_escape(frozen.get("numstability_source_manifest")),
        ),
        (
            "Pruned NumStability compiled list",
            _hash_tex(frozen.get("numstability_compiled_manifest_sha256")),
            latex_escape(frozen.get("numstability_compiled_manifest")),
        ),
    ]
    for shared in inputs.manifest.get("controlled_shared_files", []):
        hash_rows.append(
            ("Shared Lean setting", _hash_tex(shared.get("sha256")), latex_escape(shared.get("path")))
        )
    for target in sorted(_manifest_targets(inputs), key=lambda item: str(item.get("tier"))):
        lean_target = target.get("lean_target", {})
        hash_rows.append(
            (
                str(target.get("task_id")) + " target",
                _hash_tex(lean_target.get("controlled_file_sha256")),
                latex_escape(lean_target.get("file")),
            )
        )
    lines.extend(
        _longtable(
            "Fixed source and setup fingerprints",
            "P{0.19\\linewidth}P{0.42\\linewidth}P{0.32\\linewidth}",
            ("Item", "SHA-256 fingerprint", "Meaning or file"),
            hash_rows,
            size="footnotesize",
        )
    )
    for paper in manifest_papers:
        source = paper.get("source", {})
        rights_note = source.get("rights_note") if isinstance(source, Mapping) else None
        if rights_note:
            lines.append(
                "Source-copy note for "
                + latex_escape(paper.get("paper_id"))
                + ": "
                + latex_escape(rights_note)
            )

    lines.extend(
        [
            r"\section{Why T1, T2, and T3 are present}",
            "A tier is a difficulty label fixed before measurement. T1 means direct use: a close library result already exists. T2 means combine: several existing facts and small new steps must be joined. T3 means extend: the library does not contain the complete result, so a substantial new proof step is required.",
        ]
    )
    manifest_by_task = {item.get("task_id"): item for item in _manifest_targets(inputs)}
    for task in inputs.tasks:
        task_id = str(task.get("task_id"))
        target = manifest_by_task[task_id]
        tier = str(task.get("tier"))
        lines.extend(
            [
                rf"\subsection{{{latex_escape(task_id)}: {latex_escape(target.get('title'))}}}",
                "Decision: this paper has a "
                + latex_escape(tier)
                + " result. "
                + latex_escape(task.get("tier_rationale", target.get("tier_reason"))),
                "Chosen claim: " + latex_escape(task.get("informal_statement", target.get("informal_statement_paraphrase"))),
                "Paper anchors, meaning the exact places used to check the claim:",
                r"\begin{itemize}",
            ]
        )
        locations = task.get("source_locations")
        if not isinstance(locations, list) or not locations:
            locations = target.get("source_locations", [])
        for location in locations:
            if not isinstance(location, Mapping):
                continue
            anchor = location.get("equation") or location.get("anchor") or "nearby text"
            lines.append(
                r"\item "
                + latex_escape(location.get("section"))
                + ", "
                + latex_escape(anchor)
                + "; journal/printed page "
                + latex_escape(location.get("printed_page", location.get("journal_page")))
                + ", PDF page "
                + latex_escape(location.get("pdf_page"))
                + ". Role: "
                + latex_escape(location.get("role"))
                + "."
            )
        lines.extend([r"\end{itemize}", "Fixed Lean theorem statement:"])
        formal = task.get("formal_statement")
        if not isinstance(formal, Mapping) or not isinstance(formal.get("lean_header"), str):
            raise ReportError(f"task {task_id} has no fixed Lean theorem header")
        lines.extend(
            [
                r"\begin{lstlisting}",
                _ascii_lean(formal["lean_header"]),
                r"\end{lstlisting}",
                "Plain meaning: " + latex_escape(formal.get("plain_language")) + " "
                + latex_escape(task.get("interpretation_warning", "")),
            ]
        )

    lines.extend(
        [
            r"\subsection{Search for already existing complete results}",
            "An exact duplicate has the same fixed Lean claim. A semantic duplicate may use different names but still says the same mathematical thing with the same assumptions. Every Lean source file in the frozen NumStability and mathlib trees was searched, and each plausible nearby result was then compared by meaning. Text search alone was not treated as proof that a duplicate was absent.",
        ]
    )
    search_rows: list[Sequence[str]] = []
    for evidence_name, target_search in sorted(inputs.evidence.items()):
        if not evidence_name.startswith("exact_target_search"):
            continue
        for finding in target_search.get("task_findings", []):
            search_rows.append(
                (
                    latex_escape(finding.get("task_id")),
                    "no" if finding.get("exact_duplicate_found") is False else "yes",
                    "no" if finding.get("semantic_duplicate_found") is False else "yes",
                    latex_escape(finding.get("tier_assessment")),
                )
            )
    lines.extend(
        _longtable(
            "Duplicate search and final tier check",
            "P{0.11\\linewidth}P{0.12\\linewidth}P{0.14\\linewidth}P{0.55\\linewidth}",
            ("Task", "Exact duplicate", "Same-meaning duplicate", "Tier conclusion"),
            search_rows,
            size="footnotesize",
        )
    )

    lines.extend(
        [
            r"\section{The exact shared Lean setting}",
            "Both conditions receive the same small, library-neutral setting. Library-neutral means that its names and statements do not mention NumStability. This prevents the theorem wording itself from favoring condition L.",
            "The shared file contains exactly the neutral models, algorithms, and notation needed by the tasks in the current manifest. When another paper needs an additional neutral definition, this file and every affected fingerprint are regenerated for the whole corpus.",
            "The next listing records the complete controlled shared file. ASCII is the small basic computer character set. For dependable PDF building only, symbols outside ASCII are written as words such as Real, Nat, and alpha. The file fingerprint above is the exact byte record; a byte is one stored unit of file data.",
            r"\begin{lstlisting}",
            _ascii_lean(inputs.shared_source),
            r"\end{lstlisting}",
        ]
    )

    lines.extend(
        [
            r"\section{The two conditions and their isolation}",
            "Condition N means no NumStability file, compiled file, documentation, name list, search entry, or cache is visible. Condition L means the frozen NumStability source and compiled files are visible as read-only files. Read-only means a run can inspect them but cannot change them.",
            "Isolation means separating one run from files and messages that it is not allowed to see. The same target, context, shared file, agent prompt, Lean version, mathlib version, time limit, token limit, and machine class are used on both sides. Mathlib is Lean's main collection of already proved mathematics.",
            "Both sides receive the same pruned package view. Pruned means it contains only the mathlib source needed for local reading and the package compiled files needed by Lean. A base .olean file holds a compiled Lean module. Its .olean.server, .olean.private, and .ir support files hold extra compiler data that Lean 4.29 needs when it loads some modules. The full package build folders and caches are not exposed to an attempt.",
            r"\begin{center}",
            r"\fbox{\parbox{0.78\linewidth}{\centering Fixed paper context + fixed Lean target + fixed shared setting}}",
            r"\\[3pt]$\Downarrow$\\[3pt]",
            r"\fbox{\parbox{0.78\linewidth}{\centering New conversation + new restricted file and process view}}",
            r"\\[3pt]$\Downarrow$\\[-2pt]",
            r"\begin{tabular}{P{0.43\linewidth}cP{0.43\linewidth}}",
            r"\fbox{\parbox{0.39\linewidth}{\centering \textbf{N}\newline Lean + mathlib only\newline NumStability import must fail}} & $\Longleftrightarrow$ & \fbox{\parbox{0.39\linewidth}{\centering \textbf{L}\newline Same files + frozen NumStability\newline Library use is checked}} \\",
            r"\end{tabular}",
            r"\\[3pt]$\Downarrow$\\[3pt]",
            r"\fbox{\parbox{0.78\linewidth}{\centering Shared validator checks the unchanged statement, proof rules, compilation, and dependencies}}",
            r"\end{center}",
            r"\subsection{Filesystem and network boundary}",
            "Bubblewrap is a Linux tool that gives a process a restricted view of files and processes. A fresh bubblewrap view is made for each attempt. Seccomp is a rule enforced by the Linux kernel, the central part of the operating system, that blocks selected requests from a program. Here it blocks socket calls, which are requests to open network connections, from model-generated shell commands.",
            "The Codex control process is separate from the model-generated shell. It keeps the provider connection needed to send the prompt to the model service and receive the answer. This limit is important: the model's shell and web tools are offline, but the outer control process is not fully offline.",
            "For each run, the outer runner creates a fresh secret marker file and asks the Linux kernel to watch it. A blocked network request writes an event before returning an error. The kernel watch remains owned by the outer runner, so a model shell cannot erase an event by clearing or deleting the file. The result-set checker required a complete marker record for every final run.",
            "The private gold proofs and source PDFs are not mounted in either measured condition. A mount is a file tree made visible inside the restricted run.",
        ]
    )
    freeze_release = inputs.freeze_check["release_manifest"]
    freeze_compiled = inputs.freeze_check["compiled_environment_summary"]
    freeze_packages = inputs.freeze_check["packages_runtime"]
    freeze_lean = inputs.freeze_check["lean"]
    frozen_setup_rows = [
        (
            "Release files",
            freeze_release.get("file_count"),
            "Every listed benchmark and checker file passed its recorded fingerprint.",
        ),
        (
            "Construction checker files",
            len(CONSTRUCTION_TOOL_PATHS),
            "Their fingerprints matched both the construction record and the release list.",
        ),
        (
            "Lean toolchain files",
            freeze_compiled.get("toolchain_file_count"),
            "The whole Lean toolchain, meaning the compiler and its standard files, matched the frozen tree summary.",
        ),
        (
            "Package files",
            freeze_compiled.get("package_file_count"),
            str(freeze_compiled.get("package_count"))
            + " compiled package trees, including mathlib, matched their frozen summaries.",
        ),
        (
            "Files exposed in the pruned package view",
            freeze_packages.get("file_count"),
            str(freeze_packages.get("source_file_count"))
            + " mathlib source files and "
            + str(freeze_packages.get("olean_file_count"))
            + " base compiled package files and "
            + str(freeze_packages.get("compiled_support_file_count"))
            + " matching compiled support files were exposed; the rest of the package checkout was absent.",
        ),
        (
            "Online logical processors",
            inputs.freeze_check.get("host_class", {}).get("online_logical_cpus"),
            "The measured machine matched every recorded host field before the matrix started.",
        ),
        (
            "Model-token ceiling per run",
            limits.get("total_model_tokens"),
            "The frozen Codex feature list contained rollout_budget, and the strict setup counted both input and generated tokens with weight 1.",
        ),
        (
            "NumStability source files",
            freeze_lean.get("source_files_verified"),
            "The exact source manifest passed before the run matrix started.",
        ),
        (
            "Pruned NumStability compiled files",
            freeze_lean.get("compiled_files_verified"),
            "Only paths below the NumStability namespace were in the L-side compiled mount.",
        ),
        (
            "Runs with a blocked network attempt",
            check.get("network_violation_run_count"),
            "Each such run is kept as a failure and cannot pass. A higher-priority limit failure may supply its short failure code. Zero means no attempt was seen.",
        ),
        (
            "Runs with damaged marker evidence",
            check.get("network_integrity_failure_count"),
            "This must be zero before the result set is accepted.",
        ),
    ]
    lines.extend(
        _longtable(
            "Authenticated release, compiled setup, and network evidence",
            "P{0.32\\linewidth}rP{0.52\\linewidth}",
            ("Item", "Count", "What the count proves"),
            (
                (latex_escape(item), latex_escape(count), latex_escape(meaning))
                for item, count, meaning in frozen_setup_rows
            ),
            size="footnotesize",
        )
    )
    lines.extend(
        [
            r"\subsection{Construction evidence}",
            "Compile means ask Lean to read and check a whole source file. Import means ask Lean to load another named source unit. A dependency check follows the named facts used by a proof to make sure no hidden shortcut was used.",
            "Each N construction check first copied the complete controlled task, then scanned that staged task and tried a real NumStability import. Only after this absence check passed was the private answer copied in. This order makes the scan cover the files an evaluated run actually receives.",
        ]
    )
    construction_results = list(inputs.construction_check["results"])
    n_results = [result for result in construction_results if result.get("condition") == "N"]
    n_staged_file_count = sum(
        result["n_preflight"]["controlled_files_verified_after_staging"]["verified"]
        for result in n_results
    )
    l_results = [result for result in construction_results if result.get("condition") == "L"]
    l_compile_count = sum(
        1
        for result in l_results
        if isinstance(result.get("validation"), Mapping)
        and result["validation"].get("compile_exit_code") == 0
        and result["validation"].get("compile_timed_out") is False
    )
    l_audit_count = sum(
        1
        for result in l_results
        if isinstance(result.get("validation"), Mapping)
        and isinstance(result["validation"].get("dependency_audit"), Mapping)
        and result["validation"]["dependency_audit"].get("complete") is True
        and result["validation"]["dependency_audit"].get("exit_code") == 0
    )
    l_use_count = sum(
        1
        for result in l_results
        if isinstance(result.get("validation"), Mapping)
        and isinstance(result["validation"].get("dependency_audit"), Mapping)
        and result["validation"]["dependency_audit"].get("library_use") is True
    )
    l_declaration_count = sum(
        len(result["validation"]["dependency_audit"].get("library_declarations", []))
        for result in l_results
    )
    evidence_rows = [
        (
            "N staged-task scans",
            "pass",
            f"{len(n_results)} of 3 complete staged tasks had no forbidden library file; {n_staged_file_count} controlled file copies were verified",
        ),
        (
            "N real import tests",
            "pass",
            f"{len(n_results)} of 3 checks had Lean report that NumStability was absent",
        ),
        (
            "L hidden proof compiles",
            "pass" if l_compile_count == 3 else "fail",
            f"{l_compile_count} of 3 private library-side proofs compiled",
        ),
        (
            "L dependency checks",
            "pass" if l_audit_count == 3 else "fail",
            f"{l_audit_count} of 3 proof dependency records were complete",
        ),
        (
            "L NumStability use",
            "pass" if l_use_count == 3 else "fail",
            f"{l_use_count} of 3 proofs used NumStability; {l_declaration_count} declaration records were found",
        ),
    ]
    lines.extend(
        _longtable(
            "Construction evidence used by this report",
            "P{0.24\\linewidth}P{0.10\\linewidth}P{0.58\\linewidth}",
            ("Check", "Result", "Plain meaning"),
            ((latex_escape(a), latex_escape(b), latex_escape(c)) for a, b, c in evidence_rows),
        )
    )
    condition_order = {"N": 0, "L": 1}
    construction_rows: list[Sequence[str]] = []
    for result in sorted(
        construction_results,
        key=lambda item: (
            str(item.get("tier")),
            condition_order.get(str(item.get("condition")), 9),
        ),
    ):
        validation = result["validation"]
        audit = validation["dependency_audit"]
        compile_ok = (
            validation.get("compile_exit_code") == 0
            and validation.get("compile_timed_out") is False
        )
        construction_rows.append(
            (
                latex_escape(result.get("task_id")),
                latex_escape(result.get("condition")),
                latex_escape(_fmt_number(compile_ok)),
                latex_escape(_fmt_number(result.get("pass"))),
                latex_escape(_fmt_number(validation.get("statement_unchanged"))),
                latex_escape(_fmt_number(audit.get("complete"))),
                latex_escape(_fmt_number(audit.get("library_use"))),
            )
        )
    lines.append(
        "A private construction proof is a complete answer used only to prove that a task can be solved. The following six answers were rebuilt in fresh N and L workspaces and passed the same hidden checker used for submissions. The report followed the small evidence file that names the complete record, then checked the recorded file fingerprint before using these rows."
    )
    lines.extend(
        _longtable(
            "All six private construction proofs",
            "P{0.16\\linewidth}P{0.08\\linewidth}P{0.10\\linewidth}P{0.08\\linewidth}P{0.16\\linewidth}P{0.13\\linewidth}P{0.13\\linewidth}",
            (
                "Task",
                "Cond.",
                "Compile",
                "Pass",
                "Statement fixed",
                "Audit done",
                "Library use",
            ),
            construction_rows,
            size="footnotesize",
        )
    )

    lines.extend(
        [
            r"\section{How submissions were checked}",
            "A validator is a program that decides whether a submitted proof obeys the fixed rules and compiles. It performs these checks in order:",
            r"\begin{enumerate}",
            r"\item Recheck every controlled file fingerprint before and after validation.",
            r"\item Reject a changed theorem statement, a symbolic link that redirects to another file, and a compiled helper with no matching source file.",
            r"\item Scan every submitted Lean source file for \texttt{sorry}, \texttt{admit}, a new global \texttt{axiom}, \texttt{unsafe}, forbidden imports, or other rule violations. These forms can bypass the requested complete proof.",
            r"\item Compile a hidden copy of the submitted theorem. Hidden means the final checker file is not available for the agent to edit.",
            r"\item Recursively follow the named facts and definitions used by the theorem. Recursively means following each dependency and then its dependencies. Reject any reachable \texttt{sorryAx}, which is Lean's marker for a missing proof, and reject any axiom owned by \texttt{Submission} or another task-local helper module, meaning a Lean source unit supplied with the answer.",
            r"\item This audit does not ban every axiom from Lean, mathlib, or NumStability. Those outside the submitted task modules belong to the fixed libraries and compiler. The audit records them while separately rejecting missing proofs and task-local assumed facts.",
            r"\item In condition L, use the same recursive dependency record to confirm real NumStability use. Merely importing the library is not counted as use.",
            r"\end{enumerate}",
            "A system error means the measurement machinery failed rather than the proof. One such incident may be kept and rerun once. Every other failure receives the full fixed comparison time even though its real stop time is also recorded.",
            r"\subsection{Independent review records}",
            "Independent here means that the two Codex passes used different checklists: one centered on the paper's meaning, and one centered on the formal interface and run rules. A formal interface is the exact set of Lean names, inputs, and output claims. They are not human reviews.",
        ]
    )
    review_rows: list[Sequence[str]] = []
    review_task_rows: list[Sequence[str]] = []
    for review in inputs.reviews:
        reviewer = review.get("reviewer", {})
        review_rows.append(
            (
                latex_escape(review.get("review_id")),
                latex_escape(reviewer.get("focus")),
                latex_escape(review.get("overall_status")),
            )
        )
        for task_review in review.get("task_reviews", []):
            review_task_rows.append(
                (
                    latex_escape(review.get("review_id")),
                    latex_escape(task_review.get("task_id")),
                    latex_escape(task_review.get("review_outcome")),
                )
            )
    lines.extend(
        _longtable(
            "Review passes",
            "P{0.27\\linewidth}P{0.43\\linewidth}P{0.22\\linewidth}",
            ("Review", "Focus", "Overall status"),
            review_rows,
            size="footnotesize",
        )
    )
    lines.extend(
        _longtable(
            "Review outcome for each task",
            "P{0.34\\linewidth}P{0.18\\linewidth}P{0.40\\linewidth}",
            ("Review", "Task", "Outcome"),
            review_task_rows,
            size="footnotesize",
        )
    )

    lines.extend(
        [
            r"\section{Measurement limits and result meaning}",
            "Each task-condition pair was repeated three times. A repetition is another fresh attempt at the same fixed task. The labels rep-01, rep-02, and rep-03 are not random seeds.",
            "A model token is a small piece of text counted by the model service. The fixed limit was "
            + latex_escape(limits.get("total_model_tokens"))
            + " total model tokens and "
            + latex_escape(limits.get("wall_clock_seconds"))
            + " seconds per attempt.",
        ]
    )
    if observational:
        lines.append(
            r"\textbf{All result tables in this section are observational only and are not official HighamBench scores.} They describe this one complete pilot matrix under the recorded deviations."
        )

    per_run_rows: list[Sequence[str]] = []
    for run in analysis["per_run_results"]:
        status = "final" if run.get("run_id") in selected_ids else "system incident"
        per_run_rows.append(
            (
                latex_escape(run.get("run_id")),
                latex_escape(status),
                latex_escape(run.get("task_id")),
                latex_escape(run.get("repetition_id")),
                latex_escape(run.get("condition")),
                latex_escape(_fmt_number(run.get("pass"))),
                latex_escape(_fmt_number(run.get("scored_elapsed_seconds"))),
                latex_escape(_fmt_number(run.get("model_tokens"), 0)),
                latex_escape(run.get("failure_code")),
            )
        )
    lines.extend(
        _longtable(
            "Every run record (observational only, not an official score)" if observational else "Every run record",
            "P{0.20\\linewidth}P{0.09\\linewidth}P{0.09\\linewidth}P{0.07\\linewidth}P{0.05\\linewidth}rrrrP{0.10\\linewidth}",
            ("Run", "Kind", "Task", "Rep.", "Cond.", "Pass", "Seconds", "Tokens", "Failure"),
            per_run_rows,
            size="scriptsize",
        )
    )

    condition_result_rows: list[Sequence[str]] = []
    for row in conditions:
        run_count, passes_count, pass_rate, seconds, tokens, l_use = _condition_values(row, observational)
        condition_result_rows.append(
            (
                latex_escape(row.get("agent_id")),
                latex_escape(row.get("scope")),
                latex_escape(row.get("condition")),
                latex_escape(run_count),
                latex_escape(passes_count),
                _fmt_rate(pass_rate),
                latex_escape(_fmt_number(seconds)),
                latex_escape(_fmt_number(tokens, 1)),
                latex_escape(l_use),
            )
        )
    lines.extend(
        _longtable(
            "Per-condition results (observational only, not an official score)" if observational else "Per-condition results",
            "P{0.13\\linewidth}P{0.10\\linewidth}P{0.06\\linewidth}rrrrrr",
            ("Agent", "Scope", "Cond.", "Runs", "Pass", "Rate", "Med. s", "Med. tok.", "L-use"),
            condition_result_rows,
            size="scriptsize",
        )
    )
    lines.append(
        "Median means the middle measured value after sorting. L-use is the number of passing L runs whose final proof truly depended on at least one NumStability declaration. A declaration is a named Lean fact or definition."
    )

    task_result_rows: list[Sequence[str]] = []
    for row in tasks:
        run_count, passes_count, pass_rate, seconds, tokens, l_use = _condition_values(row, observational)
        task_result_rows.append(
            (
                latex_escape(row.get("task_id")),
                latex_escape(row.get("tier")),
                latex_escape(row.get("condition")),
                latex_escape(run_count),
                latex_escape(passes_count),
                _fmt_rate(pass_rate),
                latex_escape(_fmt_number(seconds)),
                latex_escape(_fmt_number(tokens, 1)),
                latex_escape(l_use),
            )
        )
    lines.extend(
        _longtable(
            "Per-task results (observational only, not an official score)" if observational else "Per-task results",
            "P{0.16\\linewidth}P{0.06\\linewidth}P{0.06\\linewidth}rrrrrr",
            ("Task", "Tier", "Cond.", "Runs", "Pass", "Rate", "Med. s", "Med. tok.", "L-use"),
            task_result_rows,
            size="scriptsize",
        )
    )

    lines.extend(
        [
            r"\subsection{Failures}",
            "A failure code is a short, fixed reason for an unsuccessful run. TIME means the time limit; TOKEN means the token limit; NONE means no proof file; RULE means a forbidden shortcut; SYNTAX means Lean could not understand the file; PROOF means Lean found an unfinished or incorrect proof; SYSTEM means the measurement machinery failed.",
        ]
    )
    failure_rows: list[Sequence[str]] = []
    for row in conditions:
        if row.get("scope") != "overall":
            continue
        counts = row.get("failure_counts")
        if not isinstance(counts, Mapping):
            raise ReportError("condition result row has no failure counts")
        for code in FAILURE_CODES:
            failure_rows.append(
                (
                    latex_escape(row.get("condition")),
                    latex_escape(code),
                    latex_escape(counts.get(code, 0)),
                )
            )
    lines.extend(
        _longtable(
            "Failure counts by condition (observational only, not an official score)" if observational else "Failure counts by condition",
            "P{0.20\\linewidth}P{0.42\\linewidth}P{0.20\\linewidth}",
            ("Condition", "Failure code", "Count"),
            failure_rows,
        )
    )

    lines.extend(
        [
            r"\subsection{Matched N/L changes}",
            "A pair contains the N and L attempt for the same task and repetition. Every change below is L minus N. A positive pass change favors L. A negative time or token change means L used less. The reported center for time and tokens is the median of the within-pair changes, not the difference between two unrelated medians. The abbreviation pp means percentage points, the direct difference between two percentages.",
            "A 95 percent range is meant to show uncertainty. Here it is made by a bootstrap, which means repeatedly drawing whole papers from the paper set and recalculating the result.",
        ]
    )
    pair_result_rows: list[Sequence[str]] = []
    for row in pairs:
        pass_change, time_change, token_change = _pair_values(row, observational)
        pair_result_rows.append(
            (
                latex_escape(row.get("scope")),
                latex_escape(row.get("pairs")),
                _fmt_delta(pass_change, scale=100.0) + " pp",
                _range(row, "pass_rate_change", scale=100.0) + " pp",
                _fmt_delta(time_change),
                _range(row, "median_paired_time_change"),
                _fmt_delta(token_change),
                _range(row, "median_paired_token_change"),
            )
        )
    lines.extend(
        _longtable(
            "Paired changes by tier (observational only, not an official score)" if observational else "Paired changes by tier",
            "P{0.10\\linewidth}rP{0.09\\linewidth}P{0.15\\linewidth}P{0.08\\linewidth}P{0.15\\linewidth}P{0.08\\linewidth}P{0.15\\linewidth}",
            ("Scope", "Pairs", "Pass", "95\\% range", "Seconds", "95\\% range", "Tokens", "95\\% range"),
            pair_result_rows,
            size="scriptsize",
        )
    )
    task_pair_result_rows: list[Sequence[str]] = []
    for row in task_pairs:
        pass_change, time_change, token_change = _pair_values(row, observational)
        task_pair_result_rows.append(
            (
                latex_escape(row.get("task_id")),
                latex_escape(row.get("tier")),
                latex_escape(row.get("pairs")),
                _fmt_delta(pass_change, scale=100.0) + " pp",
                _fmt_delta(time_change),
                _fmt_delta(token_change),
            )
        )
    lines.extend(
        _longtable(
            "Per-task paired changes (observational only, not an official score)" if observational else "Per-task paired changes",
            "P{0.22\\linewidth}P{0.08\\linewidth}rP{0.15\\linewidth}P{0.15\\linewidth}P{0.15\\linewidth}",
            ("Task", "Tier", "Pairs", "Pass change", "Second change", "Token change"),
            task_pair_result_rows,
            size="footnotesize",
        )
    )
    if paper_count == 1:
        lines.extend(
            [
                r"\begin{center}",
                r"\fcolorbox{red!70!black}{yellow!12}{\parbox{0.92\linewidth}{\textbf{One-paper warning.} A bootstrap is repeated resampling used to make an uncertainty range. This report resamples whole papers, but there is only one paper. It therefore chooses the same paper again and again. The resulting 95\% range is degenerate, meaning it has no useful information about how results vary across papers. It is shown only as an arithmetic check and must not be read as broad certainty.}}",
                r"\end{center}",
            ]
        )

    lines.extend(
        [
            r"\subsection{Actual library use in condition L}",
            "A passing L proof counts as library use only when the dependency audit finds at least one NumStability declaration in the final proof path. Merely importing or searching the library does not count.",
        ]
    )
    library_rows: list[Sequence[str]] = []
    declarations_by_task: dict[str, set[str]] = {}
    for run in selected_runs:
        if run.get("condition") != "L":
            continue
        declarations = run.get("library_declarations")
        names = [str(name) for name in declarations] if isinstance(declarations, list) else []
        task_id = str(run.get("task_id"))
        declarations_by_task.setdefault(task_id, set()).update(names)
        library_rows.append(
            (
                latex_escape(run.get("run_id")),
                latex_escape(task_id),
                latex_escape(run.get("repetition_id")),
                latex_escape(_fmt_number(run.get("pass"))),
                latex_escape(_fmt_number(run.get("library_use"))),
                latex_escape(len(names)),
            )
        )
    lines.extend(
        _longtable(
            "Library-use result for every selected L run (observational only, not an official score)" if observational else "Library-use result for every selected L run",
            "P{0.28\\linewidth}P{0.14\\linewidth}P{0.10\\linewidth}P{0.10\\linewidth}P{0.12\\linewidth}P{0.10\\linewidth}",
            ("Run", "Task", "Rep.", "Pass", "Used library", "Decl. count"),
            library_rows,
            size="footnotesize",
        )
    )
    for task_id in sorted(declarations_by_task):
        names = sorted(declarations_by_task[task_id])
        if names:
            lines.append(
                "Recorded NumStability declarations for "
                + latex_escape(task_id)
                + ": "
                + ", ".join(_inline_code(name) for name in names)
                + "."
            )
        else:
            lines.append("No NumStability declaration was recorded for " + latex_escape(task_id) + ".")

    lines.extend(
        [
            r"\section{Why these are not reference scores}",
            "A reference protocol is the full set of rules required for a result to be called an official HighamBench score. This run set is complete, but the recorded setup differs from that protocol in the following ways:",
            r"\begin{enumerate}",
        ]
    )
    for deviation in environment.get("known_reference_protocol_deviations", []):
        lines.append(r"\item " + latex_escape(deviation))
    lines.extend(
        [
            r"\end{enumerate}",
            "OCI is a standard format for a frozen container image, which is a saved software filesystem. This pilot has no OCI image fingerprint. It instead records a bubblewrap environment bundle fingerprint. The latter detects recorded component changes but is not the reference protocol's frozen image.",
            "The host folders /usr, /bin, /lib*, and /etc are mounted read-only, which means an attempt can read them but cannot change them. They are not one fully fingerprinted OCI filesystem, so this result remains observational rather than an official score.",
            "A backend seed is a number that asks the model service to repeat its random choices. No accepted and enforced seed input was available, so the three repetition labels must not be described as seeds.",
            "The token-timing caveat means the service reports exact token totals when the full model turn ends. A proof can first become valid slightly earlier, so a small amount of later text may be present in its token total. First-valid wall time is still taken when the validator first accepts the proof.",
            r"\section{Implementation file map}",
            "The table below says where each part lives. A JSON file is a structured text record that programs can read. A JSONL file is one JSON record per line.",
        ]
    )
    file_rows = [
        ("shared/HighamBench/Core.lean", "Definitions genuinely shared by several papers."),
        ("shared/HighamBench/P*Definitions.lean", "The extra definitions exposed only to one paper."),
        ("tasks/P*/T*/", "Every manifest task's target, paper context, and task record."),
        ("metadata/manifest.json", "Paper, source anchors, task bindings, and hashes."),
        ("metadata/config.json", "Versions, conditions, repetitions, and limits."),
        ("metadata/environment.json", "Machine, tools, isolation, and known deviations."),
        ("metadata/run_order.json", f"The fixed N/L order for all {pair_count} pairs."),
        ("metadata/release_files.json", "The fingerprints of the complete evaluation package."),
        ("metadata/library_source.json", "The exact NumStability source-file list."),
        ("metadata/library_olean.json", "The exact pruned NumStability compiled-file list."),
        ("metadata/packages_olean.json", "Fingerprints for compiled Lean and package trees."),
        ("metadata/packages_runtime.json", "The exact pruned package files exposed inside a run."),
        ("metadata/evidence/", "Real N-absence and L-library-use construction checks."),
        ("metadata/reviews/", "The independent review records for every task."),
        ("tools/codex_isolated.py", "Starts one fresh restricted Codex attempt."),
        ("tools/offline_shell.c", "Installs the no-socket kernel rule for model shell commands."),
        ("tools/lean_isolated.py", "Runs Lean with exactly the files allowed by N or L."),
        ("tools/preflight.py", "Scans each complete staged N task and tests the forbidden import."),
        ("tools/refresh_snapshot.py", "Regenerates metadata uniformly for every manifest paper."),
        ("tools/run_matrix.py", f"Runs the {run_count} assignments in their fixed order."),
        ("tools/runner.py", "Records one attempt, its time, tokens, and validation result."),
        ("tools/validator.py", "Checks statement identity, forbidden shortcuts, compilation, and dependencies."),
        ("tools/result_set.py", "Rejects a missing, repeated, mismatched, or out-of-order final matrix."),
        ("tools/analyze.py", "Makes all run, condition, task, failure, pair, and library-use summaries."),
        ("tools/render_report.py", "Makes this detailed LaTeX report and can compile its PDF."),
        ("result folder/freeze_check.json", "Records the checked release, tools, and compiled setup used by every run."),
    ]
    lines.extend(
        _longtable(
            "Implementation files",
            "P{0.36\\linewidth}P{0.56\\linewidth}",
            ("Path or result artifact", "Purpose"),
            ((latex_escape(path), latex_escape(purpose)) for path, purpose in file_rows),
            size="footnotesize",
        )
    )

    benchmark_id = inputs.config.get("benchmark_id")
    lines.extend(
        [
            r"\section{How to reproduce the artifacts}",
            "Run all commands from the repository root. Replace words in angle brackets with local paths. The authentication file is secret; do not copy it into a result folder or report.",
            r"\subsection{1. Run the tool tests}",
            r"\begin{lstlisting}",
            "python3 -m unittest discover -s paper_bencmark/highambench/tools/tests -v",
            r"\end{lstlisting}",
            r"\subsection{2. Run the fixed matrix}",
            r"The two verification flags below are used because both controls were checked. The frozen Codex feature list contains \texttt{rollout\_budget}, which is the model service's token-limit control. The strict agent setup turns it on, fixes \texttt{limit\_tokens} to the benchmark limit, and gives both input and generated tokens weight 1. Tests check that this setup is passed exactly once. The program reads the environment identity, agent version, model, reasoning level, and limits from the authenticated metadata; they are not free command-line choices.",
            r"\begin{lstlisting}",
            "python3 paper_bencmark/highambench/tools/run_matrix.py \\",
            "  --benchmark-root paper_bencmark/highambench \\",
            "  --project-root . \\",
            "  --results-root paper_bencmark/scratch_pad/highambench_results \\",
            "  --codex <CODEX_BINARY> --auth-file <CODEX_AUTH_FILE> \\",
            "  --offline-shell <OFFLINE_SHELL_BINARY> \\",
            "  --toolchain-root <LEAN_TOOLCHAIN_ROOT> \\",
            "  --packages-root .lake/packages \\",
            "  --packages-runtime-root " + PACKAGES_RUNTIME_ROOT + " \\",
            "  --shared-olean-root paper_bencmark/scratch_pad/highambench_environment/shared_olean \\",
            "  --library-source NumStability --library-root-file NumStability.lean \\",
            "  --library-olean " + PRUNED_LIBRARY_OLEAN_ROOT + " \\",
            "  --release-manifest paper_bencmark/highambench/metadata/release_files.json \\",
            "  --agent-network-verified --token-control-verified",
            r"\end{lstlisting}",
            r"\subsection{3. Check completeness and make summary data}",
            r"\begin{lstlisting}",
            "python3 paper_bencmark/highambench/tools/analyze.py \\",
            "  paper_bencmark/scratch_pad/highambench_results/runs.jsonl \\",
            "  --output-dir paper_bencmark/scratch_pad/highambench_results/analysis \\",
            "  --run-order paper_bencmark/highambench/metadata/run_order.json \\",
            "  --config paper_bencmark/highambench/metadata/config.json \\",
            "  --manifest paper_bencmark/highambench/metadata/manifest.json \\",
            "  --repository-root . --observational-pilot",
            r"\end{lstlisting}",
            r"\subsection{4. Make this report and PDF}",
            r"\begin{lstlisting}",
            "python3 paper_bencmark/highambench/tools/render_report.py \\",
            "  --analysis paper_bencmark/scratch_pad/highambench_results/analysis/summary.json \\",
            "  --output-tex paper_bencmark/scratch_pad/HighamBench_Report.tex \\",
            "  --compile-pdf",
            r"\end{lstlisting}",
            "The report builder rereads the final metadata, evidence, reviews, and analysis. It also requires the nearby frozen-run check, checks its fingerprint against the accepted result set, verifies the release files, and compares the construction tools, Python executable, pruned package view, and pruned NumStability library with those fixed identities. It refuses missing runs, stale records, damaged network evidence, failed token-control evidence, failed construction checks, or missing task summaries. This prevents an incomplete measurement from becoming a polished report by accident.",
            r"\section{Final scope statement}",
            "This measurement snapshot contains " + latex_escape(paper_count) + " paper(s) and " + latex_escape(task_count) + " fixed task(s). It measures proof completion under N and L; it does not measure how well an agent translates unrestricted paper prose into Lean because the statements are fixed before each run. The correct result label for the present setup is: ",
            (r"\textbf{observational pilot, not an official HighamBench score.}" if observational else r"\textbf{official HighamBench reference score.}"),
            "Recorded benchmark ID: " + _inline_code(benchmark_id) + ".",
            r"\end{document}",
            "",
        ]
    )
    return "\n".join(lines)


def write_report(output_tex: Path, document: str, *, compile_pdf: bool) -> Path | None:
    output = output_tex.resolve()
    if output.suffix.lower() != ".tex":
        raise ReportError("--output-tex must end in .tex")
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_name("." + output.name + ".tmp")
    temporary.write_text(document, encoding="utf-8")
    temporary.replace(output)
    if not compile_pdf:
        return None
    latexmk = shutil.which("latexmk")
    if latexmk is None:
        raise ReportError("--compile-pdf was requested, but latexmk is not installed")
    command = [
        latexmk,
        "-norc",
        "-pdf",
        "-interaction=nonstopmode",
        "-halt-on-error",
        f"-outdir={output.parent}",
        str(output),
    ]
    completed = subprocess.run(
        command,
        cwd=output.parent,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    if completed.returncode != 0:
        tail = "\n".join(completed.stdout.splitlines()[-40:])
        raise ReportError(f"latexmk failed with exit code {completed.returncode}:\n{tail}")
    pdf = output.with_suffix(".pdf")
    if not pdf.is_file():
        raise ReportError("latexmk returned success but did not create the expected PDF")
    return pdf


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--benchmark-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="HighamBench directory; defaults to the parent of tools/",
    )
    parser.add_argument("--analysis", type=Path, required=True, help="analyze.py summary.json")
    parser.add_argument("--output-tex", type=Path, required=True)
    parser.add_argument("--compile-pdf", action="store_true")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    try:
        inputs = load_report_inputs(args.benchmark_root, args.analysis)
        document = render_report(inputs)
        pdf = write_report(args.output_tex, document, compile_pdf=args.compile_pdf)
        result = {
            "benchmark_id": inputs.config.get("benchmark_id"),
            "latex": str(args.output_tex.resolve()),
            "pdf": str(pdf) if pdf is not None else None,
            "official_scores_valid": inputs.analysis.get("official_scores_valid") is True,
        }
        print(json.dumps(result, indent=2, sort_keys=True))
        return 0
    except (OSError, ReportError) as error:
        print(f"report error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
