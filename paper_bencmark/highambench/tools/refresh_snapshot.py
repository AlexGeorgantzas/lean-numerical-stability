#!/usr/bin/env python3
"""Refresh HighamBench construction or measurement metadata for every paper.

The central manifest is the ordered corpus description. This tool applies one
workflow to every manifest paper: validate task metadata, rebuild controlled
manifests, regenerate the paired run order, snapshot the complete evaluation
tree, and recompute the environment identity.
"""

from __future__ import annotations

import argparse
import hashlib
from pathlib import Path
from pathlib import PurePosixPath
import re
import sys
from typing import Any, Mapping, Sequence

try:
    from .common import BenchmarkToolError, read_json, sha256_file, write_json
    from .hashes import create_manifest
    from .run_matrix import (
        ENVIRONMENT_BUNDLE_DEFINITION,
        environment_bundle_digest,
        evaluation_release_tree_files,
    )
    from .task_tags import validate_task_catalog
except ImportError:  # Direct script execution.
    from common import BenchmarkToolError, read_json, sha256_file, write_json  # type: ignore
    from hashes import create_manifest  # type: ignore
    from run_matrix import (  # type: ignore
        ENVIRONMENT_BUNDLE_DEFINITION,
        environment_bundle_digest,
        evaluation_release_tree_files,
    )
    from task_tags import validate_task_catalog  # type: ignore


PHASE_CONSTRUCTION = "construction"
PHASE_MEASUREMENT_READY = "measurement-ready"
PHASES = (PHASE_CONSTRUCTION, PHASE_MEASUREMENT_READY)
PAIR_ORDER_VERSION = 2
RELEASE_MANIFEST_RELATIVE = "metadata/release_files.json"
PROJECT_BENCHMARK_PREFIX = PurePosixPath("paper_bencmark/highambench")


def _object(value: Any, label: str) -> dict[str, Any]:
    if not isinstance(value, dict):
        raise BenchmarkToolError(f"{label} must be a JSON object")
    return value


def _papers(manifest: Mapping[str, Any]) -> list[dict[str, Any]]:
    raw = manifest.get("papers")
    if not isinstance(raw, list) or not raw:
        raise BenchmarkToolError("metadata/manifest.json must contain papers")
    papers: list[dict[str, Any]] = []
    seen: set[str] = set()
    for index, value in enumerate(raw):
        paper = _object(value, f"manifest paper {index}")
        paper_id = paper.get("paper_id")
        if not isinstance(paper_id, str) or re.fullmatch(r"P[0-9]+", paper_id) is None:
            raise BenchmarkToolError(f"invalid manifest paper_id: {paper_id!r}")
        if paper_id in seen:
            raise BenchmarkToolError(f"manifest repeats paper_id {paper_id}")
        seen.add(paper_id)
        targets = paper.get("targets")
        if not isinstance(targets, list):
            raise BenchmarkToolError(f"manifest paper {paper_id} has no targets list")
        papers.append(paper)
    return papers


def _available_targets(
    papers: Sequence[Mapping[str, Any]],
) -> list[tuple[str, str, str, dict[str, Any]]]:
    result: list[tuple[str, str, str, dict[str, Any]]] = []
    seen: set[str] = set()
    for paper in papers:
        paper_id = str(paper["paper_id"])
        for index, value in enumerate(paper["targets"]):
            target = _object(value, f"manifest target {paper_id}[{index}]")
            if target.get("availability") != "available":
                continue
            tier = target.get("tier")
            task_id = target.get("task_id")
            if not isinstance(tier, str) or re.fullmatch(r"T[0-9]+", tier) is None:
                raise BenchmarkToolError(f"invalid tier for {paper_id}: {tier!r}")
            if task_id != f"{paper_id}-{tier}":
                raise BenchmarkToolError(
                    f"manifest task identity disagrees: {task_id!r}, {paper_id}, {tier}"
                )
            if task_id in seen:
                raise BenchmarkToolError(f"manifest repeats task_id {task_id}")
            seen.add(str(task_id))
            result.append((paper_id, tier, str(task_id), target))
    if not result:
        raise BenchmarkToolError("manifest contains no available tasks")
    return result


def _corpus_slug(paper_ids: Sequence[str]) -> str:
    return "-".join(paper_id.lower() for paper_id in paper_ids)


def _benchmark_id(manifest: Mapping[str, Any], paper_ids: Sequence[str]) -> str:
    specification = manifest.get("specification")
    version = specification.get("version") if isinstance(specification, Mapping) else None
    if not isinstance(version, str) or not version:
        raise BenchmarkToolError("manifest specification has no version")
    return f"highambench-{version}-{_corpus_slug(paper_ids)}"


def _benchmark_relative_path(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise BenchmarkToolError(f"{label} must be a nonempty path")
    declared = PurePosixPath(value)
    if declared.is_absolute() or ".." in declared.parts:
        raise BenchmarkToolError(f"{label} must be a safe benchmark path")
    try:
        relative = declared.relative_to(PROJECT_BENCHMARK_PREFIX)
    except ValueError:
        relative = declared
    return relative.as_posix()


def _sync_shared_bindings(
    root: Path,
    manifest: dict[str, Any],
    paper_ids: Sequence[str],
    *,
    phase: str,
) -> dict[str, list[str]]:
    """Hash shared modules and return each paper's exact staged source list."""

    raw_entries = manifest.get("controlled_shared_files")
    if not isinstance(raw_entries, list) or not raw_entries:
        raise BenchmarkToolError("manifest must contain controlled_shared_files")
    known_papers = set(paper_ids)
    by_paper = {paper_id: [] for paper_id in paper_ids}
    seen_paths: set[str] = set()
    for index, raw_entry in enumerate(raw_entries):
        entry = _object(raw_entry, f"controlled_shared_files[{index}]")
        relative = _benchmark_relative_path(
            entry.get("path"), f"controlled_shared_files[{index}].path"
        )
        relative_path = PurePosixPath(relative)
        if (
            len(relative_path.parts) < 3
            or relative_path.parts[:2] != ("shared", "HighamBench")
            or relative_path.suffix != ".lean"
        ):
            raise BenchmarkToolError(
                f"controlled shared file must be a Lean module below shared/HighamBench: {relative}"
            )
        if relative in seen_paths:
            raise BenchmarkToolError(f"controlled shared file is repeated: {relative}")
        seen_paths.add(relative)
        path = root / relative
        if path.is_symlink() or not path.is_file():
            raise BenchmarkToolError(f"missing regular controlled shared file: {path}")

        scope = entry.get("paper_ids")
        if (
            not isinstance(scope, list)
            or not scope
            or any(not isinstance(paper_id, str) for paper_id in scope)
            or len(set(scope)) != len(scope)
        ):
            raise BenchmarkToolError(
                f"controlled shared file {relative} must have unique paper_ids"
            )
        unknown = sorted(set(scope) - known_papers)
        if unknown:
            raise BenchmarkToolError(
                f"controlled shared file {relative} names unknown papers: {', '.join(unknown)}"
            )

        entry["path"] = (PROJECT_BENCHMARK_PREFIX / relative_path).as_posix()
        entry["sha256"] = sha256_file(path)
        entry["status"] = (
            "current construction snapshot; rebuilt and rehashed for its declared paper scope"
            if phase == PHASE_CONSTRUCTION
            else "measurement-ready shared setting for its declared paper scope"
        )
        for paper_id in scope:
            by_paper[paper_id].append(relative)

    missing = [paper_id for paper_id, files in by_paper.items() if not files]
    if missing:
        raise BenchmarkToolError(
            "every paper must receive at least one controlled shared Lean file: "
            + ", ".join(missing)
        )
    return by_paper


def _set_task_phase(
    root: Path,
    papers: Sequence[Mapping[str, Any]],
    targets: Sequence[tuple[str, str, str, Mapping[str, Any]]],
    *,
    measurement_ready: bool,
) -> None:
    tasks_by_paper: dict[str, list[str]] = {str(paper["paper_id"]): [] for paper in papers}
    for paper_id, tier, task_id, _target in targets:
        task_path = root / "tasks" / paper_id / tier / "task.json"
        task = _object(read_json(task_path), f"{task_id} task record")
        if task.get("task_id") != task_id or task.get("paper_id") != paper_id or task.get("tier") != tier:
            raise BenchmarkToolError(f"{task_id} task identity disagrees with its path")
        task["classification_frozen_before_runs"] = measurement_ready
        write_json(task_path, task)
        tasks_by_paper[paper_id].append(task_id)

    for paper in papers:
        paper_id = str(paper["paper_id"])
        path = root / "tasks" / paper_id / "paper.json"
        record = _object(read_json(path), f"{paper_id} paper record")
        if record.get("paper_id") != paper_id:
            raise BenchmarkToolError(f"{paper_id} paper record has the wrong paper_id")
        record["classification_frozen_before_runs"] = measurement_ready
        record["included_tasks"] = tasks_by_paper[paper_id]
        record.pop("excluded_papers", None)
        record["corpus_membership"] = (
            "This paper is part of the current corpus listed in metadata/manifest.json."
        )
        write_json(path, record)


def _measurement_readiness(
    root: Path,
    targets: Sequence[tuple[str, str, str, Mapping[str, Any]]],
) -> None:
    """Require complete construction and two current reviews for every task."""

    task_ids = [task_id for _paper_id, _tier, task_id, _target in targets]
    evidence_dir = root / "metadata" / "evidence"
    construction_records: list[Mapping[str, Any]] = []
    if evidence_dir.is_dir():
        for path in sorted(evidence_dir.glob("*.json")):
            value = read_json(path)
            if isinstance(value, Mapping) and value.get("kind") == "highambench-private-construction-check":
                construction_records.append(value)
    complete = []
    current_manifest_sha256 = sha256_file(root / "metadata" / "manifest.json")
    for record in construction_records:
        scope = record.get("scope")
        summary = record.get("summary")
        proof_count = len(task_ids) * 2
        if (
            record.get("pass") is True
            and record.get("record_status") == "current_final"
            and isinstance(scope, Mapping)
            and scope.get("complete_manifest_scope") is True
            and scope.get("selected_task_ids") == task_ids
            and scope.get("central_manifest_sha256") == current_manifest_sha256
            and isinstance(summary, Mapping)
            and summary.get("expected") == proof_count
            and summary.get("checked") == proof_count
            and summary.get("passed") == proof_count
        ):
            complete.append(record)
    if not complete:
        raise BenchmarkToolError(
            "measurement-ready phase requires one passing full-corpus private construction record"
        )

    coverage = {task_id: 0 for task_id in task_ids}
    reviews_dir = root / "metadata" / "reviews"
    if reviews_dir.is_dir():
        for path in sorted(reviews_dir.glob("*.json")):
            review = read_json(path)
            if not isinstance(review, Mapping) or review.get("record_status") != "current_final":
                continue
            task_reviews = review.get("task_reviews")
            if not isinstance(task_reviews, list):
                continue
            covered_in_record: set[str] = set()
            for raw_task_review in task_reviews:
                if not isinstance(raw_task_review, Mapping):
                    continue
                task_id = raw_task_review.get("task_id")
                outcome = raw_task_review.get(
                    "review_outcome", raw_task_review.get("outcome")
                )
                if (
                    task_id in coverage
                    and task_id not in covered_in_record
                    and isinstance(outcome, str)
                    and outcome.lower().startswith("pass")
                ):
                    coverage[str(task_id)] += 1
                    covered_in_record.add(str(task_id))
    missing = [task_id for task_id, count in coverage.items() if count < 2]
    if missing:
        raise BenchmarkToolError(
            "measurement-ready phase requires two current final reviews for every task; missing: "
            + ", ".join(missing)
        )


def _sync_manifest(
    root: Path,
    manifest: dict[str, Any],
    papers: Sequence[dict[str, Any]],
    targets: Sequence[tuple[str, str, str, dict[str, Any]]],
    *,
    benchmark_id: str,
    phase: str,
) -> None:
    paper_ids = [str(paper["paper_id"]) for paper in papers]
    manifest["benchmark_id"] = benchmark_id
    manifest["benchmark_status"] = (
        "corpus under construction; measurements prohibited"
        if phase == PHASE_CONSTRUCTION
        else "measurement-ready corpus snapshot; measurements pending"
    )
    corpus = _object(manifest.setdefault("corpus", {}), "manifest corpus")
    corpus["paper_count"] = len(paper_ids)
    corpus["paper_ids"] = paper_ids
    corpus["exclusion_note"] = (
        "These ordered paper IDs are the current construction corpus. The corpus may "
        "grow until a measurement-ready snapshot is created."
        if phase == PHASE_CONSTRUCTION
        else "These ordered paper IDs are the complete corpus for this measurement snapshot."
    )
    shared_by_paper = _sync_shared_bindings(
        root, manifest, paper_ids, phase=phase
    )
    binding_status = (
        "current construction snapshot; editable and rehashed before measurement"
        if phase == PHASE_CONSTRUCTION
        else "measurement-ready path, declaration, content hash, and N/L target builds"
    )
    for paper_id, tier, task_id, target in targets:
        target_path = root / "tasks" / paper_id / tier / "Target.lean"
        if not target_path.is_file() or target_path.is_symlink():
            raise BenchmarkToolError(f"missing regular target file for {task_id}: {target_path}")
        lean_target = _object(target.get("lean_target"), f"{task_id} lean_target")
        lean_target["controlled_file_sha256"] = sha256_file(target_path)
        lean_target["binding_status"] = binding_status
        lean_target["shared_files"] = [
            (PROJECT_BENCHMARK_PREFIX / PurePosixPath(relative)).as_posix()
            for relative in shared_by_paper[paper_id]
        ]
        lean_target.pop("shared_definitions", None)
    task_count = len(targets)
    manifest["release_rule"] = (
        "The benchmark remains editable during construction. Before measured runs, "
        "create one measurement-ready snapshot and verify every task, proof, review, "
        "controlled manifest, and planned run against that snapshot."
        if phase == PHASE_CONSTRUCTION
        else f"Do not report measurements unless all {task_count} task packages, their "
        "construction proofs, reviews, and the complete run matrix verify against this snapshot."
    )
    write_json(root / "metadata" / "manifest.json", manifest)


def _sync_controlled_manifests(
    root: Path,
    targets: Sequence[tuple[str, str, str, Mapping[str, Any]]],
) -> None:
    controlled_root = root / "metadata" / "controlled"
    controlled_root.mkdir(parents=True, exist_ok=True)
    expected_names: set[str] = set()
    for paper_id, tier, task_id, target in targets:
        expected_names.add(f"{task_id}.json")
        lean_target = _object(target.get("lean_target"), f"{task_id} lean_target")
        raw_shared = lean_target.get("shared_files")
        if not isinstance(raw_shared, list) or not raw_shared:
            raise BenchmarkToolError(f"{task_id} lean_target has no shared_files")
        shared = [
            _benchmark_relative_path(value, f"{task_id} shared_files")
            for value in raw_shared
        ]
        controlled = create_manifest(
            root,
            requested=[
                "agent_prompt.md",
                *shared,
                f"tasks/{paper_id}/{tier}/Target.lean",
                f"tasks/{paper_id}/{tier}/context.md",
            ],
            label=f"{task_id}-controlled",
        )
        write_json(controlled_root / f"{task_id}.json", controlled)
    extra = sorted(
        path.name for path in controlled_root.glob("*.json") if path.name not in expected_names
    )
    if extra:
        raise BenchmarkToolError(
            "controlled manifests exist for tasks outside the current manifest: "
            + ", ".join(extra)
        )


def _sync_run_order(
    root: Path,
    config: dict[str, Any],
    manifest: Mapping[str, Any],
    targets: Sequence[tuple[str, str, str, Mapping[str, Any]]],
    *,
    benchmark_id: str,
) -> None:
    repetitions = config.get("repetitions")
    if not isinstance(repetitions, list) or not repetitions:
        raise BenchmarkToolError("config repetitions must be a nonempty list")
    repetition_ids: list[str] = []
    for index, value in enumerate(repetitions):
        repetition = _object(value, f"config repetition {index}")
        repetition_id = repetition.get("id")
        if not isinstance(repetition_id, str) or not repetition_id:
            raise BenchmarkToolError(f"config repetition {index} has no id")
        repetition_ids.append(repetition_id)
    if len(set(repetition_ids)) != len(repetition_ids):
        raise BenchmarkToolError("config repeats a repetition id")

    specification = manifest.get("specification")
    version = specification.get("version") if isinstance(specification, Mapping) else None
    salt = f"highambench-{version}-pair-order-v{PAIR_ORDER_VERSION}"
    pairs: list[dict[str, Any]] = []
    for _paper_id, _tier, task_id, _target in targets:
        for repetition_id in repetition_ids:
            pair_id = f"{task_id}-{repetition_id}"
            digest = hashlib.sha256(
                f"{salt}|{task_id}|{repetition_id}".encode("utf-8")
            ).hexdigest()
            condition_order = ["N", "L"] if int(digest[:2], 16) % 2 == 0 else ["L", "N"]
            pairs.append(
                {
                    "pair_id": pair_id,
                    "task_id": task_id,
                    "repetition_id": repetition_id,
                    "sha256": digest,
                    "condition_order": condition_order,
                    "run_ids": [f"{pair_id}-{condition}" for condition in condition_order],
                }
            )
    run_order = {
        "schema_version": "0.1.0",
        "benchmark_id": benchmark_id,
        "order_scope": "condition order inside each task-repetition pair",
        "method": {
            "name": "sha256_first_byte_parity",
            "version": PAIR_ORDER_VERSION,
            "salt": salt,
            "input": "<salt>|<task_id>|<repetition_id>",
            "rule": "If the first digest byte is even, run N then L; if it is odd, run L then N.",
            "reason": "One deterministic rule is regenerated for every paper and task in manifest order.",
        },
        "pairs": pairs,
    }
    write_json(root / "metadata" / "run_order.json", run_order)

    paper_count = len({paper_id for paper_id, _tier, _task_id, _target in targets})
    task_count = len(targets)
    repetition_count = len(repetition_ids)
    config["benchmark_id"] = benchmark_id
    config["planned_counts_per_agent"] = {
        "papers": paper_count,
        "tasks": task_count,
        "repetitions_per_task": repetition_count,
        "conditions": 2,
        "paired_assignments": task_count * repetition_count,
        "runs": task_count * repetition_count * 2,
    }


def _sync_release_and_environment(
    root: Path,
    config: dict[str, Any],
    environment: dict[str, Any],
    manifest: Mapping[str, Any],
    *,
    corpus_slug: str,
) -> tuple[str, str, int]:
    frozen = _object(config.get("frozen_environment"), "config frozen_environment")
    prompt_sha256 = sha256_file(root / "agent_prompt.md")
    frozen["prompt_sha256"] = prompt_sha256
    agent = _object(environment.setdefault("agent", {}), "environment agent")
    agent["prompt_sha256"] = prompt_sha256

    isolation = environment.get("isolation")
    if isinstance(isolation, dict):
        component_paths = {
            "filesystem_adapter_sha256": "tools/codex_isolated.py",
            "lean_adapter_sha256": "tools/lean_isolated.py",
            "offline_shell_source_sha256": "tools/offline_shell.c",
            "runner_sha256": "tools/runner.py",
            "validator_sha256": "tools/validator.py",
            "dependency_audit_sha256": "tools/dependency_audit.lean",
        }
        for field, relative in component_paths.items():
            isolation[field] = sha256_file(root / relative)

    release = create_manifest(
        root,
        requested=sorted(evaluation_release_tree_files(root)),
        label="evaluation-package-snapshot",
    )
    release_path = root / RELEASE_MANIFEST_RELATIVE
    write_json(release_path, release)
    release_sha256 = sha256_file(release_path)

    frozen["release_manifest"] = "paper_bencmark/highambench/metadata/release_files.json"
    frozen["release_manifest_sha256"] = release_sha256
    environment["release_manifest"] = "paper_bencmark/highambench/metadata/release_files.json"
    environment["release_manifest_sha256"] = release_sha256
    environment["environment_bundle_definition"] = ENVIRONMENT_BUNDLE_DEFINITION

    lean = _object(environment.setdefault("lean", {}), "environment lean")
    shared_sources: dict[str, str] = {}
    raw_shared = manifest.get("controlled_shared_files")
    if not isinstance(raw_shared, list):
        raise BenchmarkToolError("manifest controlled_shared_files is missing")
    for index, raw_entry in enumerate(raw_shared):
        entry = _object(raw_entry, f"controlled_shared_files[{index}]")
        relative = PurePosixPath(
            _benchmark_relative_path(entry.get("path"), "controlled shared path")
        )
        shared_relative = relative.relative_to("shared").as_posix()
        digest = entry.get("sha256")
        if not isinstance(digest, str):
            raise BenchmarkToolError(f"controlled shared file {relative} has no SHA-256")
        shared_sources[shared_relative] = digest
    lean["shared_sources"] = shared_sources
    lean.pop("shared_definitions_sha256", None)
    lean.pop("shared_definitions_olean_sha256", None)
    lean.pop("shared_oleans", None)

    bundle = environment_bundle_digest(config, environment)
    environment_id = f"highambench-{corpus_slug}-{bundle[:16]}"
    frozen["environment_id"] = environment_id
    frozen["environment_bundle_sha256"] = bundle
    environment["environment_id"] = environment_id
    environment["environment_bundle_sha256"] = bundle
    write_json(root / "metadata" / "config.json", config)
    write_json(root / "metadata" / "environment.json", environment)
    return release_sha256, bundle, len(release["files"])


def refresh_snapshot(root: Path, *, phase: str) -> dict[str, Any]:
    if phase not in PHASES:
        raise BenchmarkToolError(f"phase must be one of {', '.join(PHASES)}")
    benchmark_root = root.resolve()
    if not benchmark_root.is_dir():
        raise BenchmarkToolError(f"benchmark root is not a directory: {benchmark_root}")
    manifest = _object(
        read_json(benchmark_root / "metadata" / "manifest.json"), "benchmark manifest"
    )
    config = _object(read_json(benchmark_root / "metadata" / "config.json"), "config")
    environment = _object(
        read_json(benchmark_root / "metadata" / "environment.json"), "environment"
    )
    papers = _papers(manifest)
    targets = _available_targets(papers)
    paper_ids = [str(paper["paper_id"]) for paper in papers]
    benchmark_id = _benchmark_id(manifest, paper_ids)
    measurement_ready = phase == PHASE_MEASUREMENT_READY

    tag_catalog = validate_task_catalog(benchmark_root)
    manifest_task_ids = [task_id for _paper_id, _tier, task_id, _target in targets]
    catalog_task_ids = [str(task["task_id"]) for task in tag_catalog["tasks"]]
    if catalog_task_ids != manifest_task_ids:
        raise BenchmarkToolError(
            "task directories must exactly match available manifest tasks: "
            f"manifest={manifest_task_ids}, directories={catalog_task_ids}"
        )
    paper_record_ids = sorted(path.parent.name for path in (benchmark_root / "tasks").glob("P*/paper.json"))
    if paper_record_ids != sorted(paper_ids):
        raise BenchmarkToolError(
            "paper directories must exactly match manifest papers: "
            f"manifest={sorted(paper_ids)}, directories={paper_record_ids}"
        )

    if measurement_ready:
        _measurement_readiness(benchmark_root, targets)

    _set_task_phase(
        benchmark_root, papers, targets, measurement_ready=measurement_ready
    )
    validate_task_catalog(benchmark_root)
    _sync_manifest(
        benchmark_root,
        manifest,
        papers,
        targets,
        benchmark_id=benchmark_id,
        phase=phase,
    )
    _sync_controlled_manifests(benchmark_root, targets)
    _sync_run_order(
        benchmark_root,
        config,
        manifest,
        targets,
        benchmark_id=benchmark_id,
    )
    config["configuration_status"] = (
        "corpus under construction; task metadata and snapshots may be regenerated"
        if phase == PHASE_CONSTRUCTION
        else "measurement-ready corpus snapshot; changes require a new snapshot"
    )
    frozen = _object(config.get("frozen_environment"), "config frozen_environment")
    frozen["construction_status_note"] = (
        "The corpus is still being built. No measured run may start until every task "
        "has been reviewed and a measurement-ready snapshot is created."
        if phase == PHASE_CONSTRUCTION
        else "Every manifest task is marked measurement-ready for this snapshot. "
        "Construction proofs and reviews must still pass before results are reported."
    )
    environment["benchmark_id"] = benchmark_id
    release_sha256, bundle, release_count = _sync_release_and_environment(
        benchmark_root,
        config,
        environment,
        manifest,
        corpus_slug=_corpus_slug(paper_ids),
    )
    return {
        "ok": True,
        "phase": phase,
        "benchmark_id": benchmark_id,
        "paper_ids": paper_ids,
        "task_ids": [task_id for _paper_id, _tier, task_id, _target in targets],
        "pair_count": len(targets) * len(config["repetitions"]),
        "run_count": len(targets) * len(config["repetitions"]) * 2,
        "release_file_count": release_count,
        "release_manifest_sha256": release_sha256,
        "environment_bundle_sha256": bundle,
        "environment_id": environment["environment_id"],
    }


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--benchmark-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
    )
    parser.add_argument("--phase", choices=PHASES, required=True)
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    try:
        result = refresh_snapshot(args.benchmark_root, phase=args.phase)
    except (OSError, BenchmarkToolError, ValueError) as error:
        print(f"refresh-snapshot error: {error}", file=sys.stderr)
        return 1
    print(
        f"snapshot refreshed: {result['phase']}; {len(result['paper_ids'])} papers, "
        f"{len(result['task_ids'])} tasks, {result['run_count']} planned runs"
    )
    print(f"  benchmark_id: {result['benchmark_id']}")
    print(f"  environment_id: {result['environment_id']}")
    print(f"  release files: {result['release_file_count']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
