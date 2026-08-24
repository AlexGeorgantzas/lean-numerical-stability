#!/usr/bin/env python3
"""Refresh HighamBench construction or measurement metadata for every paper.

The central manifest is the ordered corpus description. This tool applies one
workflow to every manifest paper: validate task metadata, rebuild controlled
manifests, regenerate the paired run order, freeze the live cumulative token
control, snapshot the complete evaluation tree, and recompute the environment
identity.
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
    from . import runner
    from .run_matrix import (
        CONDITION_L_PROMPT_RELATIVE,
        DEFAULT_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS,
        DEFAULT_PROMPT_STARTUP_TIMEOUT_SECONDS,
        ENVIRONMENT_BUNDLE_DEFINITION,
        FROZEN_MODEL_VERSION,
        FROZEN_REASONING_EFFORT,
        PROMPT_PROTOCOL_VERSION,
        canonical_document_digest,
        environment_bundle_digest,
        evaluation_release_tree_files,
        provider_token_gate_environment_record,
        ultra_orchestration_record,
    )
    from .task_tags import validate_task_catalog
except ImportError:  # Direct script execution.
    from common import BenchmarkToolError, read_json, sha256_file, write_json  # type: ignore
    from hashes import create_manifest  # type: ignore
    import runner  # type: ignore
    from run_matrix import (  # type: ignore
        CONDITION_L_PROMPT_RELATIVE,
        DEFAULT_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS,
        DEFAULT_PROMPT_STARTUP_TIMEOUT_SECONDS,
        ENVIRONMENT_BUNDLE_DEFINITION,
        FROZEN_MODEL_VERSION,
        FROZEN_REASONING_EFFORT,
        PROMPT_PROTOCOL_VERSION,
        canonical_document_digest,
        environment_bundle_digest,
        evaluation_release_tree_files,
        provider_token_gate_environment_record,
        ultra_orchestration_record,
    )
    from task_tags import validate_task_catalog  # type: ignore


PHASE_CONSTRUCTION = "construction"
PHASE_MEASUREMENT_READY = "measurement-ready"
PHASES = (PHASE_CONSTRUCTION, PHASE_MEASUREMENT_READY)
PAIR_ORDER_VERSION = 2
RELEASE_MANIFEST_RELATIVE = "metadata/release_files.json"
PROJECT_BENCHMARK_PREFIX = PurePosixPath("paper_bencmark/highambench")
TOKEN_MEASUREMENT_SOURCE = "codex_app_server_rawResponse/completed"
TOKEN_USAGE_NOTIFICATION = "rawResponse/completed"


def _local_shared_imports(path: Path) -> list[tuple[str, int]]:
    """Return local HighamBench modules imported by a controlled source."""

    imports: list[tuple[str, int]] = []
    for line_number, raw_line in enumerate(
        path.read_text(encoding="utf-8").splitlines(), start=1
    ):
        line = raw_line.split("--", 1)[0].strip()
        if not line.startswith("import "):
            continue
        for module in line.removeprefix("import ").split():
            if module.startswith("HighamBench."):
                imports.append((module, line_number))
    return imports


def _session_isolation_record() -> dict[str, Any]:
    """Return the fixed no-history/no-proof-transfer contract for each run."""

    return {
        "ephemeral_thread_start_per_run": False,
        "fresh_codex_state_directory_per_run": True,
        "history_persistence": "none",
        "memories_feature_disabled": True,
        "normal_exit_state_cleanup": True,
        "prior_outputs_or_submissions_mounted": False,
        "state_directory_reused_across_runs": False,
        "thread_resume_or_fork_used": False,
        "provider_prompt_prefix_cache": {
            "automatic_prefix_caching_may_occur": True,
            "cached_input_charged_at_full_token_weight": True,
            "cached_object": "exact-prefix prefill key/value computation, not generated output",
            "cross_run_answer_or_proof_replay": False,
            "kind": "automatic exact-input-prefix prefill computation reuse",
            "pinned_codex_disable_control_available": False,
            "semantic_history_transfer": False,
        },
    }


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
    scopes_by_path: dict[str, set[str]] = {}
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
        scopes_by_path[relative] = set(scope)

    for relative, importer_scope in scopes_by_path.items():
        for module, line_number in _local_shared_imports(root / relative):
            imported = f"shared/{module.replace('.', '/')}.lean"
            dependency_scope = scopes_by_path.get(imported)
            if dependency_scope is None:
                raise BenchmarkToolError(
                    f"controlled shared file {relative}:{line_number} imports undeclared "
                    f"local module {module}"
                )
            missing_scope = sorted(importer_scope - dependency_scope)
            if missing_scope:
                raise BenchmarkToolError(
                    f"controlled shared file {relative}:{line_number} imports {module}, "
                    "but that dependency is unavailable to papers: "
                    + ", ".join(missing_scope)
                )

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
    limits: Mapping[str, Any],
) -> None:
    wall_clock_seconds = limits.get("wall_clock_seconds")
    total_model_tokens = limits.get("total_model_tokens")
    if (
        not isinstance(wall_clock_seconds, int)
        or isinstance(wall_clock_seconds, bool)
        or wall_clock_seconds <= 0
        or not isinstance(total_model_tokens, int)
        or isinstance(total_model_tokens, bool)
        or total_model_tokens <= 0
    ):
        raise BenchmarkToolError("task limits must be positive integers")
    tasks_by_paper: dict[str, list[str]] = {str(paper["paper_id"]): [] for paper in papers}
    for paper_id, tier, task_id, _target in targets:
        task_path = root / "tasks" / paper_id / tier / "task.json"
        task = _object(read_json(task_path), f"{task_id} task record")
        if task.get("task_id") != task_id or task.get("paper_id") != paper_id or task.get("tier") != tier:
            raise BenchmarkToolError(f"{task_id} task identity disagrees with its path")
        task["classification_frozen_before_runs"] = measurement_ready
        task["limits"] = {
            "total_model_tokens": total_model_tokens,
            "wall_clock_seconds": wall_clock_seconds,
        }
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
    *,
    ignore_exact_target_novelty_rejections: bool = False,
) -> dict[str, Any]:
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
    review_records: list[dict[str, Any]] = []
    ignored_rejections: set[str] = set()
    reviews_dir = root / "metadata" / "reviews"
    if reviews_dir.is_dir():
        for path in sorted(reviews_dir.glob("*.json")):
            review = read_json(path)
            if not isinstance(review, Mapping):
                continue
            status = review.get("record_status")
            if ignore_exact_target_novelty_rejections:
                if status not in ("current_final", "final", "current_with_blocking_defects"):
                    continue
                reviewer = review.get("reviewer")
                if not isinstance(reviewer, Mapping) or reviewer.get("fresh_context") is not True:
                    raise BenchmarkToolError(
                        f"novelty override review {path.name} is not a fresh-context Codex review"
                    )
                identifiers = review.get("identifiers")
                snapshot = review.get("snapshot")
                review_manifest_sha256 = (
                    review.get("benchmark_manifest_sha256")
                    or (
                        identifiers.get("benchmark_manifest_sha256")
                        if isinstance(identifiers, Mapping)
                        else None
                    )
                    or (
                        snapshot.get("manifest_sha256")
                        if isinstance(snapshot, Mapping)
                        else None
                    )
                )
                if review_manifest_sha256 != current_manifest_sha256:
                    raise BenchmarkToolError(
                        f"novelty override review {path.name} cites a stale benchmark manifest"
                    )
            elif status != "current_final":
                continue
            task_reviews = review.get("task_reviews", review.get("tasks"))
            if not isinstance(task_reviews, list):
                continue
            covered_in_record: set[str] = set()
            for raw_task_review in task_reviews:
                if not isinstance(raw_task_review, Mapping):
                    continue
                task_id = raw_task_review.get("task_id")
                outcome = raw_task_review.get(
                    "review_outcome",
                    raw_task_review.get("outcome", raw_task_review.get("decision")),
                )
                if task_id not in coverage or task_id in covered_in_record:
                    continue
                accepted = isinstance(outcome, str) and outcome.lower().startswith("pass")
                if ignore_exact_target_novelty_rejections and not accepted:
                    normalized = outcome.lower() if isinstance(outcome, str) else ""
                    exact_target_collision = (
                        raw_task_review.get("exact_target_absent_from_mathlib") is False
                        or raw_task_review.get("exact_target_absent_from_numstability") is False
                    )
                    accepted = (
                        raw_task_review.get("source_faithful") is True
                        and ("exact_target" in normalized or exact_target_collision)
                        and ("fail" in normalized or "collision" in normalized)
                    )
                    if accepted:
                        ignored_rejections.add(str(task_id))
                if ignore_exact_target_novelty_rejections and raw_task_review.get(
                    "source_faithful"
                ) is not True:
                    accepted = False
                if accepted:
                    coverage[str(task_id)] += 1
                    covered_in_record.add(str(task_id))
            if covered_in_record:
                review_records.append(
                    {
                        "path": f"metadata/reviews/{path.name}",
                        "sha256": sha256_file(path),
                        "record_status": status,
                        "task_count": len(covered_in_record),
                    }
                )
    missing = [task_id for task_id, count in coverage.items() if count < 2]
    if missing:
        raise BenchmarkToolError(
            "measurement-ready phase requires two current final reviews for every task; missing: "
            + ", ".join(missing)
        )
    return {
        "enabled": ignore_exact_target_novelty_rejections,
        "scope": "exact-target novelty rejections only",
        "source_fidelity_required": True,
        "fresh_context_reviews_required": ignore_exact_target_novelty_rejections,
        "review_records": review_records,
        "ignored_rejection_task_ids": sorted(ignored_rejections),
        "note": (
            "The project owner directed that the fresh-context reviews be retained "
            "but their exact-target novelty rejections be ignored for this private, "
            "pre-publication measurement."
            if ignore_exact_target_novelty_rejections
            else "No review override was applied."
        ),
    }


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


def _token_control_record(limit_tokens: int) -> dict[str, Any]:
    """Return the cached-inclusive, outcome-dependent ledger contract."""

    return {
        "advisory_rollout_budget": {
            "enabled": True,
            "feature": "rollout_budget",
            "feature_row": "rollout_budget under development false",
            "limit_tokens": limit_tokens,
            "prefill_token_weight": 1,
            "role": "advisory_only",
            "sampling_token_weight": 1,
            "strict_config": True,
        },
        "all_descendant_threads_included": True,
        "cached_input_counted_once": True,
        "checked_before_submission_validation": True,
        "comparison": ">=",
        "concurrent_inflight_overshoot_possible": False,
        "control": "loopback_provider_response_admission_gate",
        "input_includes_cached": True,
        "limit_tokens": limit_tokens,
        "live_update_sequence": True,
        "live_cumulative": True,
        "measurement_exact_required": True,
        "measurement_source": TOKEN_MEASUREMENT_SOURCE,
        "notification": TOKEN_USAGE_NOTIFICATION,
        "one_response_overshoot_possible": True,
        "outer_runner_polling": True,
        "over_limit_pass_allowed": False,
        "response_ids_deduplicated": True,
        "root_completion_is_tree_barrier": False,
        "trusted_adapter_freezes_first_threshold": True,
        "trusted_adapter_latches_first_threshold": True,
        "trusted_usage_path_outside_workspace": True,
        "usage_scope": "rooted_attempt_thread_tree_completed_responses",
        "provider_gate_protocol": runner.PROVIDER_GATE_PROTOCOL,
        "provider_response_bound_tokens": 272000,
        "strict_admission_inequality": (
            "completed_tokens + (open_request_count + 1) * "
            "response_bound < token_limit"
        ),
        "crossing_response_release": runner.PROVIDER_GATE_CROSSING_RELEASE_POLICY,
        "crossing_response_actions_released": False,
        "provider_requests_quiescent_at_scored_endpoint": True,
        "tree_quiescence_distinct_from_provider_quiescence": True,
        "outcome_exactness": {
            "accepted_proof": {
                "required_evidence": "exact_authenticated_submission_boundary",
                "provider_gate_close_reason": "accepted_submission",
                "provider_requests_quiescent": True,
                "drain_complete": False,
                "measurement_exact": True,
                "submission_boundary_exact": True,
                "root_turn_active": True,
                "descendants_quiescent": True,
                "later_model_response_possible": False,
            },
            "token_limit": {
                "required_evidence": "sealed_sanitized_sole_inflight_crossing",
                "provider_gate_close_reason": "token_limit",
                "provider_requests_quiescent": True,
                "tree_quiescent": False,
                "drain_complete": False,
                "measurement_exact": True,
                "crossing_response_actions_released": False,
            },
            "scored_failure": {
                "required_evidence": "exact_natural_drain",
                "provider_gate_close_reason": "natural_end",
                "provider_requests_quiescent": True,
                "drain_complete": True,
                "measurement_exact": True,
                "tree_quiescent": True,
            },
            "unscorable_useful_work": {
                "trigger": (
                    "no_exact_authenticated_provider_gate_endpoint_for_outcome"
                ),
                "matrix_action": "abort_and_preserve_incident",
                "retry_allowed": False,
                "scored": False,
            },
        },
    }


def _sync_token_control(
    config: dict[str, Any], environment: dict[str, Any]
) -> None:
    limits = _object(config.get("limits"), "config limits")
    limit_tokens = limits.get("total_model_tokens")
    if (
        not isinstance(limit_tokens, int)
        or isinstance(limit_tokens, bool)
        or limit_tokens <= 0
    ):
        raise BenchmarkToolError(
            "config limits.total_model_tokens must be a positive integer"
        )
    config["token_control"] = _token_control_record(limit_tokens)
    environment["token_control"] = _token_control_record(limit_tokens)


def _sync_prompt_startup_timeout(
    config: dict[str, Any], environment: dict[str, Any]
) -> None:
    """Freeze adapter startup separately from prompt-to-proof measurement time."""

    if not float(DEFAULT_PROMPT_STARTUP_TIMEOUT_SECONDS).is_integer():
        raise BenchmarkToolError("prompt startup timeout must be an exact integer")
    timeout = int(DEFAULT_PROMPT_STARTUP_TIMEOUT_SECONDS)
    limits = _object(config.get("limits"), "config limits")
    runtime = _object(environment.setdefault("runtime", {}), "environment runtime")
    limits["prompt_startup_timeout_seconds"] = timeout
    runtime["prompt_startup_timeout_seconds"] = timeout


def _sync_post_submission_validation_reserve(
    config: dict[str, Any], environment: dict[str, Any]
) -> None:
    """Freeze the complete serial hidden-validation and process-closure tail."""

    if not float(DEFAULT_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS).is_integer():
        raise BenchmarkToolError(
            "post-submission validation reserve must be an exact integer"
        )
    reserve = int(DEFAULT_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS)
    limits = _object(config.get("limits"), "config limits")
    runtime = _object(environment.setdefault("runtime", {}), "environment runtime")
    limits["post_submission_validation_reserve_seconds"] = reserve
    runtime["post_submission_validation_reserve_seconds"] = reserve


def _sync_session_isolation(
    config: dict[str, Any], environment: dict[str, Any]
) -> None:
    record = _session_isolation_record()
    configured = _object(config.setdefault("isolation", {}), "config isolation")
    implemented = _object(
        environment.setdefault("isolation", {}), "environment isolation"
    )
    configured.update(record)
    implemented.update(record)


def _sync_ultra_orchestration(
    config: dict[str, Any], environment: dict[str, Any]
) -> None:
    """Freeze Ultra delegation and its projection-v6 accounting contract."""

    frozen = _object(config.get("frozen_environment"), "config frozen_environment")
    agent = _object(environment.setdefault("agent", {}), "environment agent")
    record = ultra_orchestration_record()
    frozen["model_version"] = FROZEN_MODEL_VERSION
    frozen["model_reasoning_effort"] = FROZEN_REASONING_EFFORT
    frozen["ultra_orchestration"] = record
    agent["model"] = FROZEN_MODEL_VERSION
    agent["reasoning_effort"] = FROZEN_REASONING_EFFORT
    agent["ultra_orchestration"] = record
    agent["disabled_capabilities"] = [
        "web and browser tools",
        "apps and plugins",
        "memory",
        "image generation",
    ]
    agent["fresh_mode"] = [
        "Codex app-server thread/start with ephemeral=false inside a unique temporary state directory",
        "history.persistence=none",
        "a new temporary CODEX_HOME for every attempt",
        "the temporary state directory is deleted on normal adapter exit and is never reused or mounted by another attempt",
        "user configuration and project rules ignored",
    ]


def _sync_provider_token_gate(
    root: Path, config: dict[str, Any], environment: dict[str, Any]
) -> None:
    """Freeze the gate source, model bound, and local TLS/DNS provenance."""

    record = provider_token_gate_environment_record(root)
    implementation = _object(
        record.get("implementation"), "provider-token-gate implementation"
    )
    static_configuration = _object(
        record.get("static_configuration"),
        "provider-token-gate static configuration",
    )
    upstream_response_contract = _object(
        static_configuration.get("upstream_response_contract"),
        "provider-token-gate upstream response contract",
    )
    if (
        type(record.get("schema_version")) is not int
        or record.get("schema_version") != 2
        or record.get("protocol") != "highambench-provider-token-gate-v6"
        or implementation.get("version") != "6"
        or canonical_document_digest(upstream_response_contract)
        != canonical_document_digest(
            runner.PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT
        )
    ):
        raise BenchmarkToolError(
            "snapshot refresh requires the exact provider-token-gate v6 freeze"
        )
    frozen = _object(config.get("frozen_environment"), "config frozen_environment")
    frozen["provider_token_gate_sha256"] = canonical_document_digest(record)
    environment["provider_token_gate"] = record


def _invalidate_live_canary_descriptors(
    config: dict[str, Any], environment: dict[str, Any]
) -> None:
    """Require fresh live attestations after every full snapshot refresh.

    A refresh may change any release-covered execution component.  Retaining a
    prior ``passed`` descriptor would let the launcher skip generation and only
    discover the stale component binding at its later verify-only gate.  The
    explicit promoter does not call ``refresh_snapshot``; it validates one
    attestation against the current snapshot, marks it passed, and performs only
    the non-semantic release/environment rehash needed to retain that evidence.
    """

    frozen = _object(config.get("frozen_environment"), "config frozen_environment")
    for key in ("ultra_orchestration_canary", "token_control_canary"):
        configured = frozen.get(key)
        implemented = environment.get(key)
        if isinstance(configured, dict):
            configured["status"] = "replacement_required"
        if isinstance(implemented, dict):
            implemented["status"] = "replacement_required"


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
    condition_l_prompt = root / CONDITION_L_PROMPT_RELATIVE
    if not condition_l_prompt.is_file() or condition_l_prompt.is_symlink():
        raise BenchmarkToolError(
            f"condition-L prompt must be a regular file: {condition_l_prompt}"
        )
    prompt_protocol = {
        "version": PROMPT_PROTOCOL_VERSION,
        "composition_order": [
            "common_prompt",
            "condition_L_supplement_if_condition_L",
            "task_context",
            "fixed_target",
        ],
        "common_prompt": {
            "path": "agent_prompt.md",
            "sha256": prompt_sha256,
            "bytes": (root / "agent_prompt.md").stat().st_size,
        },
        "condition_supplements": {
            "L": {
                "path": CONDITION_L_PROMPT_RELATIVE,
                "sha256": sha256_file(condition_l_prompt),
                "bytes": condition_l_prompt.stat().st_size,
            }
        },
        "N_receives_condition_supplement": False,
        "relevant_theorem_or_module_hints_supplied": False,
    }
    frozen["prompt_protocol"] = prompt_protocol
    agent["prompt_protocol"] = prompt_protocol

    isolation = environment.get("isolation")
    if isinstance(isolation, dict):
        component_paths = {
            "filesystem_adapter_sha256": "tools/codex_isolated.py",
            "provider_token_gate_sha256": "tools/provider_token_gate.py",
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


def refresh_snapshot(
    root: Path,
    *,
    phase: str,
    ignore_exact_target_novelty_rejections: bool = False,
) -> dict[str, Any]:
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
    if ignore_exact_target_novelty_rejections and not measurement_ready:
        raise BenchmarkToolError(
            "the exact-target novelty override is valid only for measurement-ready snapshots"
        )

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

    review_policy: dict[str, Any] | None = None
    if measurement_ready:
        review_policy = _measurement_readiness(
            benchmark_root,
            targets,
            ignore_exact_target_novelty_rejections=(
                ignore_exact_target_novelty_rejections
            ),
        )

    _set_task_phase(
        benchmark_root,
        papers,
        targets,
        measurement_ready=measurement_ready,
        limits=_object(config.get("limits"), "config limits"),
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
    _sync_prompt_startup_timeout(config, environment)
    _sync_post_submission_validation_reserve(config, environment)
    _sync_token_control(config, environment)
    _sync_session_isolation(config, environment)
    _sync_ultra_orchestration(config, environment)
    _sync_provider_token_gate(benchmark_root, config, environment)
    _invalidate_live_canary_descriptors(config, environment)
    config["configuration_status"] = (
        "corpus under construction; task metadata and snapshots may be regenerated"
        if phase == PHASE_CONSTRUCTION
        else "measurement-ready corpus snapshot; changes require a new snapshot"
    )
    if review_policy is None:
        config.pop("private_measurement_review_override", None)
    else:
        config["private_measurement_review_override"] = review_policy
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
    parser.add_argument(
        "--ignore-exact-target-novelty-rejections",
        action="store_true",
        help=(
            "retain two fresh-context reviews and require source fidelity, but "
            "ignore only exact-target novelty rejections for a private measurement"
        ),
    )
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    try:
        result = refresh_snapshot(
            args.benchmark_root,
            phase=args.phase,
            ignore_exact_target_novelty_rejections=(
                args.ignore_exact_target_novelty_rejections
            ),
        )
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
