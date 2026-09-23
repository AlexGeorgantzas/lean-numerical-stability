"""Fail-closed admission for an outcome-aware proof-development corpus.

Earlier faithful contestant statements are private feasibility evidence only.
They are never copied into either new contestant workspace. A newly screened
task instead needs a separate full candidate audit before admission.
"""

from __future__ import annotations

from pathlib import Path

from common import BenchmarkError, load_json, sha256_file


ROOT = Path(__file__).resolve().parents[3]
SCHEMA = "pilot-29-proof-development-admission-1"
STRATA = {"algorithm_error", "finite_format", "error_interface"}


def _unchanged_json(path: Path, digest: str, label: str) -> dict:
    if not path.is_absolute() or not path.is_file() or path.is_symlink():
        raise BenchmarkError(f"{label} path is missing or unsafe")
    if sha256_file(path) != digest:
        raise BenchmarkError(f"{label} hash changed")
    return load_json(path)


def _verify_source_review(task_id: str, task: dict, packet_path: Path,
                          paper: Path) -> None:
    review_path = Path(task["source_review_path"])
    review = _unchanged_json(
        review_path, task["source_review_sha256"], "source review"
    )
    reviewed_packet = review_path.parent / "workspace" / "source" / "packet.json"
    if (review.get("task_id") != task_id
            or review.get("status") != "SOURCE_CONTRACT_REVIEWED_NOT_ADMITTED"
            or review.get("assessment") != "faithful"
            or review.get("reviewer_model") != "gpt-6-astra"
            or review.get("reasoning_effort") != "high"
            or review.get("source_pdf_sha256") != sha256_file(paper)
            or load_json(reviewed_packet) != load_json(packet_path)):
        raise BenchmarkError(f"source-contract review failed for {task_id}")


def _verify_prior_pair(task_id: str, task: dict, record: dict,
                       prior_admission: dict, prior_campaign: dict) -> None:
    prior_task = prior_admission.get("tasks", {}).get(task_id)
    if (not isinstance(prior_task, dict)
            or prior_task.get("status") != "ADMITTED_DEVELOPMENT"
            or prior_task.get("target_collision_review")
            != "NO_TARGET_RESULT_FOUND"):
        raise BenchmarkError(f"prior admission lacks {task_id}")
    if (prior_task.get("source_packet_sha256") != task["source_packet_sha256"]
            or prior_task.get("source_pdf_sha256") != task["source_pdf_sha256"]
            or prior_task.get("source_review_path") != task["source_review_path"]
            or prior_task.get("source_review_sha256")
            != task["source_review_sha256"]):
        raise BenchmarkError(f"prior source evidence differs for {task_id}")
    campaign_root = Path(record["prior_campaign_path"])
    entries = [entry for entry in prior_campaign.get("pairs", [])
               if entry.get("task_id") == task_id]
    if len(entries) != 1:
        raise BenchmarkError(f"prior campaign has no unique pair for {task_id}")
    pair_path = campaign_root / task_id / "pair-report.json"
    pair = _unchanged_json(pair_path, task["prior_pair_report_sha256"],
                           "prior pair report")
    if (entries[0].get("pair_report_sha256")
            != task["prior_pair_report_sha256"]
            or pair.get("status") != "AUDITED_FAITHFUL_PAIR"):
        raise BenchmarkError(f"prior faithful pair changed for {task_id}")
    l_condition = pair.get("conditions", {}).get("R1", {})
    if (l_condition.get("result_status") != "ACCEPTED_FAITHFUL"
            or l_condition.get("candidate_sha256")
            != task["prior_faithful_l_candidate_sha256"]):
        raise BenchmarkError(f"prior L statement not faithful for {task_id}")
    candidate_path = Path(l_condition["candidate"]["path"])
    if (not candidate_path.is_absolute() or not candidate_path.is_file()
            or candidate_path.is_symlink()
            or sha256_file(candidate_path)
            != task["prior_faithful_l_candidate_sha256"]):
        raise BenchmarkError(f"prior L statement changed for {task_id}")
    final_attempt = l_condition["attempts"][-1]
    if (final_attempt.get("status") != "ACCEPTED_FAITHFUL"
            or final_attempt.get("validation_pass") is not True
            or final_attempt.get("audit", {}).get("accepted") is not True):
        raise BenchmarkError(f"prior candidate audit failed for {task_id}")
    reached = set(entries[0].get("treatment_uptake", {}).get("direct_reached", []))
    required = set(task["required_direct_names"])
    if not required or not required.issubset(reached):
        raise BenchmarkError(f"prior candidate lacks direct use for {task_id}")


def _verify_new_private(task_id: str, task: dict) -> None:
    candidate_path = Path(task["private_candidate_path"])
    candidate_sha = task["private_candidate_sha256"]
    if (not candidate_path.is_absolute() or not candidate_path.is_file()
            or candidate_path.is_symlink()
            or sha256_file(candidate_path) != candidate_sha):
        raise BenchmarkError(f"private candidate changed for {task_id}")
    result_path = Path(task["private_audit_result_path"])
    result = _unchanged_json(result_path, task["private_audit_result_sha256"],
                             "private full audit")
    if (result.get("task_id") != task_id
            or result.get("candidate_sha256") != candidate_sha
            or result.get("source_contract")
            != "statement-only-single-target-sorry"
            or result.get("condition_blind") is not True
            or result.get("attempt_blind") is not True
            or result.get("decision", {}).get("accepted") is not True):
        raise BenchmarkError(f"private full audit failed for {task_id}")
    manifest_path = result_path.parent / "preparation" / "private_semantic_manifest.json"
    manifest = _unchanged_json(manifest_path,
        result["private_manifest_sha256"], "private semantic manifest")
    names = {dependency.get("name") for dependency in
             manifest.get("raw_semantic_report", {}).get("dependencies", [])}
    required = set(task["required_direct_names"])
    if (manifest.get("candidate", {}).get("sha256") != candidate_sha
            or not required or not required.issubset(names)):
        raise BenchmarkError(f"private candidate lacks direct use for {task_id}")


def verify_admission(task_id: str, *, packet_path: Path, paper: Path,
                     admission_path: Path, corpus_path: Path) -> dict:
    record = load_json(admission_path)
    corpus = load_json(corpus_path)
    tasks = record.get("tasks", {})
    if (record.get("schema_version") != SCHEMA
            or record.get("status") != "ADMITTED_DEVELOPMENT"
            or not isinstance(tasks, dict)
            or set(tasks) != set(corpus.get("scheduled_order", []))):
        raise BenchmarkError("Pilot 29 admission/corpus identity is malformed")
    task = tasks.get(task_id)
    if (not isinstance(task, dict)
            or task.get("status") != "ADMITTED_DEVELOPMENT"
            or task.get("model_stratum") not in STRATA
            or task.get("source_packet_sha256") != sha256_file(packet_path)
            or task.get("source_pdf_sha256") != sha256_file(paper)
            or task.get("target_collision_review")
            != "NO_TARGET_RESULT_FOUND"
            or not isinstance(task.get("collision_review_note"), str)
            or len(task["collision_review_note"]) < 20):
        raise BenchmarkError(f"Pilot 29 source/collision gate failed for {task_id}")
    _verify_source_review(task_id, task, packet_path, paper)
    prior_admission_path = ROOT / record["prior_admission_path"]
    prior_admission = _unchanged_json(
        prior_admission_path, record["prior_admission_sha256"],
        "prior admission",
    )
    prior_campaign_path = Path(record["prior_campaign_path"]) / "campaign.json"
    prior_campaign = _unchanged_json(
        prior_campaign_path, record["prior_campaign_sha256"],
        "prior campaign",
    )
    if prior_campaign.get("status") != "COMPLETE":
        raise BenchmarkError("prior campaign was not complete")
    if task.get("evidence_kind") == "prior_faithful_pair":
        _verify_prior_pair(task_id, task, record, prior_admission, prior_campaign)
    elif task.get("evidence_kind") == "new_private_audit":
        _verify_new_private(task_id, task)
    else:
        raise BenchmarkError(f"unknown admission evidence kind for {task_id}")
    return task
