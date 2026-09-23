"""Verify private, outcome-aware admission evidence for Pilot 27 tasks."""

from __future__ import annotations

from pathlib import Path

from common import BenchmarkError, load_json, sha256_file


ROOT = Path(__file__).resolve().parents[3]


def verify_admission(
    task_id: str, *, packet_path: Path, paper: Path,
    admission_path: Path, corpus_path: Path,
) -> dict:
    record = load_json(admission_path)
    corpus = load_json(corpus_path)
    if (record.get("schema_version") != "pilot-27-proof-canary-admission-1"
            or record.get("status") != "ADMITTED_DEVELOPMENT"
            or set(record.get("tasks", {})) != set(corpus.get("scheduled_order", []))):
        raise BenchmarkError("Pilot 27 admission/corpus identity is malformed")
    task = record["tasks"].get(task_id)
    if not isinstance(task, dict) or task.get("status") != "ADMITTED_DEVELOPMENT":
        raise BenchmarkError(f"Pilot 27 task is not admitted: {task_id}")
    prior_admission_path = ROOT / record["prior_admission_path"]
    if sha256_file(prior_admission_path) != record["prior_admission_sha256"]:
        raise BenchmarkError("prior admission record changed")
    prior = load_json(prior_admission_path)
    prior_task = prior.get("tasks", {}).get(task_id)
    if not isinstance(prior_task, dict):
        raise BenchmarkError(f"prior admission lacks {task_id}")
    if (prior_task.get("status") != "ADMITTED_DEVELOPMENT"
            or prior_task.get("source_packet_sha256") != sha256_file(packet_path)
            or prior_task.get("source_pdf_sha256") != sha256_file(paper)
            or prior_task.get("target_collision_review") != "NO_TARGET_RESULT_FOUND"):
        raise BenchmarkError(f"prior source/collision gate failed for {task_id}")
    # The earlier smoke compilation is provenance, not faithfulness evidence:
    # some of its private probes deliberately used `target : True`.
    smoke_path = Path(record["prior_skeleton_compile_path"])
    if sha256_file(smoke_path) != record["prior_skeleton_compile_sha256"]:
        raise BenchmarkError("prior private compilation record changed")
    smoke = load_json(smoke_path)
    if (smoke.get("status") != "PASS"
            or smoke.get("tasks", {}).get(task_id, {}).get("status")
            != "COMPILED_SORRY_STATEMENT_ONLY"):
        raise BenchmarkError(f"prior private compilation smoke failed for {task_id}")
    source_path = Path(prior_task["source_review_path"])
    if sha256_file(source_path) != prior_task["source_review_sha256"]:
        raise BenchmarkError(f"independent source review changed for {task_id}")
    source = load_json(source_path)
    reviewed_packet = source_path.parent / "workspace" / "source" / "packet.json"
    if (source.get("task_id") != task_id
            or source.get("assessment") != "faithful"
            or source.get("source_pdf_sha256") != sha256_file(paper)
            or load_json(reviewed_packet) != load_json(packet_path)):
        raise BenchmarkError(f"independent source review failed for {task_id}")

    campaign_root = Path(record["prior_campaign_path"])
    campaign_path = campaign_root / "campaign.json"
    if sha256_file(campaign_path) != record["prior_campaign_sha256"]:
        raise BenchmarkError("prior campaign journal changed")
    campaign = load_json(campaign_path)
    if campaign.get("status") != "COMPLETE":
        raise BenchmarkError("prior campaign was not complete")
    matches = [entry for entry in campaign.get("pairs", [])
               if entry.get("task_id") == task_id]
    if len(matches) != 1:
        raise BenchmarkError(f"prior campaign has no unique pair for {task_id}")
    entry = matches[0]
    pair_path = campaign_root / task_id / "pair-report.json"
    if (sha256_file(pair_path) != task["prior_pair_report_sha256"]
            or entry.get("pair_report_sha256") != task["prior_pair_report_sha256"]):
        raise BenchmarkError(f"prior pair report changed for {task_id}")
    pair = load_json(pair_path)
    condition = pair.get("conditions", {}).get("R1", {})
    if (pair.get("status") != "AUDITED_FAITHFUL_PAIR"
            or condition.get("result_status") != "ACCEPTED_FAITHFUL"
            or condition.get("candidate_sha256")
            != task["prior_faithful_l_candidate_sha256"]):
        raise BenchmarkError(f"prior L statement was not audited faithful: {task_id}")
    candidate_path = Path(condition["candidate"]["path"])
    if sha256_file(candidate_path) != task["prior_faithful_l_candidate_sha256"]:
        raise BenchmarkError(f"private faithful skeleton changed for {task_id}")
    final_attempt = condition["attempts"][-1]
    if (final_attempt.get("status") != "ACCEPTED_FAITHFUL"
            or final_attempt.get("validation_pass") is not True
            or final_attempt.get("audit", {}).get("accepted") is not True):
        raise BenchmarkError(f"private candidate gate failed for {task_id}")
    reached = set(entry.get("treatment_uptake", {}).get("direct_reached", []))
    required = set(task.get("required_target_dependency", []))
    if (not required or not required.issubset(reached)
            or task.get("required_fp_model") is not True
            or "NumStability.FPModel" not in reached):
        raise BenchmarkError(f"private candidate lacks direct FPModel/algorithm use: {task_id}")
    return task
