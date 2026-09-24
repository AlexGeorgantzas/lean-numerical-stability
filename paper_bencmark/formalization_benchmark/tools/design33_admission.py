"""Fail-closed admission for Pilot 33's outcome-aware high-overlap corpus.

Private source-faithfulness candidates are admission evidence, never contestant
inputs. Historical Pilot 29 tasks retain their earlier independently verified
source and collision gates and are explicitly labeled outcome-aware.
"""

from __future__ import annotations

from pathlib import Path

from common import BenchmarkError, load_json, sha256_file


SCHEMA = "pilot-33-high-overlap-admission-1"


def _checked_json(path: Path, digest: str, label: str) -> dict:
    if not path.is_absolute() or not path.is_file() or path.is_symlink():
        raise BenchmarkError(f"{label} path is missing or unsafe")
    if sha256_file(path) != digest:
        raise BenchmarkError(f"{label} hash changed")
    return load_json(path)


def _new_private(task_id: str, task: dict) -> None:
    candidate = Path(task["private_candidate_path"])
    candidate_sha = task["private_candidate_sha256"]
    if (not candidate.is_absolute() or not candidate.is_file()
            or candidate.is_symlink() or sha256_file(candidate) != candidate_sha):
        raise BenchmarkError(f"private candidate changed for {task_id}")
    result_path = Path(task["private_audit_result_path"])
    result = _checked_json(result_path, task["private_audit_result_sha256"],
                           "private candidate audit")
    if (result.get("task_id") != task_id
            or result.get("candidate_sha256") != candidate_sha
            or result.get("source_packet_sha256") != task["source_packet_sha256"]
            or result.get("paper_sha256") != task["source_pdf_sha256"]
            or result.get("source_contract")
            != "statement-only-single-target-sorry"
            or result.get("condition_blind") is not True
            or result.get("attempt_blind") is not True
            or result.get("decision", {}).get("accepted") is not True):
        raise BenchmarkError(f"private full audit failed for {task_id}")
    manifest_path = result_path.parent / "preparation" / "private_semantic_manifest.json"
    manifest = _checked_json(manifest_path, result["private_manifest_sha256"],
                             "private semantic manifest")
    names = {dependency.get("name") for dependency in
             manifest.get("raw_semantic_report", {}).get("dependencies", [])}
    required = set(task["required_direct_names"])
    if (manifest.get("candidate", {}).get("sha256") != candidate_sha
            or not required or not required.issubset(names)):
        raise BenchmarkError(f"private candidate lacks direct use for {task_id}")


def _historical(task_id: str, task: dict, packet_path: Path, paper: Path) -> None:
    from design29_admission import verify_admission as verify_pilot29

    prior_admission = Path(task["prior_admission_path"])
    prior_corpus = Path(task["prior_corpus_path"])
    _checked_json(prior_admission, task["prior_admission_sha256"],
                  "prior admission")
    _checked_json(prior_corpus, task["prior_corpus_sha256"], "prior corpus")
    prior_task = verify_pilot29(
        task_id, packet_path=packet_path, paper=paper,
        admission_path=prior_admission, corpus_path=prior_corpus,
    )
    if prior_task.get("required_direct_names") != task["required_direct_names"]:
        raise BenchmarkError(f"prior direct-use gate differs for {task_id}")


def verify_admission(task_id: str, *, packet_path: Path, paper: Path,
                     admission_path: Path, corpus_path: Path) -> dict:
    record = load_json(admission_path)
    corpus = load_json(corpus_path)
    tasks = record.get("tasks", {})
    if (record.get("schema_version") != SCHEMA
            or record.get("status") != "ADMITTED_DEVELOPMENT"
            or corpus.get("schema_version") != "pilot-33-high-overlap-corpus-1"
            or corpus.get("pilot_identity") != "pilot33-high-overlap-proof-development"
            or len(corpus.get("scheduled_order", [])) != 15
            or not isinstance(tasks, dict)
            or set(tasks) != set(corpus.get("scheduled_order", []))):
        raise BenchmarkError("Pilot 33 admission/corpus identity is malformed")
    task = tasks.get(task_id)
    hard = set(corpus.get("predeclared_hard_tasks", []))
    if (not hard.issubset(set(corpus.get("scheduled_order", [])))
            or (task_id in hard) != (isinstance(task, dict)
                                       and task.get("difficulty") == "hard")):
        raise BenchmarkError(f"Pilot 33 difficulty label changed for {task_id}")
    if (not isinstance(task, dict)
            or task.get("status") != "ADMITTED_DEVELOPMENT"
            or task.get("difficulty") not in {"ordinary", "hard"}
            or task.get("source_cluster") not in
                {"CAST08", "P14", "HI21", "RUMP12", "H20"}
            or task.get("model_stratum") not in
                {"algorithm_error", "finite_format", "error_interface"}
            or task.get("source_packet_sha256") != sha256_file(packet_path)
            or task.get("source_pdf_sha256") != sha256_file(paper)
            or task.get("target_collision_review") != "NO_TARGET_RESULT_FOUND"
            or len(task.get("collision_review_note", "")) < 20
            or not task.get("required_direct_names")):
        raise BenchmarkError(f"Pilot 33 source/collision gate failed for {task_id}")
    if task.get("evidence_kind") == "new_private_audit":
        _new_private(task_id, task)
    elif task.get("evidence_kind") == "outcome_aware_pilot29":
        _historical(task_id, task, packet_path, paper)
    else:
        raise BenchmarkError(f"unknown admission evidence for {task_id}")
    return task
