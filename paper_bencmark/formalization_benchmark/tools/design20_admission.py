"""Fail-closed, hash-verified admission gate for development canaries."""

from __future__ import annotations

from pathlib import Path

from common import BenchmarkError, load_json, sha256_file


ROOT = Path(__file__).resolve().parents[1] / "design20"
ADMISSION = ROOT / "ADMISSION_3.json"


def verify_admission(task_id: str, *, packet_path: Path, paper: Path,
                     admission_path: Path | None = None,
                     corpus_path: Path | None = None) -> dict:
    record = load_json(admission_path or ADMISSION)
    if record.get("schema_version") != "pilot-20-development-admission-1":
        raise BenchmarkError("Pilot-20 development admission is missing or malformed")
    tasks = record.get("tasks")
    if not isinstance(tasks, dict) or task_id not in tasks:
        raise BenchmarkError(f"no Pilot-20 admission for {task_id}")
    task = tasks[task_id]
    if (task.get("status") != "ADMITTED_DEVELOPMENT"
            or task.get("source_packet_sha256") != sha256_file(packet_path)
            or task.get("source_pdf_sha256") != sha256_file(paper)
            or task.get("target_collision_review") != "NO_TARGET_RESULT_FOUND"):
        raise BenchmarkError(f"Pilot-20 source/collision admission failed for {task_id}")
    source_path = Path(task["source_review_path"])
    if not source_path.is_absolute() or sha256_file(source_path) != task["source_review_sha256"]:
        raise BenchmarkError(f"Pilot-20 source review changed for {task_id}")
    source = load_json(source_path)
    if (source.get("task_id") != task_id
            or source.get("status") != "SOURCE_CONTRACT_REVIEWED_NOT_ADMITTED"
            or source.get("assessment") != "faithful"
            or source.get("source_pdf_sha256") != task["source_pdf_sha256"]
            or source.get("reviewer_model") != "gpt-6-astra"
            or source.get("reasoning_effort") != "high"):
        raise BenchmarkError(f"Pilot-20 independent source review did not pass for {task_id}")
    reviewed_packet = source_path.parent / "workspace" / "source" / "packet.json"
    if load_json(reviewed_packet) != load_json(packet_path):
        raise BenchmarkError(f"Pilot-20 reviewer saw a different packet for {task_id}")
    preflight_path = Path(record["static_preflight_path"])
    if (not preflight_path.is_absolute()
            or sha256_file(preflight_path) != record["static_preflight_sha256"]):
        raise BenchmarkError("Pilot-20 static preflight changed")
    preflight = load_json(preflight_path)
    if (preflight.get("status") != "PASS"
            or preflight.get("corpus_sha256") != sha256_file(
                corpus_path or ROOT / "CORPUS_3.json")):
        raise BenchmarkError("Pilot-20 static preflight did not pass")
    try:
        checks = preflight["tasks"][task_id]
        if checks["R0"]["status"] != "PASS" or checks["R1"]["status"] != "PASS":
            raise KeyError("condition failed")
        if not set(task["direct_component_names"]).issubset(
                set(checks["R1"]["selected_roots"])):
            raise KeyError("direct library components not surfaced")
    except (KeyError, TypeError) as error:
        raise BenchmarkError(f"Pilot-20 preflight component gate failed for {task_id}") from error
    skeleton_path = Path(task["private_skeleton_path"])
    if not skeleton_path.is_absolute() or sha256_file(skeleton_path) != task["private_skeleton_sha256"]:
        raise BenchmarkError(f"Pilot-20 private compatibility skeleton changed for {task_id}")
    compile_path = Path(record["private_skeleton_compile_path"])
    if (not compile_path.is_absolute()
            or sha256_file(compile_path) != record["private_skeleton_compile_sha256"]):
        raise BenchmarkError("Pilot-20 private skeleton compilation record changed")
    compilation = load_json(compile_path)
    try:
        compiled = compilation["tasks"][task_id]
        if (compilation["status"] != "PASS"
                or compiled["status"] != "COMPILED_SORRY_STATEMENT_ONLY"
                or compiled["private_source_sha256"] != task["private_skeleton_sha256"]
                or compiled["compile"]["pass"] is not True):
            raise KeyError("private statement compilation did not pass")
    except (KeyError, TypeError) as error:
        raise BenchmarkError(f"Pilot-20 private statement compilation failed for {task_id}") from error
    return task
