#!/usr/bin/env python3
"""Fresh, off-benchmark, source-only review of a Pilot-20 development packet."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import shutil
import sys

from codex_driver import CodexDriver
from common import BenchmarkError, load_json, sha256_file, utc_now, write_bytes_atomic, write_json_atomic
from deployment import load_deployment
from design20_matched import CORPUS, ROOT
from design18_source_contract import MODEL, EFFORT, PROMPT


def run_one(*, task_id: str, deployment_path: Path, output_root: Path) -> dict:
    corpus = load_json(CORPUS)
    if task_id not in corpus["scheduled_order"]:
        raise BenchmarkError("task is outside the Pilot-20 development corpus")
    packet_path = ROOT / "packets" / f"{task_id}.json"
    packet = load_json(packet_path)
    if packet.get("task_id") != task_id:
        raise BenchmarkError("source packet task ID mismatch")
    deployment = load_deployment(deployment_path)
    pdf = ROOT / "sources" / packet["paper_pdf"]["path_basename"]
    if not pdf.is_file():
        pdf = deployment.pdf_root / packet["paper_pdf"]["path_basename"]
    if sha256_file(pdf) != packet["paper_pdf"]["sha256"]:
        raise BenchmarkError("source PDF changed")
    if output_root.exists() or output_root.is_symlink():
        raise BenchmarkError("source-contract output already exists")
    output_root.mkdir(parents=True, mode=0o700)
    workspace = output_root / "workspace"
    source = workspace / "source"
    source.mkdir(parents=True, mode=0o700)
    shutil.copyfile(pdf, source / "paper.pdf")
    (source / "paper.pdf").chmod(0o400)
    write_bytes_atomic(source / "packet.json", json.dumps(packet, indent=2, sort_keys=True).encode(),
                       mode=0o400)
    driver = CodexDriver(
        codex_binary=deployment.codex_binary,
        code_mode_host_sha256=deployment.code_mode_host_sha256,
        model=MODEL, reasoning_effort=EFFORT, state_root=None,
        auth_file=deployment.auth_file, bwrap_binary=deployment.bwrap_binary,
        offline_shell=deployment.offline_shell,
        toolchain_root=deployment.toolchain_root,
        packages_root=deployment.packages_root,
        workspace_writable=False,
        protected_workspace_paths=[source],
    )
    try:
        turn = driver.run_turn(
            prompt=PROMPT + f"\nSelected task ID: {task_id}\n",
            workspace=workspace,
            artifact_dir=output_root / "reviewer",
            timeout_seconds=7200,
        )
    finally:
        driver.close(artifact_dir=output_root / "session-close")
    try:
        parsed = json.loads(turn.final_message)
    except (TypeError, json.JSONDecodeError):
        parsed = None
    status = ("SOURCE_CONTRACT_REVIEWED_NOT_ADMITTED"
              if turn.exit_code == 0 and not turn.timed_out and turn.usage_complete
              and isinstance(parsed, dict) and parsed.get("task_id") == task_id
              else "REVIEWER_OUTPUT_INCIDENT")
    record = {
        "schema_version": "pilot-20-source-contract-review-1",
        "task_id": task_id, "status": status,
        "reviewer_model": MODEL, "reasoning_effort": EFFORT,
        "source_pdf_sha256": sha256_file(source / "paper.pdf"),
        "draft_packet_sha256": sha256_file(source / "packet.json"),
        "turn_artifact_sha256": sha256_file(output_root / "reviewer" / "turn.json"),
        "turn_usage": turn.usage, "usage_complete": turn.usage_complete,
        "turn_wall_seconds": turn.wall_seconds,
        "assessment": parsed.get("assessment") if isinstance(parsed, dict) else None,
        "parsed_review": parsed, "created_at_utc": utc_now(),
    }
    write_json_atomic(output_root / "source-contract-review.json", record, mode=0o400)
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--task-id", required=True)
    parser.add_argument("--deployment", required=True, type=Path)
    parser.add_argument("--output-root", required=True, type=Path)
    args = parser.parse_args()
    record = run_one(task_id=args.task_id, deployment_path=args.deployment,
                     output_root=args.output_root)
    print(json.dumps({key: record[key] for key in
                      ("task_id", "status", "assessment", "turn_usage", "turn_wall_seconds")},
                     sort_keys=True))
    return 0 if record["status"] == "SOURCE_CONTRACT_REVIEWED_NOT_ADMITTED" else 2


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError) as error:
        print(f"Pilot-20 source-contract error: {error}", file=sys.stderr)
        raise SystemExit(2)
