#!/usr/bin/env python3
"""Load the newest hash-verified faithfulness decision for one task."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path
from typing import Any


TASK_ID_RE = re.compile(r"^P\d{2}-T[123]$")
AUDIT_ID_RE = re.compile(r"^audit_(\d+)$")


class AuditContextError(RuntimeError):
    pass


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def read_json(data: bytes, label: str) -> dict[str, Any]:
    try:
        value = json.loads(data)
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise AuditContextError(f"{label} is not valid UTF-8 JSON: {error}") from error
    if not isinstance(value, dict):
        raise AuditContextError(f"{label} must contain a JSON object")
    return value


def repository_root(explicit: Path | None) -> Path:
    if explicit is not None:
        root = explicit.expanduser().resolve()
    else:
        result = subprocess.run(
            ["git", "rev-parse", "--show-toplevel"],
            check=False,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        if result.returncode != 0:
            raise AuditContextError(
                "not inside a Git repository; pass --repo-root explicitly"
            )
        root = Path(result.stdout.strip()).resolve()
    if not (root / ".git").exists():
        raise AuditContextError(f"repository root has no .git directory: {root}")
    return root


def safe_path(root: Path, relative: str) -> Path:
    path = (root / relative).resolve()
    if path != root and root not in path.parents:
        raise AuditContextError(f"path escapes repository root: {relative}")
    return path


def git_show(root: Path, commit: str, relative: str) -> bytes:
    result = subprocess.run(
        ["git", "-C", str(root), "show", f"{commit}:{relative}"],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if result.returncode != 0:
        detail = result.stderr.decode("utf-8", errors="replace").strip()
        raise AuditContextError(
            f"cannot recover {relative} from commit {commit}: {detail}"
        )
    return result.stdout


def load_bound_artifact(
    root: Path,
    relative: str,
    expected_sha256: str,
    commit: str,
) -> tuple[bytes, str]:
    current = safe_path(root, relative)
    if current.is_file():
        data = current.read_bytes()
        if sha256(data) == expected_sha256:
            return data, "working-tree"

    data = git_show(root, commit, relative)
    actual = sha256(data)
    if actual != expected_sha256:
        raise AuditContextError(
            f"{relative} has SHA-256 {actual}, expected {expected_sha256}"
        )
    return data, f"git:{commit}"


def audit_sort_key(path: Path) -> int:
    match = AUDIT_ID_RE.fullmatch(path.name)
    return int(match.group(1)) if match else -1


def history_entry(
    root: Path, task_id: str, requested_audit: str | None
) -> tuple[Path, dict[str, Any], dict[str, Any], dict[str, Any]]:
    history = root / "paper_bencmark" / "faithfulness_audit" / "history"
    if requested_audit is not None:
        if AUDIT_ID_RE.fullmatch(requested_audit) is None:
            raise AuditContextError("audit ID must have the form audit_NNN")
        candidates = [history / requested_audit]
    else:
        candidates = sorted(
            (
                path
                for path in history.glob("audit_*")
                if path.is_dir() and AUDIT_ID_RE.fullmatch(path.name)
            ),
            key=audit_sort_key,
            reverse=True,
        )

    if not candidates:
        raise AuditContextError(f"no audit history entries found under {history}")

    for directory in candidates:
        manifest_path = directory / "manifest.json"
        if not manifest_path.is_file():
            raise AuditContextError(f"missing audit manifest: {manifest_path}")
        manifest = read_json(manifest_path.read_bytes(), str(manifest_path))
        if manifest.get("status") != "completed":
            if requested_audit is not None:
                raise AuditContextError(f"{directory.name} is not completed")
            continue

        files = manifest.get("files")
        if not isinstance(files, list):
            raise AuditContextError(f"{manifest_path} has no files list")
        result_records = [
            item
            for item in files
            if isinstance(item, dict)
            and isinstance(item.get("path"), str)
            and item["path"].endswith("/results.json")
        ]
        if len(result_records) != 1:
            raise AuditContextError(
                f"{manifest_path} must bind exactly one results.json"
            )
        result_record = result_records[0]
        results_path = safe_path(root, result_record["path"])
        results_data = results_path.read_bytes()
        expected_results_hash = result_record.get("sha256")
        if not isinstance(expected_results_hash, str):
            raise AuditContextError(f"{manifest_path} omits the results SHA-256")
        actual_results_hash = sha256(results_data)
        if actual_results_hash != expected_results_hash:
            raise AuditContextError(
                f"{results_path} has SHA-256 {actual_results_hash}, "
                f"expected {expected_results_hash}"
            )
        results = read_json(results_data, str(results_path))
        tasks = results.get("tasks")
        if not isinstance(tasks, list):
            raise AuditContextError(f"{results_path} has no tasks list")
        matches = [
            item
            for item in tasks
            if isinstance(item, dict) and item.get("task_id") == task_id
        ]
        if len(matches) == 1:
            return directory, manifest, results, matches[0]
        if len(matches) > 1:
            raise AuditContextError(
                f"{results_path} contains duplicate entries for {task_id}"
            )
        if requested_audit is not None:
            raise AuditContextError(f"{requested_audit} does not contain {task_id}")

    raise AuditContextError(f"no completed audit history entry contains {task_id}")


def file_state(root: Path, record: dict[str, Any]) -> dict[str, Any]:
    relative = record.get("path")
    expected = record.get("sha256")
    if not isinstance(relative, str) or not isinstance(expected, str):
        raise AuditContextError("artifact record must contain path and sha256")
    path = safe_path(root, relative)
    if not path.is_file():
        return {
            "path": relative,
            "expected_sha256": expected,
            "actual_sha256": None,
            "matches_audit": False,
        }
    actual = sha256(path.read_bytes())
    return {
        "path": relative,
        "expected_sha256": expected,
        "actual_sha256": actual,
        "matches_audit": actual == expected,
    }


def selected_task_result(task: dict[str, Any]) -> dict[str, Any]:
    """Return the validated result from a multi-pass history entry."""
    result = task.get("result")
    if not isinstance(result, dict):
        return task

    validation = task.get("validation")
    if not isinstance(validation, dict) or validation.get("status") != "validated":
        raise AuditContextError("task result is present but is not validated")
    return result


def build_context(
    root: Path, task_id: str, requested_audit: str | None
) -> dict[str, Any]:
    directory, manifest, results, task = history_entry(
        root, task_id, requested_audit
    )
    result = selected_task_result(task)
    snapshot = results.get("repository_snapshot")
    if isinstance(snapshot, dict) and isinstance(snapshot.get("commit"), str):
        commit = snapshot["commit"]
        snapshot_source = "repository_snapshot"
    else:
        commit = task.get("evidence_commit")
        if not isinstance(commit, str):
            raise AuditContextError(
                f"{directory.name} has neither a repository snapshot commit "
                f"nor an evidence commit for {task_id}"
            )
        snapshot = {"commit": commit, "scope": "task-evidence"}
        snapshot_source = "task_evidence_commit"

    artifacts = result.get("artifacts")
    if not isinstance(artifacts, dict):
        raise AuditContextError(f"{task_id} has no artifact index")
    decision_record = artifacts.get("decision")
    report_record = artifacts.get("report")
    if not isinstance(decision_record, dict) or not isinstance(report_record, dict):
        raise AuditContextError(f"{task_id} has incomplete decision/report records")

    decision_data, decision_source = load_bound_artifact(
        root,
        decision_record["path"],
        decision_record["sha256"],
        commit,
    )
    report_data, report_source = load_bound_artifact(
        root,
        report_record["path"],
        report_record["sha256"],
        commit,
    )
    decision = read_json(decision_data, decision_record["path"])
    if decision.get("task_id") != task_id:
        raise AuditContextError("decision task ID disagrees with the requested task")
    for field in ("classification", "accepted", "adjudicated"):
        if decision.get(field) != result.get(field):
            raise AuditContextError(
                f"decision field {field} disagrees with the history index"
            )

    target = result.get("target")
    paper = result.get("paper")
    if not isinstance(target, dict) or not isinstance(paper, dict):
        raise AuditContextError(f"{task_id} has incomplete target/paper records")
    target_state = file_state(root, target)
    paper_state = file_state(root, paper)

    warnings: list[str] = []
    if bool(result.get("accepted")):
        warnings.append(
            "The latest audit accepted this task; do not repair it without explicit direction."
        )
    if not target_state["matches_audit"]:
        warnings.append(
            "The current target differs from the audited target; inspect intervening changes."
        )
    if not paper_state["matches_audit"]:
        warnings.append(
            "The current reference PDF differs from the audited PDF; stop before repair."
        )
    if decision_source != "working-tree" or report_source != "working-tree":
        warnings.append(
            "Historical decision material was recovered from the pinned Git snapshot."
        )

    return {
        "schema_version": "highambench-builder-audit-context-1",
        "task_id": task_id,
        "audit": {
            "audit_id": manifest.get("audit_id", directory.name),
            "history_directory": str(directory.relative_to(root)),
            "recorded_at_utc": manifest.get("recorded_at_utc"),
            "repository_snapshot": snapshot,
            "snapshot_source": snapshot_source,
            "protocol_versions": results.get("protocol_versions"),
        },
        "verdict": {
            "classification": result.get("classification"),
            "accepted": result.get("accepted"),
            "adjudicated": result.get("adjudicated"),
            "implications": result.get("implications"),
        },
        "audited_inputs": {
            "target": target,
            "paper": paper,
            "decision": decision_record,
            "report": report_record,
        },
        "current_state": {
            "target": target_state,
            "paper": paper_state,
        },
        "artifact_sources": {
            "decision": decision_source,
            "report": report_source,
        },
        "decision": decision,
        "report_markdown": report_data.decode("utf-8"),
        "warnings": warnings,
    }


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Load the newest hash-verified audit context for one task."
    )
    parser.add_argument("task_id", help="task ID such as P11-T1")
    parser.add_argument(
        "--repo-root",
        type=Path,
        help="lean-fp-analysis repository root; defaults to the current Git root",
    )
    parser.add_argument(
        "--audit-id",
        help="select a specific audit_NNN instead of the newest matching audit",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if TASK_ID_RE.fullmatch(args.task_id) is None:
        print(
            "audit-context error: task ID must have the form PNN-T1, PNN-T2, or PNN-T3",
            file=sys.stderr,
        )
        return 2
    try:
        root = repository_root(args.repo_root)
        context = build_context(root, args.task_id, args.audit_id)
    except (AuditContextError, OSError, KeyError) as error:
        print(f"audit-context error: {error}", file=sys.stderr)
        return 1
    json.dump(context, sys.stdout, indent=2, ensure_ascii=False)
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
