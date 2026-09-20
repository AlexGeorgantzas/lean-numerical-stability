from __future__ import annotations

import fcntl
import json
import math
import os
import secrets
import shutil
import subprocess
import time
from contextlib import contextmanager
from pathlib import Path
from typing import Any, Iterator, Mapping

from audit_controller import AuditController, audit_evidence_manifest
from codex_driver import CodexDriver, ProviderCapabilityError, command_cgroup_snapshot
from common import (
    BenchmarkError,
    assert_no_credentials_in_bytes,
    assert_no_credentials_in_tree,
    bounded_tree_usage,
    canonical_json_bytes,
    discover_lean_declaration_names,
    file_tree_fingerprint,
    freeze_candidate,
    load_json,
    make_repair_feedback,
    sha256_bytes,
    sha256_file,
    treatment_free_runtime_manifest,
    tree_manifest,
    verify_tree_manifest,
    visible_system_runtime_manifest,
    utc_now,
    write_bytes_atomic,
    write_json_atomic,
)
from deployment import Deployment, executable_identity
from formalization_validator import validate_candidate
from hardware import snapshot_hardware, verify_frozen_hardware_identity
from lean_sandbox import compiler_command, extractor_command
from manifest_control import MANIFEST_PATH, ROOT, task_record, verify_manifest
from measure_library_build import validate_build_record


TERMINAL_CONDITION_STATES = {
    "ACCEPTED_FAITHFUL",
    "ATTEMPT_LIMIT",
    "ACTIVE_TIME_LIMIT",
    "RULE_VIOLATION",
    "INFRASTRUCTURE_FAILURE",
    "TELEMETRY_FAILURE",
    "AUDIT_SYSTEM_INCIDENT",
}

TERMINAL_PAIR_STATES = {"COMPLETE", "DRY_RUN_COMPLETE", "PAIR_INCIDENT"}
RESUMABLE_CONDITION_STATES = {"READY", "FEEDBACK_FROZEN"}
INCIDENT_CONDITION_STATES = {
    "INFRASTRUCTURE_FAILURE",
    "TELEMETRY_FAILURE",
    "RULE_VIOLATION",
    "AUDIT_SYSTEM_INCIDENT",
}

SEALED_PAIR_REPORT_FIELDS = (
    "pilot_id",
    "run_id",
    "task_id",
    "created_at_utc",
    "created_unix_ns",
    "pair_root",
    "pair_state_path",
    "status",
    "condition_order",
    "conditions",
    "partial_condition_evidence",
    "manifest_sha256",
    "admission_sha256",
    "dry_run",
    "strict_hardware_enforced",
    "measurement_admissible",
    "credential_scan",
    "incident",
    "completed_at_utc",
    "completed_unix_ns",
    "end_to_end_wall_seconds",
    "contestant_active_seconds_total",
    "contestant_active_time_complete",
    "contestant_active_time_interpretation",
    "excluded_end_to_end_wall_seconds",
)


def _task_packet_markdown(packet: dict[str, Any]) -> str:
    source = packet["bibliographic_source"]
    lines = [
        f"# {packet['task_id']}: {packet['selected_result']}",
        "",
        "## Authoritative source",
        "",
        f"- Authors: {', '.join(source['authors'])}",
        f"- Title: {source['title']}",
        f"- Year: {source['year']}",
        f"- PDF SHA-256: `{packet['paper_pdf']['sha256']}`",
        "",
        "## Exact source locations",
        "",
    ]
    for location in packet["paper_locations"]:
        lines.append(
            f"- {location['section']}, printed page(s) {location['printed_pages']}, "
            f"PDF page(s) {location['pdf_pages']}: {location['anchor']}"
        )
    lines.extend(["", "## Target clarification", ""])
    lines.extend(f"- {item}" for item in packet["task_clarification"])
    lines.extend(["", "## Scope constraints", ""])
    lines.extend(f"- {item}" for item in packet["scope_constraints"])
    lines.extend(
        [
            "",
            "The PDF is authoritative. This packet identifies the selected result and "
            "disambiguates its scope; it is not a Lean target or a proof.",
            "",
        ]
    )
    return "\n".join(lines)


def _candidate_template() -> str:
    return """import Mathlib

namespace HighamBenchCandidate

/- Replace this placeholder proposition and add faithful supporting definitions
above it. Keep the root name and literal proof hole unchanged. -/
theorem target : True := by
  sorry

end HighamBenchCandidate
"""


def _environment_note() -> str:
    return """# Local Lean environment

Run this exact command from the workspace:

```bash
lean --root . -o Candidate.olean Candidate.lean
```

The controller supplies the frozen Lean/Mathlib search path. Condition L's
prompt identifies its additional read-only library source mount when present.
Do not add package files, download dependencies, or access the network.
Positive-PID/process-group signaling and file metadata mutation syscalls are
disabled by the common command sandbox. Use ordinary file writes and renames;
the controller owns process cleanup and time limits.
"""


def _condition_order(config: dict[str, Any], task_id: str) -> list[str]:
    order = config.get("condition_order")
    if isinstance(order, dict) and order.get(task_id) in (["N", "L"], ["L", "N"]):
        return list(order[task_id])
    # This fallback is deterministic but is rejected once a frozen order field
    # is present. It exists only so older prepared manifests can be diagnosed.
    digest = sha256_bytes(task_id.encode("ascii"))
    return ["N", "L"] if int(digest[0], 16) % 2 == 0 else ["L", "N"]


def _validation_feedback(
    validation: dict[str, Any], *, forbidden_identifiers: set[str]
) -> dict[str, Any]:
    failure_code = validation.get("failure_code")
    if failure_code == "COMPILATION_FAILURE":
        mismatch = (
            "The submitted formalization does not elaborate in the frozen Lean environment."
        )
    elif failure_code == "RULE_VIOLATION":
        mismatch = (
            "The submission does not satisfy the required single-file, single-root-hole "
            "integrity contract."
        )
    else:
        mismatch = "The submission did not pass the fixed formalization validation contract."
    return make_repair_feedback(
        [
            {
                "paper_requirement": (
                    "The formalized proposition and all supporting definitions must elaborate "
                    "under the frozen Lean environment and obey the single-root-hole contract."
                ),
                "candidate_mismatch": mismatch,
            }
        ],
        forbidden_identifiers=forbidden_identifiers,
    )


def _usage_add(total: dict[str, int], usage: Mapping[str, Any]) -> dict[str, int]:
    result = dict(total)
    for key in (
        "input_tokens",
        "cached_input_tokens",
        "cache_write_input_tokens",
        "output_tokens",
        "reasoning_output_tokens",
        "total_tokens",
    ):
        value = usage.get(key, 0)
        if isinstance(value, int) and not isinstance(value, bool) and value >= 0:
            result[key] = result.get(key, 0) + value
    return result


def _measured_active_seconds(value: Any, *, label: str) -> float:
    if (
        not isinstance(value, (int, float))
        or isinstance(value, bool)
        or not math.isfinite(float(value))
        or float(value) < 0.0
    ):
        raise BenchmarkError(f"{label} is not a finite nonnegative duration")
    return float(value)


def _record_active_time_limit(state: dict[str, Any], limit: float) -> None:
    active_seconds = _measured_active_seconds(
        state.get("active_seconds"), label="condition active time"
    )
    state["status"] = "ACTIVE_TIME_LIMIT"
    state["active_time_limit_threshold_seconds"] = limit
    state["active_time_limit_overshoot_seconds"] = max(
        0.0, active_seconds - limit
    )


def _active_time_is_complete(record: Mapping[str, Any], *, label: str) -> bool:
    complete = record.get("contestant_active_time_complete")
    interpretation = record.get("contestant_active_time_interpretation")
    if (
        not isinstance(complete, bool)
        or interpretation not in {"exact", "observed lower bound"}
        or complete != (interpretation == "exact")
    ):
        raise BenchmarkError(f"{label} active-time interpretation is malformed")
    return complete


def _mark_active_time_incomplete(state: dict[str, Any]) -> None:
    state["contestant_active_time_complete"] = False
    state["contestant_active_time_interpretation"] = "observed lower bound"


def _mark_usage_incomplete(state: dict[str, Any]) -> None:
    state["contestant_usage_complete"] = False
    state["contestant_usage_interpretation"] = "observed lower bound"


def _aggregate_active_time_completeness(
    records: list[Mapping[str, Any]],
) -> tuple[bool, str]:
    complete = all(
        _active_time_is_complete(record, label=f"pair component {index}")
        for index, record in enumerate(records)
    )
    return complete, "exact" if complete else "observed lower bound"


def _write_state(path: Path, state: dict[str, Any]) -> None:
    now_utc = utc_now()
    now_unix_ns = time.time_ns()
    terminal_condition = state.get(
        "schema_version"
    ) == "formalization-condition-state-1" and state.get(
        "status"
    ) in TERMINAL_CONDITION_STATES
    terminal_pair = state.get(
        "schema_version"
    ) == "formalization-pair-state-1" and state.get("status") in TERMINAL_PAIR_STATES
    terminal = terminal_condition or terminal_pair
    if not terminal or "updated_at_utc" not in state:
        state["updated_at_utc"] = now_utc
    if terminal and "completed_unix_ns" not in state:
        created_unix_ns = state.get("created_unix_ns")
        if isinstance(created_unix_ns, int) and not isinstance(created_unix_ns, bool):
            state["completed_at_utc"] = now_utc
            state["completed_unix_ns"] = now_unix_ns
            state["end_to_end_wall_seconds"] = (
                now_unix_ns - created_unix_ns
            ) / 1_000_000_000
            active_components = [
                summary
                for summary in state.get("conditions", {}).values()
                if isinstance(summary, Mapping)
            ]
            partial = state.get("partial_condition_evidence")
            if isinstance(partial, Mapping):
                active_components.append(partial)
            measured_seconds = (
                float(state.get("active_seconds", 0.0))
                if terminal_condition
                else sum(
                    float(summary.get("active_seconds", 0.0))
                    for summary in active_components
                )
            )
            if terminal_pair:
                state["contestant_active_seconds_total"] = measured_seconds
                (
                    state["contestant_active_time_complete"],
                    state["contestant_active_time_interpretation"],
                ) = _aggregate_active_time_completeness(active_components)
            state["excluded_end_to_end_wall_seconds"] = max(
                0.0,
                float(state["end_to_end_wall_seconds"])
                - measured_seconds,
            )
    write_json_atomic(path, state, mode=0o400 if terminal else 0o600)


def _append_attempt(
    state: dict[str, Any], attempt: dict[str, Any], started_perf_ns: int
) -> None:
    state.pop("inflight_turn", None)
    wall_seconds = (time.perf_counter_ns() - started_perf_ns) / 1_000_000_000
    active_seconds = float(attempt.get("active_seconds", 0.0))
    attempt["wall_seconds"] = wall_seconds
    attempt["excluded_wall_seconds"] = max(0.0, wall_seconds - active_seconds)
    state["attempt_wall_seconds"] = float(state.get("attempt_wall_seconds", 0.0)) + wall_seconds
    state["excluded_wall_seconds"] = float(state.get("excluded_wall_seconds", 0.0)) + attempt[
        "excluded_wall_seconds"
    ]
    attempt["journal_state"] = "final"
    attempts = state["attempts"]
    if attempts and attempts[-1].get("attempt") == attempt.get("attempt"):
        if attempts[-1].get("journal_state") not in {"provisional", "final"}:
            raise BenchmarkError("attempt journal has an invalid prior state")
        # A final entry may only be observed through shared in-memory mutation
        # of the just-journaled attempt; never add or account it twice.
        if attempts[-1] is not attempt and attempts[-1].get("journal_state") == "final":
            raise BenchmarkError("attempt journal was finalized twice")
        attempts[-1] = attempt
    else:
        attempts.append(attempt)


def _journal_frozen_submission(
    state: dict[str, Any], attempt: dict[str, Any], started_perf_ns: int
) -> None:
    """Persist the measured submission before any off-clock validation/audit."""

    if state["attempts"] and state["attempts"][-1].get("attempt") == attempt.get("attempt"):
        raise BenchmarkError("attempt submission was journaled twice")
    elapsed = (time.perf_counter_ns() - started_perf_ns) / 1_000_000_000
    attempt["status"] = "SUBMISSION_FROZEN"
    attempt["journal_state"] = "provisional"
    attempt["submission_frozen_at_utc"] = utc_now()
    attempt["wall_seconds_through_submission"] = elapsed
    attempt["excluded_wall_seconds_through_submission"] = max(
        0.0, elapsed - float(attempt.get("active_seconds", 0.0))
    )
    state["attempts"].append(attempt)
    state.pop("inflight_turn", None)


def _formalizer_artifact_manifest(root: Path) -> dict[str, dict[str, str]]:
    names = (
        "turn.json",
        "events.jsonl",
        "stderr.log",
        "prompt.md",
        "last_message.txt",
        "network_violations.bin",
    )
    result: dict[str, dict[str, str]] = {}
    for name in names:
        path = root / name
        if not path.is_file() or path.is_symlink():
            raise BenchmarkError(f"formalizer artifact is missing or unsafe: {path}")
        result[name] = {"path": str(path), "sha256": sha256_file(path)}
    return result


@contextmanager
def _task_lock(run_root: Path, task_id: str) -> Iterator[None]:
    lock_root = run_root / "locks"
    lock_root.mkdir(parents=True, exist_ok=True, mode=0o700)
    path = lock_root / f"{task_id}.lock"
    descriptor = os.open(path, os.O_RDWR | os.O_CREAT | os.O_CLOEXEC, 0o600)
    try:
        fcntl.flock(descriptor, fcntl.LOCK_EX)
        yield
    finally:
        fcntl.flock(descriptor, fcntl.LOCK_UN)
        os.close(descriptor)


@contextmanager
def _campaign_lock(
    run_root: Path,
    global_registry_root: Path | None = None,
    predecessor_run_root: Path | None = None,
    legacy_predecessor_run_root: Path | None = None,
    ancestral_predecessor_run_root: Path | None = None,
    great_ancestral_predecessor_run_root: Path | None = None,
    fifth_ancestral_predecessor_run_root: Path | None = None,
) -> Iterator[None]:
    """Serialize this release, the account registry, and all five predecessors."""

    paths = [run_root / "locks" / "formalization-pilot.lock"]
    if global_registry_root is not None:
        paths.append(global_registry_root / "locks" / "campaign.lock")
    if predecessor_run_root is not None:
        paths.append(predecessor_run_root / "locks" / "formalization-pilot.lock")
    if legacy_predecessor_run_root is not None:
        paths.append(legacy_predecessor_run_root / "locks" / "formalization-pilot.lock")
    if ancestral_predecessor_run_root is not None:
        paths.append(ancestral_predecessor_run_root / "locks" / "formalization-pilot.lock")
    if great_ancestral_predecessor_run_root is not None:
        paths.append(great_ancestral_predecessor_run_root / "locks" / "formalization-pilot.lock")
    if fifth_ancestral_predecessor_run_root is not None:
        paths.append(fifth_ancestral_predecessor_run_root / "locks" / "formalization-pilot.lock")
    descriptors: list[int] = []
    try:
        for path in sorted(set(paths)):
            path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
            if path.parent.is_symlink() or path.is_symlink():
                raise BenchmarkError(f"unsafe benchmark lock path: {path}")
            descriptor = os.open(
                path,
                os.O_RDWR | os.O_CREAT | os.O_CLOEXEC | os.O_NOFOLLOW,
                0o600,
            )
            descriptors.append(descriptor)
            try:
                fcntl.flock(descriptor, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError as error:
                raise BenchmarkError(
                    "another formalization benchmark pair is already active on Titan"
                ) from error
        yield
    finally:
        for descriptor in reversed(descriptors):
            try:
                fcntl.flock(descriptor, fcntl.LOCK_UN)
            finally:
                os.close(descriptor)


class PairController:
    def __init__(self, deployment: Deployment, *, allow_unenforced_hardware: bool = False) -> None:
        self.deployment = deployment
        self.manifest, self.config = verify_manifest()
        self.strict_hardware = deployment.strict_hardware and not allow_unenforced_hardware
        root_module = deployment.library_source.parent / "NumStability.lean"
        self.feedback_forbidden_identifiers = discover_lean_declaration_names(
            deployment.library_source,
            root_module,
        )

    def _campaign_lock(self) -> Iterator[None]:
        return _campaign_lock(
            self.deployment.run_root,
            getattr(self.deployment, "global_registry_root", None),
            getattr(self.deployment, "predecessor_run_root", None),
            getattr(self.deployment, "legacy_predecessor_run_root", None),
            getattr(self.deployment, "ancestral_predecessor_run_root", None),
            getattr(self.deployment, "great_ancestral_predecessor_run_root", None),
            getattr(self.deployment, "fifth_ancestral_predecessor_run_root", None),
        )

    def _qualify_provider(self) -> dict[str, Any]:
        from provider_capability_canary import run_provider_capability_canary

        return run_provider_capability_canary(self.deployment)

    def _verify_qualification_binding(self, admission: Mapping[str, Any]) -> None:
        if self.deployment.global_registry_root is None:
            return  # Non-admissible synthetic fixtures have no account registry.
        from provider_capability_canary import ROLES, SCHEMA, qualification_identity

        binding = admission.get("provider_qualification")
        expected = (
            self.deployment.run_root
            / "qualifications"
            / sha256_file(MANIFEST_PATH)
            / "qualification.json"
        )
        if (
            not isinstance(binding, Mapping)
            or binding.get("record_path") != str(expected)
            or not expected.is_file()
            or expected.is_symlink()
            or binding.get("record_sha256") != sha256_file(expected)
            or binding.get("charged_to_contestant") is not False
        ):
            raise BenchmarkError("official pair lost its provider qualification binding")
        record = load_json(expected)
        identity = record.get("identity")
        expected_identity = qualification_identity(
            self.deployment, self.manifest, self.config
        )
        role_names = {role[0] for role in ROLES}
        outcomes = record.get("role_outcomes")
        if (
            record.get("schema_version") != SCHEMA
            or record.get("status") != "PASSED"
            or identity != expected_identity
            or record.get("provider_turns") != len(ROLES)
            or not isinstance(outcomes, Mapping)
            or set(outcomes) != role_names
            or record.get("charged_to_contestant") is not False
            or record.get("roles_manifest") != tree_manifest(expected.parent / "roles")
        ):
            raise BenchmarkError("official pair provider qualification evidence changed")
        for role in role_names:
            outcome = outcomes[role]
            expected_role = expected_identity["roles"][role]
            if (
                not isinstance(outcome, Mapping)
                or any(outcome.get(field) != value for field, value in expected_role.items())
            ):
                raise BenchmarkError(
                    "official pair provider qualification role evidence changed"
                )

    def _active_time_limit(self) -> float:
        return _measured_active_seconds(
            self.config.get("contestant_active_time_limit_seconds"),
            label="contestant active-time limit",
        )

    def _verify_condition_active_time_contract(
        self, state: Mapping[str, Any]
    ) -> None:
        active_time_complete = _active_time_is_complete(state, label="condition")
        active_seconds = _measured_active_seconds(
            state.get("active_seconds"), label="condition active time"
        )
        limit = self._active_time_limit()
        status = state.get("status")
        if not active_time_complete and status not in INCIDENT_CONDITION_STATES:
            raise BenchmarkError(
                "a scored condition may not contain incomplete active-time telemetry"
            )
        if (
            active_seconds > limit
            and status != "ACTIVE_TIME_LIMIT"
            and status not in INCIDENT_CONDITION_STATES
        ):
            raise BenchmarkError(
                "condition exceeded the cumulative active-time limit without "
                "terminating as ACTIVE_TIME_LIMIT"
            )
        if status == "ACTIVE_TIME_LIMIT":
            threshold = state.get("active_time_limit_threshold_seconds")
            overshoot = state.get("active_time_limit_overshoot_seconds")
            if (
                not isinstance(threshold, (int, float))
                or isinstance(threshold, bool)
                or float(threshold) != limit
                or not isinstance(overshoot, (int, float))
                or isinstance(overshoot, bool)
                or not math.isfinite(float(overshoot))
                or float(overshoot) != max(0.0, active_seconds - limit)
            ):
                raise BenchmarkError(
                    "active-time-limit evidence is missing or inconsistent"
                )

    def _credential_scan(self, pair_root: Path) -> dict[str, Any]:
        return assert_no_credentials_in_tree(pair_root, self.deployment.auth_file)

    def _quarantine_workspace_if_unsafe(
        self,
        *,
        pair_root: Path,
        task_id: str,
        condition: str,
        paper_path: Path,
        packet: dict[str, Any],
    ) -> dict[str, Any] | None:
        """Atomically move an unsafe generated tree outside the result closure.

        The moved tree is deliberately neither traversed nor deleted.  This keeps
        incident sealing bounded even for hostile permissions, special nodes, or
        a sparse/overpopulated tree.  A fresh authenticated staging workspace is
        then recreated so crash recovery never depends on the quarantined bytes.
        """

        condition_root = pair_root / "conditions" / condition
        workspace = condition_root / "workspace"
        quarantine_root = self.deployment.run_root / "quarantine"
        quarantine_root.mkdir(parents=True, exist_ok=True, mode=0o700)
        if not quarantine_root.is_dir() or quarantine_root.is_symlink():
            raise BenchmarkError("workspace quarantine root is unsafe")
        os.chmod(quarantine_root, 0o700)

        existing_records = sorted(condition_root.glob("workspace-quarantine-*.json"))
        if existing_records:
            if len(existing_records) != 1:
                raise BenchmarkError("condition has multiple workspace quarantine records")
            record_path = existing_records[0]
            if not record_path.is_file() or record_path.is_symlink():
                raise BenchmarkError("workspace quarantine record is unsafe")
            record = load_json(record_path)
            destination_raw = record.get("quarantine_path")
            if (
                record.get("schema_version")
                != "formalization-workspace-quarantine-1"
                or record.get("task_id") != task_id
                or record.get("condition") != condition
                or record.get("status") not in {"planned", "quarantined"}
                or not isinstance(destination_raw, str)
            ):
                raise BenchmarkError("workspace quarantine record is malformed")
            destination = Path(destination_raw).resolve(strict=False)
            try:
                destination.relative_to(quarantine_root.resolve())
            except ValueError as error:
                raise BenchmarkError("workspace quarantine path escapes its root") from error

            if record["status"] == "planned":
                if os.path.lexists(destination):
                    if destination.is_symlink() or not destination.is_dir():
                        raise BenchmarkError("quarantined workspace destination is unsafe")
                elif os.path.lexists(workspace):
                    metadata = os.lstat(workspace)
                    if (
                        metadata.st_dev != record.get("original_device")
                        or metadata.st_ino != record.get("original_inode")
                    ):
                        raise BenchmarkError(
                            "planned workspace quarantine source identity changed"
                        )
                    os.rename(workspace, destination)
                    for directory_path in (condition_root, quarantine_root):
                        fsync_descriptor = os.open(
                            directory_path, os.O_RDONLY | os.O_DIRECTORY
                        )
                        try:
                            os.fsync(fsync_descriptor)
                        finally:
                            os.close(fsync_descriptor)
                else:
                    record["quarantined_tree_missing_on_recovery"] = True
                record["status"] = "quarantined"
                record["quarantined_at_utc"] = utc_now()
                write_json_atomic(record_path, record, mode=0o400)

            if os.path.lexists(workspace):
                limits = self.config["workspace_limits"]
                try:
                    bounded_tree_usage(
                        workspace,
                        maximum_entries=int(limits["maximum_entries"]),
                        maximum_bytes=int(limits["maximum_total_bytes"]),
                    )
                except BenchmarkError:
                    recovery_destination = quarantine_root / (
                        f"{pair_root.name}-{condition}-recovery-{secrets.token_hex(8)}"
                    )
                    os.rename(workspace, recovery_destination)
                    fsync_directory = os.open(
                        quarantine_root, os.O_RDONLY | os.O_DIRECTORY
                    )
                    try:
                        os.fsync(fsync_directory)
                    finally:
                        os.close(fsync_directory)
                    record["additional_recovery_quarantine_path"] = str(
                        recovery_destination.resolve(strict=False)
                    )
                    write_json_atomic(record_path, record, mode=0o400)
            if not os.path.lexists(workspace):
                self._stage_condition(
                    task_id=task_id,
                    condition=condition,
                    condition_root=condition_root,
                    paper_path=paper_path,
                    packet=packet,
                )
            return record

        if not os.path.lexists(workspace):
            return None
        limits = self.config["workspace_limits"]
        try:
            bounded_tree_usage(
                workspace,
                maximum_entries=int(limits["maximum_entries"]),
                maximum_bytes=int(limits["maximum_total_bytes"]),
            )
            return None
        except BenchmarkError:
            pass

        token = secrets.token_hex(8)
        destination = quarantine_root / f"{pair_root.name}-{condition}-{token}"
        record_path = condition_root / f"workspace-quarantine-{token}.json"
        metadata = os.lstat(workspace)
        record: dict[str, Any] = {
            "schema_version": "formalization-workspace-quarantine-1",
            "task_id": task_id,
            "condition": condition,
            "classification": "unsafe_or_unbounded_generated_workspace",
            "status": "planned",
            "original_mode": metadata.st_mode,
            "original_device": metadata.st_dev,
            "original_inode": metadata.st_ino,
            "quarantine_path": str(destination.resolve(strict=False)),
            "workspace_limits": {
                "maximum_entries": int(limits["maximum_entries"]),
                "maximum_total_bytes": int(limits["maximum_total_bytes"]),
            },
            "planned_at_utc": utc_now(),
        }
        write_json_atomic(record_path, record, mode=0o400)
        os.rename(workspace, destination)
        for directory_path in (condition_root, quarantine_root):
            descriptor = os.open(directory_path, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
        record["status"] = "quarantined"
        record["quarantined_at_utc"] = utc_now()
        write_json_atomic(record_path, record, mode=0o400)
        self._stage_condition(
            task_id=task_id,
            condition=condition,
            condition_root=condition_root,
            paper_path=paper_path,
            packet=packet,
        )
        return record

    def _paper_and_packet(self, task_id: str) -> tuple[Path, Path, dict[str, Any]]:
        task = task_record(self.manifest, task_id)
        packet_path = ROOT / task["source_packet"]["relative_path"]
        packet = load_json(packet_path)
        paper_path = self.deployment.pdf_root / task["source_pdf"]["path_basename"]
        if not paper_path.is_file() or paper_path.is_symlink():
            raise BenchmarkError(f"private source PDF is missing: {paper_path}")
        actual = sha256_file(paper_path)
        if actual != task["source_pdf"]["sha256"]:
            raise BenchmarkError(
                f"source PDF hash mismatch for {task_id}: expected "
                f"{task['source_pdf']['sha256']}, got {actual}"
            )
        return paper_path, packet_path, packet

    def _verify_hardware_identity(self, hardware: Mapping[str, Any]) -> None:
        if not self.strict_hardware:
            return
        deployment_record = load_json(self.deployment.path)
        verify_frozen_hardware_identity(
            hardware, deployment_record.get("hardware_identity")
        )

    def doctor(self, task_id: str) -> dict[str, Any]:
        if task_id not in self.config["task_ids"]:
            raise BenchmarkError(f"task is outside the frozen pilot: {task_id}")
        paper_path, packet_path, _ = self._paper_and_packet(task_id)
        if self.strict_hardware:
            private_root = (self.deployment.path.parent / "private").resolve()
            try:
                self.deployment.auth_file.resolve().relative_to(private_root)
            except ValueError as error:
                raise BenchmarkError(
                    "Codex auth store is outside the private deployment root"
                ) from error
            auth_metadata = self.deployment.auth_file.lstat()
            if (
                self.deployment.auth_file.is_symlink()
                or not self.deployment.auth_file.is_file()
                or auth_metadata.st_uid != os.getuid()
                or auth_metadata.st_mode & 0o077
                or auth_metadata.st_size > 4 * 1024 * 1024
            ):
                raise BenchmarkError("Codex auth store permissions or type are unsafe")
        deployment_record = load_json(self.deployment.path)
        library = load_json(self.deployment.library_snapshot_record)
        if library.get("schema_version") != "numstability-formalization-snapshot-1":
            raise BenchmarkError("unsupported NumStability snapshot record")
        if library.get("commit") != self.config.get(
            "numstability_commit", "45813a95dacf577461bae13f033af0dbc985a225"
        ):
            raise BenchmarkError("deployed NumStability snapshot commit mismatch")
        for label, root, section_name in (
            ("NumStability source", self.deployment.library_source.parent, "source"),
            ("NumStability olean", self.deployment.library_olean, "olean"),
            (
                "NumStability setup build evidence",
                self.deployment.library_snapshot_record.parent / "build",
                "build",
            ),
        ):
            verify_tree_manifest(root, library.get(section_name), label=label)
        build_root = self.deployment.library_snapshot_record.parent / "build"
        build_record_path = build_root / "build-record.json"
        build_record = load_json(build_record_path)
        validate_build_record(
            build_record,
            expected_source_commit=str(library["commit"]),
            expected_mathlib_commit=str(self.config["mathlib_commit"]),
            expected_toolchain=str(self.config["lean_toolchain"]),
            expected_tool_hashes={
                "lake_sha256": sha256_file(
                    self.deployment.toolchain_root / "bin" / "lake"
                ),
                "lean_sha256": sha256_file(
                    self.deployment.toolchain_root / "bin" / "lean"
                ),
                "gnu_time_sha256": sha256_file(Path("/usr/bin/time")),
            },
        )
        deployed_output_tree = {
            "present": True,
            **file_tree_fingerprint(self.deployment.library_olean),
        }
        if build_record.get("generated_output_tree") != deployed_output_tree:
            raise BenchmarkError("deployed NumStability build output digest changed")
        deployed_olean_inventory = {
            "present": True,
            **file_tree_fingerprint(self.deployment.library_olean, suffix=".olean"),
        }
        if build_record.get("generated_olean") != deployed_olean_inventory:
            raise BenchmarkError("deployed NumStability OLean inventory changed")
        for section_name, expected_name in (
            ("build_output", "build-output.log"),
            ("gnu_time", "gnu-time.txt"),
        ):
            section = build_record.get(section_name)
            if not isinstance(section, Mapping) or section.get("relative_path") != expected_name:
                raise BenchmarkError(f"NumStability {section_name} record is malformed")
            artifact = build_root / expected_name
            if (
                not artifact.is_file()
                or artifact.is_symlink()
                or section.get("sha256") != sha256_file(artifact)
                or section.get("bytes") != artifact.stat().st_size
            ):
                raise BenchmarkError(f"NumStability {section_name} artifact changed")
        for hardware_field in ("hardware_before", "hardware_after"):
            observed = build_record.get(hardware_field)
            if not isinstance(observed, Mapping) or observed.get("admitted") is not True:
                raise BenchmarkError("NumStability build hardware envelope was not admitted")
            if self.strict_hardware:
                verify_frozen_hardware_identity(
                    observed, deployment_record.get("hardware_identity")
                )
        runtime = load_json(self.deployment.runtime_snapshot_record)
        if runtime.get("schema_version") != "formalization-runtime-snapshot-1":
            raise BenchmarkError("unsupported Lean/Mathlib snapshot record")
        if (
            runtime.get("lean_toolchain") != self.config["lean_toolchain"]
            or runtime.get("mathlib_commit") != self.config["mathlib_commit"]
        ):
            raise BenchmarkError("deployed Lean/Mathlib snapshot identity mismatch")
        verify_tree_manifest(
            self.deployment.toolchain_root,
            runtime.get("toolchain"),
            label="Lean toolchain",
        )
        verify_tree_manifest(
            self.deployment.packages_root,
            runtime.get("packages"),
            label="Lean package closure",
        )
        expected_treatment_absence = treatment_free_runtime_manifest(
            {
                "packages": self.deployment.packages_root,
                "toolchain": self.deployment.toolchain_root,
            }
        )
        if runtime.get("condition_n_treatment_absence") != expected_treatment_absence:
            raise BenchmarkError(
                "condition N runtime treatment-absence record changed after deployment"
            )
        common_prompt = ROOT / "prompts" / "formalizer.md"
        l_prompt = ROOT / "prompts" / "condition_L.md"
        repair_prompt = ROOT / "prompts" / "repair.md"
        for path in (common_prompt, l_prompt, repair_prompt):
            if not path.is_file() or path.is_symlink():
                raise BenchmarkError(f"controlled prompt is missing or unsafe: {path}")
        hardware = snapshot_hardware(strict=self.strict_hardware)
        self._verify_hardware_identity(hardware)
        command_resources = command_cgroup_snapshot(required=self.strict_hardware)
        if self.strict_hardware:
            assert command_resources is not None
            expected_command = self.config["command_resource_envelope"]
            if (
                command_resources.get("memory_max")
                != str(expected_command["memory_bytes"])
                or command_resources.get("memory_swap_max") != "0"
                or command_resources.get("pids_max")
                != str(expected_command["tasks_max"])
                or command_resources.get("cpu_weight")
                != str(expected_command["command_cpu_weight"])
            ):
                raise BenchmarkError("generated-command cgroup envelope changed")
        codex = executable_identity(self.deployment.codex_binary)
        if codex["version_exit_code"] != 0 or "codex" not in codex["version"].lower():
            raise BenchmarkError("Codex executable identity check failed")
        lean = executable_identity(self.deployment.toolchain_root / "bin" / "lean")
        if lean["version_exit_code"] != 0:
            raise BenchmarkError("Lean executable identity check failed")
        mathlib_root = self.deployment.packages_root / "mathlib"
        mathlib_commit = subprocess.run(
            ["git", "-C", str(mathlib_root), "rev-parse", "HEAD"],
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
        )
        if self.strict_hardware and (
            mathlib_commit.returncode != 0
            or mathlib_commit.stdout.strip() != self.config["mathlib_commit"]
        ):
            raise BenchmarkError("deployed Mathlib commit mismatch")
        if self.strict_hardware:
            expected_release_hash = deployment_record.get("release_manifest_sha256")
            if expected_release_hash != sha256_file(MANIFEST_PATH):
                raise BenchmarkError("deployment was prepared from a different release manifest")
            if (
                deployment_record.get("pilot_id") != self.config["pilot_id"]
                or deployment_record.get("manifest_payload_sha256")
                != self.manifest["manifest_payload_sha256"]
            ):
                raise BenchmarkError("deployment pilot or manifest payload identity changed")
            if (
                self.deployment.global_registry_root is None
                or self.deployment.predecessor_run_root is None
                or self.deployment.legacy_predecessor_run_root is None
                or self.deployment.ancestral_predecessor_run_root is None
                or self.deployment.great_ancestral_predecessor_run_root is None
                or self.deployment.fifth_ancestral_predecessor_run_root is None
            ):
                raise BenchmarkError("pilot-7 registry or predecessor locks are missing")
            from setup_titan import pilot5_lineage

            # doctor is called under the pilot-7 campaign lock (including the
            # predecessor and account-global locks). The frozen pilot-5 status
            # verifier would try to reacquire them in another process. Setup
            # performs that full status check before publication; here compare
            # the pinned release, qualification, index, state and report bytes.
            lineage = pilot5_lineage(
                str(self.deployment.predecessor_run_root.parent),
                verify_status=False,
            )
            if any(deployment_record.get(key) != value for key, value in lineage.items()):
                raise BenchmarkError("predecessor incident provenance changed")
            expected_codex_hash = deployment_record.get("codex_binary_sha256")
            if expected_codex_hash != codex["sha256"]:
                raise BenchmarkError("Codex binary changed after deployment")
            code_mode_host = self.deployment.codex_binary.with_name("codex-code-mode-host")
            if (
                code_mode_host.is_symlink()
                or not code_mode_host.is_file()
                or deployment_record.get("code_mode_host_binary") != str(code_mode_host)
                or deployment_record.get("code_mode_host_sha256")
                != self.deployment.code_mode_host_sha256
                or deployment_record.get("code_mode_host_sha256")
                != sha256_file(code_mode_host)
            ):
                raise BenchmarkError("Codex Code Mode host changed after deployment")
            for field, path, label in (
                (
                    "library_snapshot_record_sha256",
                    self.deployment.library_snapshot_record,
                    "NumStability snapshot record",
                ),
                (
                    "library_build_record_sha256",
                    build_record_path,
                    "NumStability setup build record",
                ),
                (
                    "runtime_snapshot_record_sha256",
                    self.deployment.runtime_snapshot_record,
                    "Lean/Mathlib snapshot record",
                ),
                ("bwrap_binary_sha256", self.deployment.bwrap_binary, "Bubblewrap binary"),
                ("offline_shell_sha256", self.deployment.offline_shell, "offline shell"),
            ):
                if deployment_record.get(field) != sha256_file(path):
                    raise BenchmarkError(f"{label} changed after deployment")
            for path_field, hash_field, label in (
                (
                    "command_sandbox_canary_record",
                    "command_sandbox_canary_record_sha256",
                    "command sandbox canary record",
                ),
                (
                    "runtime_canary_record",
                    "runtime_canary_record_sha256",
                    "runtime canary record",
                ),
                (
                    "codex_preflight_record",
                    "codex_preflight_record_sha256",
                    "Codex preflight record",
                ),
                (
                    "visible_system_runtime_record",
                    "visible_system_runtime_record_sha256",
                    "visible common system runtime record",
                ),
            ):
                raw = deployment_record.get(path_field)
                if not isinstance(raw, str) or not raw:
                    raise BenchmarkError(f"{label} path is missing")
                raw_path = Path(raw).expanduser()
                if raw_path.is_symlink():
                    raise BenchmarkError(f"{label} may not be a symlink")
                path = raw_path.resolve()
                try:
                    path.relative_to(self.deployment.path.parent.resolve())
                except ValueError as error:
                    raise BenchmarkError(f"{label} escapes the deployment root") from error
                if (
                    not path.is_file()
                    or deployment_record.get(hash_field) != sha256_file(path)
                ):
                    raise BenchmarkError(f"{label} changed after deployment")
            system_record_path = Path(
                str(deployment_record["visible_system_runtime_record"])
            ).expanduser().resolve()
            if load_json(system_record_path) != visible_system_runtime_manifest():
                raise BenchmarkError("visible common system runtime changed after deployment")
            preflight_record = load_json(
                Path(str(deployment_record["codex_preflight_record"])).resolve()
            )
            roles = preflight_record.get("roles")
            if (
                not isinstance(roles, Mapping)
                or set(roles) != {"formalizer", "auditor"}
                or any(
                    not isinstance(role, Mapping)
                    or role.get("private_auth_runtime_tmpfs") is not True
                    for role in roles.values()
                )
            ):
                raise BenchmarkError("Codex private-auth tmpfs preflight is missing")
        order = _condition_order(self.config, task_id)
        if order not in (["N", "L"], ["L", "N"]):
            raise BenchmarkError("invalid frozen condition order")
        indexed = self._load_indexed_pair(task_id)
        destination = (
            {"status": "NOT_STARTED", "run_id": None}
            if indexed is None
            else {
                "status": indexed[2].get("status"),
                "run_id": indexed[2].get("run_id"),
            }
        )
        record = {
            "schema_version": "formalization-doctor-1",
            "status": "admitted",
            "task_id": task_id,
            "checked_at_utc": utc_now(),
            "manifest_sha256": sha256_file(MANIFEST_PATH),
            "packet_sha256": sha256_file(packet_path),
            "paper_sha256": sha256_file(paper_path),
            "common_prompt_sha256": sha256_file(common_prompt),
            "condition_L_appendix_sha256": sha256_file(l_prompt),
            "repair_prompt_sha256": sha256_file(repair_prompt),
            "condition_order": order,
            "task_destination": destination,
            "formalizer_model": self.config.get("formalizer_model"),
            "formalizer_reasoning_effort": self.config.get("formalizer_reasoning_effort"),
            "audit_model": self.config.get("audit_model"),
            "audit_reasoning_effort": self.config.get("audit_reasoning_effort"),
            "submission_limit": self.config["submission_limit"],
            "contestant_active_time_limit_seconds": self.config[
                "contestant_active_time_limit_seconds"
            ],
            "token_cap": self.config["token_cap"],
            "hardware": hardware,
            "generated_command_cgroup": command_resources,
            "condition_n_treatment_absence": expected_treatment_absence,
            "codex": codex,
            "lean": lean,
            "mathlib_commit": (
                mathlib_commit.stdout.strip()
                if mathlib_commit.returncode == 0
                else "development-unverified"
            ),
            "bwrap_sha256": sha256_file(self.deployment.bwrap_binary),
            "offline_shell_sha256": sha256_file(self.deployment.offline_shell),
            "numstability_snapshot_record_sha256": sha256_file(
                self.deployment.library_snapshot_record
            ),
            "numstability_build_record_sha256": sha256_file(build_record_path),
            "numstability_build": {
                "elapsed_monotonic_seconds": build_record.get(
                    "elapsed_monotonic_seconds"
                ),
                "generated_olean": build_record.get("generated_olean"),
                "dependency_olean_file_count": build_record.get("cache_state", {})
                .get("dependency_closure_before", {})
                .get("dependency_olean_file_count"),
                "benchmark_charged": False,
            },
            "runtime_snapshot_record_sha256": sha256_file(
                self.deployment.runtime_snapshot_record
            ),
            "strict_hardware_enforced": self.strict_hardware,
            "measurement_admissible": self.strict_hardware,
            "no_provider_call": True,
        }
        return record

    def doctor_when_idle(self, task_id: str) -> dict[str, Any]:
        """Run the heavy release doctor only when no measured pair is active."""

        with self._campaign_lock():
            return self.doctor(task_id)

    def qualify_provider_when_idle(self, task_id: str) -> dict[str, Any]:
        """Paid off-benchmark qualification; never allocates a pair or task slot."""

        if not self.strict_hardware:
            raise BenchmarkError("provider qualification requires strict hardware")
        with self._campaign_lock():
            self.doctor(task_id)
            qualification = self._qualify_provider()
            if qualification.get("status") != "PASSED":
                raise BenchmarkError("provider qualification did not pass")
            self._verify_qualification_binding(
                {
                    "provider_qualification": {
                        "record_path": qualification.get("record_path"),
                        "record_sha256": qualification.get("record_sha256"),
                        "charged_to_contestant": False,
                    }
                }
            )
            return {
                "status": "PASSED",
                "pilot_id": self.config["pilot_id"],
                "record_path": qualification["record_path"],
                "record_sha256": qualification["record_sha256"],
                "benchmark_charged": False,
                "official_slot_consumed": False,
            }

    def _stage_condition(
        self,
        *,
        task_id: str,
        condition: str,
        condition_root: Path,
        paper_path: Path,
        packet: dict[str, Any],
    ) -> tuple[Path, str]:
        # Persist canonical paths so an OS path alias (for example macOS
        # /var -> /private/var) cannot make an unchanged staging record look
        # different after the task index is reloaded with Path.resolve().
        workspace = (condition_root / "workspace").resolve()
        common_bytes = (ROOT / "prompts" / "formalizer.md").read_bytes()
        prompt_bytes = common_bytes
        if condition == "L":
            prompt_bytes += (ROOT / "prompts" / "condition_L.md").read_bytes()
        elif condition != "N":
            raise BenchmarkError(f"unknown condition: {condition}")
        if workspace.exists():
            prompt_path = condition_root / "prompt.txt"
            staging_path = condition_root / "staging.json"
            paper_copy = workspace / "source" / "paper.pdf"
            packet_copy = workspace / "source" / "task.md"
            environment_note = workspace / "ENVIRONMENT.md"
            for path in (prompt_path, staging_path, paper_copy, packet_copy, environment_note):
                if not path.is_file() or path.is_symlink():
                    raise BenchmarkError(f"incomplete or unsafe staged condition file: {path}")
            expected_packet = _task_packet_markdown(packet).encode("utf-8")
            expected_environment = _environment_note().encode("utf-8")
            if prompt_path.read_bytes() != prompt_bytes:
                raise BenchmarkError(f"condition {condition} prompt changed after staging")
            if sha256_file(paper_copy) != sha256_file(paper_path):
                raise BenchmarkError(f"condition {condition} paper changed after staging")
            if packet_copy.read_bytes() != expected_packet:
                raise BenchmarkError(f"condition {condition} packet changed after staging")
            if environment_note.read_bytes() != expected_environment:
                raise BenchmarkError(f"condition {condition} environment note changed after staging")
            staging = load_json(staging_path)
            expected_staging_fields = {
                "task_id": task_id,
                "condition": condition,
                "workspace": str(workspace),
                "paper_sha256": sha256_file(paper_copy),
                "task_packet_render_sha256": sha256_file(packet_copy),
                "common_prompt_sha256": sha256_file(ROOT / "prompts" / "formalizer.md"),
                "effective_prompt_sha256": sha256_file(prompt_path),
                "condition_L_appendix": condition == "L",
            }
            changed_staging_fields = sorted(
                key
                for key, value in expected_staging_fields.items()
                if staging.get(key) != value
            )
            if changed_staging_fields:
                raise BenchmarkError(
                    f"condition {condition} staging record changed in fields: "
                    + ", ".join(changed_staging_fields)
                )
            template_hash = sha256_bytes(_candidate_template().encode("utf-8"))
            if staging.get("candidate_template_sha256") != template_hash:
                raise BenchmarkError(f"condition {condition} candidate baseline is unauthenticated")
            condition_state_path = condition_root / "condition_state.json"
            unstarted = not condition_state_path.exists()
            if condition_state_path.exists() and (
                condition_state_path.is_symlink() or not condition_state_path.is_file()
            ):
                raise BenchmarkError(f"condition {condition} state path is unsafe")
            if condition_state_path.is_file() and not condition_state_path.is_symlink():
                condition_state = load_json(condition_state_path)
                unstarted = not condition_state.get("attempts") and condition_state.get(
                    "status"
                ) == "READY"
            if unstarted and sha256_file(workspace / "Candidate.lean") != template_hash:
                raise BenchmarkError(
                    f"condition {condition} unstarted candidate changed after staging"
                )
            return workspace, prompt_bytes.decode("utf-8")
        source_root = workspace / "source"
        source_root.mkdir(parents=True, mode=0o700)
        shutil.copyfile(paper_path, source_root / "paper.pdf")
        write_bytes_atomic(
            source_root / "task.md", _task_packet_markdown(packet).encode("utf-8"), mode=0o400
        )
        write_bytes_atomic(workspace / "Candidate.lean", _candidate_template().encode("utf-8"))
        write_bytes_atomic(
            workspace / "ENVIRONMENT.md", _environment_note().encode("utf-8"), mode=0o400
        )
        (source_root / "paper.pdf").chmod(0o400)
        prompt = prompt_bytes.decode("utf-8")
        write_bytes_atomic(condition_root / "prompt.txt", prompt_bytes, mode=0o400)
        staged = {
            "task_id": task_id,
            "condition": condition,
            "workspace": str(workspace),
            "paper_sha256": sha256_file(source_root / "paper.pdf"),
            "task_packet_render_sha256": sha256_file(source_root / "task.md"),
            "candidate_template_sha256": sha256_file(workspace / "Candidate.lean"),
            "common_prompt_sha256": sha256_file(ROOT / "prompts" / "formalizer.md"),
            "effective_prompt_sha256": sha256_file(condition_root / "prompt.txt"),
            "condition_L_appendix": condition == "L",
            "staged_at_utc": utc_now(),
        }
        write_json_atomic(condition_root / "staging.json", staged, mode=0o400)
        if condition == "N":
            for path in workspace.rglob("*"):
                if path.is_file() and b"NumStability" in path.read_bytes():
                    raise BenchmarkError(f"condition N staging leaked NumStability in {path}")
        return workspace, prompt

    def _stage_pair(
        self,
        *,
        pair_root: Path,
        task_id: str,
        paper_path: Path,
        packet: dict[str, Any],
    ) -> dict[str, Any]:
        """Idempotently stage and authenticate both sides before either runs."""

        staged: dict[str, Any] = {}
        for condition in ("N", "L"):
            condition_root = pair_root / "conditions" / condition
            condition_root.mkdir(parents=True, exist_ok=True, mode=0o700)
            workspace, prompt = self._stage_condition(
                task_id=task_id,
                condition=condition,
                condition_root=condition_root,
                paper_path=paper_path,
                packet=packet,
            )
            staged[condition] = {
                "workspace": str(workspace),
                "effective_prompt_sha256": sha256_bytes(prompt.encode("utf-8")),
                "paper_sha256": sha256_file(workspace / "source" / "paper.pdf"),
                "packet_sha256": sha256_file(workspace / "source" / "task.md"),
                "candidate_template_sha256": load_json(
                    condition_root / "staging.json"
                )["candidate_template_sha256"],
            }
        common_hash = sha256_file(ROOT / "prompts" / "formalizer.md")
        l_appendix = (ROOT / "prompts" / "condition_L.md").read_bytes()
        if staged["N"]["paper_sha256"] != staged["L"]["paper_sha256"] or staged[
            "N"
        ]["packet_sha256"] != staged["L"]["packet_sha256"]:
            raise BenchmarkError("N/L source staging is not byte-identical")
        if staged["N"]["effective_prompt_sha256"] != common_hash:
            raise BenchmarkError("condition N prompt is not the frozen common prompt")
        expected_l = sha256_bytes(
            (ROOT / "prompts" / "formalizer.md").read_bytes() + l_appendix
        )
        if staged["L"]["effective_prompt_sha256"] != expected_l:
            raise BenchmarkError("condition L prompt composition mismatch")
        staging_path = pair_root / "pair_staging.json"
        if staging_path.exists():
            if staging_path.is_symlink() or load_json(staging_path) != staged:
                raise BenchmarkError("pair staging record changed or is inconsistent")
        else:
            write_json_atomic(staging_path, staged, mode=0o400)
        return staged

    def _driver(self, condition: str, condition_root: Path) -> CodexDriver:
        library_source = self.deployment.library_source if condition == "L" else None
        library_olean = self.deployment.library_olean if condition == "L" else None
        workspace = condition_root / "workspace"
        return CodexDriver(
            codex_binary=self.deployment.codex_binary,
            code_mode_host_sha256=self.deployment.code_mode_host_sha256,
            model=str(self.config["formalizer_model"]),
            reasoning_effort=str(self.config["formalizer_reasoning_effort"]),
            # Provider credentials are staged only in a private tmpfs/runtime
            # control directory owned and removed by the driver. They never
            # enter the result closure under condition_root.
            state_root=None,
            auth_file=self.deployment.auth_file,
            bwrap_binary=self.deployment.bwrap_binary,
            offline_shell=self.deployment.offline_shell,
            toolchain_root=self.deployment.toolchain_root,
            packages_root=self.deployment.packages_root,
            library_source=library_source,
            library_olean=library_olean,
            workspace_writable=True,
            protected_workspace_paths=[workspace / "source", workspace / "ENVIRONMENT.md"],
        )

    def _prepare_dossier(
        self,
        *,
        candidate: Path,
        condition: str,
        attempt_root: Path,
    ) -> tuple[Path, str, dict[str, Any]]:
        from prepare_candidate_audit import CandidateAuditError, prepare_candidate_audit

        helper = Path(__file__).with_name("declaration_dossier.lean")
        try:
            blind, private = prepare_candidate_audit(
                candidate,
                compiler_command=compiler_command(self.deployment, condition),
                extractor_command=extractor_command(
                    self.deployment, condition, helper
                ),
                compiler_environment={},
                extractor_environment={},
                scratch_root=attempt_root,
                timeout_seconds=float(self.config.get("validation_timeout_seconds", 600)),
            )
        except CandidateAuditError as error:
            raise BenchmarkError(
                f"candidate semantic dossier failed ({error.failure_code}): {error}"
            ) from error
        dossier_root = attempt_root / "dossier"
        dossier_root.mkdir()
        blind_path = dossier_root / "blind_semantic_dossier.json"
        private_path = dossier_root / "private_semantic_manifest.json"
        write_json_atomic(blind_path, blind, mode=0o400)
        write_json_atomic(private_path, private, mode=0o400)
        semantic_sha256 = blind.get("semantic_sha256")
        if (
            not isinstance(semantic_sha256, str)
            or private.get("blind_semantic_sha256") != semantic_sha256
        ):
            raise BenchmarkError("candidate dossier semantic hash contract failed")
        return blind_path, semantic_sha256, private

    def _run_condition(
        self,
        *,
        pair_root: Path,
        task_id: str,
        condition: str,
        paper_path: Path,
        packet: dict[str, Any],
    ) -> dict[str, Any]:
        condition_root = pair_root / "conditions" / condition
        driver = self._driver(condition, condition_root)
        result: dict[str, Any] | None = None
        try:
            result = self._run_condition_impl(
                pair_root=pair_root,
                task_id=task_id,
                condition=condition,
                paper_path=paper_path,
                packet=packet,
                driver=driver,
            )
        finally:
            # A condition's same-conversation guarantee and raw token stream
            # live in this one app-server process. Closing is also a security
            # check; a close failure is promoted to a pair incident.
            driver.close(
                artifact_dir=condition_root / "formalizer-session-close"
            )
        assert result is not None
        shutdown = self._condition_shutdown_binding(condition_root)
        if result.get("status") not in INCIDENT_CONDITION_STATES and (
            not shutdown or not all(item.get("graceful") is True for item in shutdown)
        ):
            raise BenchmarkError(
                f"condition {condition} has no authenticated graceful conversation shutdown"
            )
        # The earlier terminal write makes a crash conservative. Once the
        # conversation shutdown is authenticated, replace it with the complete
        # per-condition wall boundary, including final app-server teardown.
        closed_unix_ns = time.time_ns()
        created_unix_ns = result.get("created_unix_ns")
        if isinstance(created_unix_ns, int) and not isinstance(created_unix_ns, bool):
            result["completed_at_utc"] = utc_now()
            result["completed_unix_ns"] = closed_unix_ns
            result["end_to_end_wall_seconds"] = (
                closed_unix_ns - created_unix_ns
            ) / 1_000_000_000
            result["excluded_end_to_end_wall_seconds"] = max(
                0.0,
                float(result["end_to_end_wall_seconds"])
                - float(result.get("active_seconds", 0.0)),
            )
            result["updated_at_utc"] = result["completed_at_utc"]
            _write_state(condition_root / "condition_state.json", result)
        return result

    def _run_condition_impl(
        self,
        *,
        pair_root: Path,
        task_id: str,
        condition: str,
        paper_path: Path,
        packet: dict[str, Any],
        driver: CodexDriver,
    ) -> dict[str, Any]:
        condition_root = pair_root / "conditions" / condition
        condition_root.mkdir(parents=True, exist_ok=True, mode=0o700)
        state_path = condition_root / "condition_state.json"
        workspace, initial_prompt = self._stage_condition(
            task_id=task_id,
            condition=condition,
            condition_root=condition_root,
            paper_path=paper_path,
            packet=packet,
        )
        if state_path.is_file():
            state = load_json(state_path)
            if state.get("status") == "CONTESTANT_ACTIVE" and not state.get(
                "inflight_turn"
            ):
                recovery_attempt = len(state.get("attempts", [])) + 1
                recovered_formalizer = (
                    condition_root
                    / "attempts"
                    / f"{recovery_attempt:02d}"
                    / "formalizer"
                )
                recovered_turn_path = recovered_formalizer / "turn.json"
                if not recovered_turn_path.is_file() or recovered_turn_path.is_symlink():
                    _mark_usage_incomplete(state)
                    _mark_active_time_incomplete(state)
                    _write_state(state_path, state)
                    raise BenchmarkError(
                        "interrupted formalizer turn has no safe complete turn record"
                    )
                try:
                    recovered_turn = load_json(recovered_turn_path)
                except BenchmarkError as error:
                    _mark_usage_incomplete(state)
                    _mark_active_time_incomplete(state)
                    _write_state(state_path, state)
                    raise BenchmarkError(
                        "interrupted formalizer turn record is malformed"
                    ) from error
                else:
                    recovered_usage = recovered_turn.get("usage")
                    recovered_active = recovered_turn.get(
                        "active_seconds_through_quiescence"
                    )
                    if (
                        recovered_turn.get("schema_version") != 3
                        or not isinstance(recovered_usage, Mapping)
                        or set(recovered_usage) != set(state["contestant_usage"])
                        or any(
                            not isinstance(value, int)
                            or isinstance(value, bool)
                            or value < 0
                            for value in recovered_usage.values()
                        )
                        or not isinstance(recovered_active, (int, float))
                        or isinstance(recovered_active, bool)
                        or not math.isfinite(float(recovered_active))
                        or recovered_active < 0
                        or not isinstance(recovered_turn.get("usage_complete"), bool)
                    ):
                        _mark_usage_incomplete(state)
                        _mark_active_time_incomplete(state)
                        _write_state(state_path, state)
                        raise BenchmarkError(
                            "interrupted formalizer turn record is malformed"
                        )
                    recovered_return_path = (
                        recovered_formalizer.parent / "turn-return.json"
                    )
                    recovered_return = {
                        "schema_version": "formalization-turn-return-1",
                        "attempt": recovery_attempt,
                        "thread_id": recovered_turn.get("thread_id"),
                        "exit_code": recovered_turn.get("exit_code"),
                        "timed_out": recovered_turn.get("timed_out"),
                        "failure_kind": recovered_turn.get("failure_kind"),
                        "model_active_seconds": float(recovered_active),
                        "usage": dict(recovered_usage),
                        "usage_complete": recovered_turn["usage_complete"],
                        "formalizer_turn_sha256": sha256_file(recovered_turn_path),
                        "returned_at_utc": utc_now(),
                        "reconstructed_after_interruption": True,
                    }
                    write_json_atomic(
                        recovered_return_path, recovered_return, mode=0o400
                    )
                    state["active_seconds"] = _measured_active_seconds(
                        state.get("active_seconds"), label="condition active time"
                    ) + float(recovered_active)
                    state["contestant_usage"] = _usage_add(
                        state["contestant_usage"], recovered_usage
                    )
                    if not recovered_turn["usage_complete"]:
                        state["contestant_usage_complete"] = False
                        state["contestant_usage_interpretation"] = (
                            "observed lower bound"
                        )
                    if recovered_turn.get("thread_id"):
                        state["thread_id"] = recovered_turn["thread_id"]
                    state["inflight_turn"] = {
                        "attempt": recovery_attempt,
                        "turn_return_path": str(recovered_return_path),
                        "turn_return_sha256": sha256_file(recovered_return_path),
                        "model_active_seconds": float(recovered_active),
                        "usage": dict(recovered_usage),
                        "usage_complete": recovered_turn["usage_complete"],
                        "reconstructed_after_interruption": True,
                    }
                    state["status"] = "TURN_RETURNED"
                    _write_state(state_path, state)
            inflight = state.get("inflight_turn")
            if (
                state.get("status") == "TURN_RETURNED"
                and isinstance(inflight, Mapping)
                and inflight.get("reconstructed_after_interruption") is not True
                and "candidate_freeze_seconds" not in inflight
            ):
                # A hard kill may land after the model turn was journaled but
                # before the final candidate hash/freeze duration was durable.
                # The model usage remains independently complete; only charged
                # active time becomes a known lower bound.
                _mark_active_time_incomplete(state)
                _write_state(state_path, state)
            if state.get("status") in TERMINAL_CONDITION_STATES:
                self._verify_condition_active_time_contract(state)
                return state
            if state.get("attempts"):
                raise BenchmarkError(
                    f"condition {condition} was interrupted after a submission; "
                    "the exact raw-usage conversation cannot be cold-resumed"
                )
            if state.get("status") not in RESUMABLE_CONDITION_STATES:
                raise BenchmarkError(
                    f"condition {condition} was interrupted outside a resumable boundary: "
                    f"{state.get('status')}"
                )
        else:
            state = {
                "schema_version": "formalization-condition-state-1",
                "task_id": task_id,
                "condition": condition,
                "status": "READY",
                "thread_id": None,
                "active_seconds": 0.0,
                "attempt_wall_seconds": 0.0,
                "excluded_wall_seconds": 0.0,
                "contestant_usage": {
                    "input_tokens": 0,
                    "cached_input_tokens": 0,
                    "cache_write_input_tokens": 0,
                    "output_tokens": 0,
                    "reasoning_output_tokens": 0,
                    "total_tokens": 0,
                },
                "contestant_usage_complete": True,
                "contestant_usage_interpretation": "exact",
                "contestant_active_time_complete": True,
                "contestant_active_time_interpretation": "exact",
                "attempts": [],
                "created_at_utc": utc_now(),
                "created_unix_ns": time.time_ns(),
            }
            _write_state(state_path, state)

        maximum = int(self.config["submission_limit"])
        limit = self._active_time_limit()
        while len(state["attempts"]) < maximum:
            attempt_number = len(state["attempts"]) + 1
            remaining = limit - _measured_active_seconds(
                state.get("active_seconds"), label="condition active time"
            )
            if remaining <= 0:
                _record_active_time_limit(state, limit)
                _write_state(state_path, state)
                return state
            attempt_root = condition_root / "attempts" / f"{attempt_number:02d}"
            if attempt_root.exists():
                raise BenchmarkError(f"incomplete attempt artifact already exists: {attempt_root}")
            attempt_root.mkdir(parents=True)
            attempt_started_perf_ns = time.perf_counter_ns()
            hardware = snapshot_hardware(strict=self.strict_hardware)
            self._verify_hardware_identity(hardware)
            write_json_atomic(attempt_root / "hardware.json", hardware, mode=0o400)
            if attempt_number == 1:
                prompt = initial_prompt
                prompt_kind = "initial"
            else:
                feedback = state["attempts"][-1].get("repair_feedback")
                if not isinstance(feedback, dict):
                    raise BenchmarkError("repair attempt has no frozen feedback")
                template = (ROOT / "prompts" / "repair.md").read_text(encoding="utf-8")
                prompt = template.replace(
                    "{{FEEDBACK_JSON}}", json.dumps(feedback, indent=2, sort_keys=True)
                )
                prompt_kind = "repair"
            state["status"] = "CONTESTANT_ACTIVE"
            _write_state(state_path, state)
            formalizer_root = attempt_root / "formalizer"
            result = driver.run_turn(
                prompt=prompt,
                workspace=workspace,
                artifact_dir=formalizer_root,
                timeout_seconds=remaining,
                thread_id=state.get("thread_id"),
            )
            model_active_seconds = (
                (result.active_ended_perf_ns - result.active_started_perf_ns)
                / 1_000_000_000
                if result.active_started_perf_ns is not None
                and result.active_ended_perf_ns is not None
                else 0.0
            )
            model_active_seconds = _measured_active_seconds(
                model_active_seconds, label="model active time"
            )
            turn_record_path = formalizer_root / "turn.json"
            if not turn_record_path.is_file() or turn_record_path.is_symlink():
                raise BenchmarkError("formalizer returned without a safe turn record")
            turn_return_path = attempt_root / "turn-return.json"
            turn_return = {
                "schema_version": "formalization-turn-return-1",
                "attempt": attempt_number,
                "thread_id": result.thread_id,
                "exit_code": result.exit_code,
                "timed_out": result.timed_out,
                "failure_kind": result.failure_kind,
                "model_active_seconds": model_active_seconds,
                "usage": result.usage,
                "usage_complete": result.usage_complete,
                "formalizer_turn_sha256": sha256_file(turn_record_path),
                "returned_at_utc": utc_now(),
            }
            write_json_atomic(turn_return_path, turn_return, mode=0o400)
            state["active_seconds"] = (
                _measured_active_seconds(
                    state.get("active_seconds"), label="condition active time"
                )
                + model_active_seconds
            )
            if any(value > 0 for value in result.usage.values()):
                state["contestant_usage"] = _usage_add(
                    state["contestant_usage"], result.usage
                )
            if not result.usage_complete:
                state["contestant_usage_complete"] = False
                state["contestant_usage_interpretation"] = "observed lower bound"
            if result.thread_id:
                state["thread_id"] = result.thread_id
            state["inflight_turn"] = {
                "attempt": attempt_number,
                "turn_return_path": str(turn_return_path),
                "turn_return_sha256": sha256_file(turn_return_path),
                "model_active_seconds": model_active_seconds,
                "usage": result.usage,
                "usage_complete": result.usage_complete,
            }
            state["status"] = "TURN_RETURNED"
            _write_state(state_path, state)
            control_surface_violation: str | None = None
            try:
                driver.assert_safe_control_surfaces(
                    workspace,
                    scan_workspace=result.failure_kind != "workspace_limit",
                )
            except BenchmarkError as error:
                control_surface_violation = str(error)
            frozen: dict[str, Any] | None = None
            freeze_error: str | None = None
            candidate_freeze_seconds = 0.0
            may_submit = (
                result.exit_code == 0
                and not result.timed_out
                and result.active_started_perf_ns is not None
                and result.active_ended_perf_ns is not None
                and result.failure_kind != "provider_capability_violation"
            )
            if may_submit:
                freeze_started = time.perf_counter_ns()
                try:
                    frozen = freeze_candidate(
                        workspace / "Candidate.lean",
                        attempt_root / "Candidate.lean",
                        auth_file=self.deployment.auth_file,
                    )
                except (OSError, BenchmarkError) as error:
                    freeze_error = str(error)
                finally:
                    candidate_freeze_seconds = _measured_active_seconds(
                        (time.perf_counter_ns() - freeze_started) / 1_000_000_000,
                        label="candidate freeze time",
                    )
                    state["active_seconds"] = (
                        _measured_active_seconds(
                            state.get("active_seconds"),
                            label="condition active time",
                        )
                        + candidate_freeze_seconds
                    )
                    state["inflight_turn"]["candidate_freeze_seconds"] = (
                        candidate_freeze_seconds
                    )
                    state["inflight_turn"]["candidate"] = frozen
                    # Candidate hashing/freezing is the final charged phase.
                    # Persist its actual duration even if an asynchronous
                    # interruption prevents the submission from being scored.
                    _write_state(state_path, state)
            active_seconds = model_active_seconds + candidate_freeze_seconds
            hardware_after = snapshot_hardware(strict=self.strict_hardware)
            self._verify_hardware_identity(hardware_after)
            write_json_atomic(
                attempt_root / "hardware_after.json", hardware_after, mode=0o400
            )
            usage_complete = result.usage_complete
            if not may_submit:
                state["inflight_turn"]["candidate_freeze_seconds"] = 0.0
                state["inflight_turn"]["candidate"] = None
            _write_state(state_path, state)
            attempt: dict[str, Any] = {
                "attempt": attempt_number,
                "prompt_kind": prompt_kind,
                "active_seconds": active_seconds,
                "model_active_seconds": model_active_seconds,
                "candidate_freeze_seconds": candidate_freeze_seconds,
                "formalizer_wall_seconds": result.wall_seconds,
                "active_seconds_cumulative": state["active_seconds"],
                "usage": result.usage,
                "usage_complete": usage_complete,
                "usage_cumulative": state["contestant_usage"],
                "thread_id": result.thread_id,
                "formalizer_exit_code": result.exit_code,
                "formalizer_timed_out": result.timed_out,
                "formalizer_failure_kind": result.failure_kind,
                "formalizer_artifacts": _formalizer_artifact_manifest(
                    formalizer_root
                ),
                "candidate": frozen,
                "freeze_error": freeze_error,
                "control_surface_violation": control_surface_violation,
                "hardware_start_sha256": sha256_file(attempt_root / "hardware.json"),
                "hardware_end_sha256": sha256_file(
                    attempt_root / "hardware_after.json"
                ),
                "validation": None,
                "audit": None,
                "repair_feedback": None,
            }
            marker = attempt_root / "formalizer" / "network_violations.bin"
            if result.failure_kind == "provider_capability_violation":
                # A missing or unsafe provider capability is a release failure,
                # not misconduct by the contestant. Preserve any secondary
                # network/control evidence without letting it mask the cause.
                attempt["status"] = "INFRASTRUCTURE_FAILURE"
                attempt["incident_classification"] = (
                    "provider_capability_incompatibility"
                )
                _append_attempt(state, attempt, attempt_started_perf_ns)
                state["status"] = "INFRASTRUCTURE_FAILURE"
                _write_state(state_path, state)
                return state
            if control_surface_violation is not None:
                attempt["status"] = "RULE_VIOLATION"
                _append_attempt(state, attempt, attempt_started_perf_ns)
                state["status"] = "RULE_VIOLATION"
                _write_state(state_path, state)
                return state
            if marker.is_file() and marker.stat().st_size:
                attempt["status"] = "RULE_VIOLATION"
                _append_attempt(state, attempt, attempt_started_perf_ns)
                state["status"] = "RULE_VIOLATION"
                _write_state(state_path, state)
                return state
            if result.failure_kind in {
                "workspace_limit",
                "artifact_limit",
                "command_resource_limit",
            }:
                attempt["status"] = "RULE_VIOLATION"
                _append_attempt(state, attempt, attempt_started_perf_ns)
                state["status"] = "RULE_VIOLATION"
                _write_state(state_path, state)
                return state
            if result.timed_out and result.active_started_perf_ns is None:
                attempt["status"] = "INFRASTRUCTURE_FAILURE"
                _append_attempt(state, attempt, attempt_started_perf_ns)
                state["status"] = "INFRASTRUCTURE_FAILURE"
                _write_state(state_path, state)
                return state
            if result.timed_out:
                # The five-hour endpoint is itself a valid benchmark outcome.
                # Raw responses observed before interruption remain a documented
                # lower bound; incomplete token telemetry does not censor time.
                attempt["status"] = "ACTIVE_TIME_LIMIT"
                attempt["usage_interpretation"] = "incomplete lower bound"
                _append_attempt(state, attempt, attempt_started_perf_ns)
                _record_active_time_limit(state, limit)
                _write_state(state_path, state)
                return state
            if result.failure_kind == "telemetry_invalid":
                attempt["status"] = "TELEMETRY_FAILURE"
                _append_attempt(state, attempt, attempt_started_perf_ns)
                state["status"] = "TELEMETRY_FAILURE"
                _write_state(state_path, state)
                return state
            if result.exit_code != 0 or result.thread_id is None:
                attempt["status"] = "INFRASTRUCTURE_FAILURE"
                _append_attempt(state, attempt, attempt_started_perf_ns)
                state["status"] = "INFRASTRUCTURE_FAILURE"
                _write_state(state_path, state)
                return state
            if result.usage.get("total_tokens", 0) <= 0:
                attempt["status"] = "TELEMETRY_FAILURE"
                _append_attempt(state, attempt, attempt_started_perf_ns)
                state["status"] = "TELEMETRY_FAILURE"
                _write_state(state_path, state)
                return state
            if _measured_active_seconds(
                state.get("active_seconds"), label="condition active time"
            ) > limit:
                attempt["status"] = "ACTIVE_TIME_LIMIT"
                attempt["active_time_limit_threshold_seconds"] = limit
                attempt["active_time_limit_overshoot_seconds"] = (
                    float(state["active_seconds"]) - limit
                )
                _append_attempt(state, attempt, attempt_started_perf_ns)
                _record_active_time_limit(state, limit)
                _write_state(state_path, state)
                return state
            if frozen is None:
                feedback = make_repair_feedback(
                    [
                        {
                            "paper_requirement": "A complete Lean formalization must be submitted.",
                            "candidate_mismatch": (
                                "The required candidate file was not available at the submission "
                                "boundary."
                            ),
                        }
                    ],
                    forbidden_identifiers=self.feedback_forbidden_identifiers,
                )
                attempt["status"] = "CANDIDATE_MISSING"
                attempt["repair_feedback"] = feedback
                write_json_atomic(
                    attempt_root / "repair_feedback.json", feedback, mode=0o400
                )
                attempt["repair_feedback_sha256"] = sha256_file(
                    attempt_root / "repair_feedback.json"
                )
                _append_attempt(state, attempt, attempt_started_perf_ns)
                if attempt_number == maximum:
                    state["status"] = "ATTEMPT_LIMIT"
                    _write_state(state_path, state)
                    return state
                state["status"] = "FEEDBACK_FROZEN"
                _write_state(state_path, state)
                continue

            _journal_frozen_submission(state, attempt, attempt_started_perf_ns)
            state["status"] = "SUBMISSION_FROZEN"
            _write_state(state_path, state)
            state["status"] = "VALIDATING"
            _write_state(state_path, state)
            validation_started = time.perf_counter_ns()
            validation = validate_candidate(
                attempt_root / "Candidate.lean",
                compiler_command=compiler_command(self.deployment, condition),
                compiler_environment={},
                scratch_root=attempt_root,
                timeout_seconds=float(self.config.get("validation_timeout_seconds", 600)),
            )
            validation["wall_seconds"] = (
                time.perf_counter_ns() - validation_started
            ) / 1_000_000_000
            validation["excluded_from_contestant_measurement"] = True
            write_json_atomic(attempt_root / "validation.json", validation, mode=0o400)
            attempt["validation"] = {
                "pass": validation["pass"],
                "failure_code": validation["failure_code"],
                "sha256": sha256_file(attempt_root / "validation.json"),
                "wall_seconds": validation["wall_seconds"],
            }
            if validation.get("failure_code") == "INFRASTRUCTURE_FAILURE":
                attempt["status"] = "INFRASTRUCTURE_FAILURE"
                _append_attempt(state, attempt, attempt_started_perf_ns)
                state["status"] = "INFRASTRUCTURE_FAILURE"
                _write_state(state_path, state)
                return state
            if not validation["pass"]:
                feedback = _validation_feedback(
                    validation,
                    forbidden_identifiers=self.feedback_forbidden_identifiers,
                )
                write_json_atomic(attempt_root / "repair_feedback.json", feedback, mode=0o400)
                attempt["status"] = "VALIDATION_REJECTED"
                attempt["repair_feedback"] = feedback
                attempt["repair_feedback_sha256"] = sha256_file(
                    attempt_root / "repair_feedback.json"
                )
                _append_attempt(state, attempt, attempt_started_perf_ns)
                if attempt_number == maximum:
                    state["status"] = "ATTEMPT_LIMIT"
                    _write_state(state_path, state)
                    return state
                state["status"] = "FEEDBACK_FROZEN"
                _write_state(state_path, state)
                continue

            state["status"] = "PREPARING_AUDIT"
            _write_state(state_path, state)
            dossier_started = time.perf_counter_ns()
            try:
                blind_path, semantic_sha256, private = self._prepare_dossier(
                    candidate=attempt_root / "Candidate.lean",
                    condition=condition,
                    attempt_root=attempt_root,
                )
            except BenchmarkError as error:
                attempt["dossier_wall_seconds"] = (
                    time.perf_counter_ns() - dossier_started
                ) / 1_000_000_000
                attempt["status"] = "INFRASTRUCTURE_FAILURE"
                attempt["infrastructure_error"] = str(error)
                _append_attempt(state, attempt, attempt_started_perf_ns)
                state["status"] = "INFRASTRUCTURE_FAILURE"
                _write_state(state_path, state)
                return state
            attempt["dossier_wall_seconds"] = (
                time.perf_counter_ns() - dossier_started
            ) / 1_000_000_000
            attempt["semantic_sha256"] = semantic_sha256
            audit_root = pair_root / "audits" / semantic_sha256
            audit = AuditController(
                codex_binary=self.deployment.codex_binary,
                code_mode_host_sha256=self.deployment.code_mode_host_sha256,
                auth_file=self.deployment.auth_file,
                model=str(self.config["audit_model"]),
                reasoning_effort=str(self.config["audit_reasoning_effort"]),
                timeout_seconds=float(self.config.get("audit_timeout_seconds", 7200)),
                maximum_infrastructure_retries=int(
                    self.config.get("audit_infrastructure_retries", 2)
                ),
                bwrap_binary=self.deployment.bwrap_binary,
                offline_shell=self.deployment.offline_shell,
                toolchain_root=self.deployment.toolchain_root,
                packages_root=self.deployment.packages_root,
                forbidden_feedback_identifiers=self.feedback_forbidden_identifiers,
            )
            state["status"] = "AUDITING"
            _write_state(state_path, state)
            audit_started_perf_ns = time.perf_counter_ns()
            try:
                decision = audit.run(
                    task_id=task_id,
                    paper_path=paper_path,
                    paper_sha256=packet["paper_pdf"]["sha256"],
                    source_packet=workspace / "source" / "task.md",
                    dossier_path=blind_path,
                    semantic_sha256=semantic_sha256,
                    audit_root=audit_root,
                )
            except BenchmarkError as error:
                audit_wall_seconds = (
                    time.perf_counter_ns() - audit_started_perf_ns
                ) / 1_000_000_000
                audit_classification = (
                    "provider_capability_incompatibility"
                    if isinstance(error, ProviderCapabilityError)
                    else "audit_system_infrastructure"
                )
                incident = audit.seal_incident(
                    audit_root=audit_root,
                    task_id=task_id,
                    paper_sha256=packet["paper_pdf"]["sha256"],
                    semantic_sha256=semantic_sha256,
                    error=str(error),
                    wall_seconds=audit_wall_seconds,
                    classification=audit_classification,
                )
                incident_path = audit_root / "incident.json"
                attempt["audit"] = {
                    "verdict": "audit-system-incident",
                    "accepted": False,
                    "incident_path": str(incident_path),
                    "incident_sha256": sha256_file(incident_path),
                    "wall_seconds": incident["audit_wall_seconds"],
                    "tokens_excluded": True,
                    "usage": incident["usage"],
                    "usage_complete": incident["usage_complete"],
                    "classification": audit_classification,
                }
                attempt["status"] = "AUDIT_SYSTEM_INCIDENT"
                attempt["incident_classification"] = audit_classification
                attempt["infrastructure_error"] = str(error)
                _append_attempt(state, attempt, attempt_started_perf_ns)
                state["status"] = "AUDIT_SYSTEM_INCIDENT"
                _write_state(state_path, state)
                return state
            audit_usage = {
                "input_tokens": 0,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 0,
                "reasoning_output_tokens": 0,
                "total_tokens": 0,
            }
            audit_usage_complete = True
            incremental_telemetry = decision.get(
                "incremental_auditor_telemetry", decision.get("auditor_telemetry", [])
            )
            for role_telemetry in incremental_telemetry:
                if isinstance(role_telemetry, Mapping):
                    role_usage = role_telemetry.get("usage")
                    if isinstance(role_usage, Mapping):
                        audit_usage = _usage_add(audit_usage, role_usage)
                    for role_try in role_telemetry.get("tries", []):
                        if isinstance(role_try, Mapping) and not role_try.get(
                            "usage_complete", False
                        ):
                            audit_usage_complete = False
            attempt["audit"] = {
                "verdict": decision["verdict"],
                "accepted": decision["accepted"],
                "decision_path": str(audit_root / "decision.json"),
                "decision_sha256": sha256_file(audit_root / "decision.json"),
                "reused": bool(decision.get("audit_reused", False)),
                "shared_audit_wall_seconds": decision["audit_wall_seconds"],
                "wall_seconds": decision.get(
                    "incremental_audit_wall_seconds", decision["audit_wall_seconds"]
                ),
                "tokens_excluded": True,
                "usage": audit_usage,
                "usage_complete": audit_usage_complete,
            }
            if decision.get("audit_incident"):
                attempt["status"] = "AUDIT_SYSTEM_INCIDENT"
                _append_attempt(state, attempt, attempt_started_perf_ns)
                state["status"] = "AUDIT_SYSTEM_INCIDENT"
                _write_state(state_path, state)
                return state
            if decision["accepted"]:
                attempt["status"] = "ACCEPTED_FAITHFUL"
                _append_attempt(state, attempt, attempt_started_perf_ns)
                state["status"] = "ACCEPTED_FAITHFUL"
                state["accepted_semantic_sha256"] = semantic_sha256
                _write_state(state_path, state)
                return state
            feedback = decision.get("repair_feedback")
            if not isinstance(feedback, dict):
                raise BenchmarkError("unaccepted audit decision has no neutral feedback")
            frozen_feedback_path = audit_root / "repair_feedback.json"
            if (
                not frozen_feedback_path.is_file()
                or frozen_feedback_path.is_symlink()
                or load_json(frozen_feedback_path) != feedback
            ):
                raise BenchmarkError("audit repair feedback failed its frozen-byte contract")
            attempt["repair_feedback"] = feedback
            attempt["repair_feedback_sha256"] = sha256_file(frozen_feedback_path)
            attempt["status"] = "AUDIT_REJECTED"
            _append_attempt(state, attempt, attempt_started_perf_ns)
            if attempt_number == maximum:
                state["status"] = "ATTEMPT_LIMIT"
                _write_state(state_path, state)
                return state
            state["status"] = "FEEDBACK_FROZEN"
            _write_state(state_path, state)

        state["status"] = "ATTEMPT_LIMIT"
        _write_state(state_path, state)
        return state

    @staticmethod
    def _condition_shutdown_binding(condition_root: Path) -> list[dict[str, Any]]:
        records: list[dict[str, Any]] = []
        candidates = [condition_root / "formalizer-session-close" / "shutdown.json"]
        candidates.extend(
            sorted(condition_root.glob("attempts/*/formalizer/session-close/shutdown.json"))
        )
        for path in candidates:
            if not path.exists():
                continue
            if not path.is_file() or path.is_symlink():
                raise BenchmarkError(f"unsafe formalizer shutdown record: {path}")
            record = load_json(path)
            stderr_path = path.parent / "stderr-after-last-turn.log"
            expected_stderr = record.get("stderr_sha256")
            if (
                not stderr_path.is_file()
                or stderr_path.is_symlink()
                or not isinstance(expected_stderr, str)
                or sha256_file(stderr_path) != expected_stderr
                or not isinstance(record.get("graceful"), bool)
                or not isinstance(record.get("returncode"), int)
                or record.get("stdout_drained_to_eof") is not True
                or record.get("late_stdout_line_count") != 0
            ):
                raise BenchmarkError("formalizer shutdown evidence failed authentication")
            records.append(
                {
                    "record_path": str(path.resolve()),
                    "record_sha256": sha256_file(path),
                    "stderr_path": str(stderr_path.resolve()),
                    "stderr_sha256": expected_stderr,
                    "graceful": record["graceful"],
                    "returncode": record["returncode"],
                }
            )
        return records

    @staticmethod
    def _summarize_condition(
        pair_root: Path, condition: str, result: Mapping[str, Any]
    ) -> dict[str, Any]:
        condition_root = pair_root / "conditions" / condition
        condition_state_path = condition_root / "condition_state.json"
        return {
            "status": result["status"],
            "active_seconds": result["active_seconds"],
            "contestant_active_time_complete": result[
                "contestant_active_time_complete"
            ],
            "contestant_active_time_interpretation": result[
                "contestant_active_time_interpretation"
            ],
            "end_to_end_wall_seconds": result.get("end_to_end_wall_seconds"),
            "excluded_end_to_end_wall_seconds": result.get(
                "excluded_end_to_end_wall_seconds"
            ),
            "contestant_usage": result["contestant_usage"],
            "contestant_usage_complete": result["contestant_usage_complete"],
            "contestant_usage_interpretation": result[
                "contestant_usage_interpretation"
            ],
            "submission_count": len(result["attempts"]),
            "state_path": str(condition_state_path),
            "state_sha256": sha256_file(condition_state_path),
            "conversation_shutdown": PairController._condition_shutdown_binding(
                condition_root
            ),
            "evidence_manifest": tree_manifest(condition_root),
        }

    @staticmethod
    def _summarize_partial_condition(
        pair_root: Path, condition: str, state: Mapping[str, Any]
    ) -> dict[str, Any]:
        condition_root = pair_root / "conditions" / condition
        state_path = condition_root / "condition_state.json"
        attempts = state.get("attempts")
        active_seconds = state.get("active_seconds", 0.0)
        if not isinstance(attempts, list):
            raise BenchmarkError("partial condition attempts are malformed")
        if (
            not isinstance(active_seconds, (int, float))
            or isinstance(active_seconds, bool)
            or active_seconds < 0
        ):
            raise BenchmarkError("partial condition active time is malformed")
        return {
            "condition": condition,
            "status": state.get("status"),
            "active_seconds": float(active_seconds),
            "contestant_active_time_complete": state.get(
                "contestant_active_time_complete"
            ),
            "contestant_active_time_interpretation": state.get(
                "contestant_active_time_interpretation"
            ),
            "contestant_usage": state.get("contestant_usage"),
            "contestant_usage_complete": state.get("contestant_usage_complete"),
            "contestant_usage_interpretation": state.get(
                "contestant_usage_interpretation"
            ),
            "submission_count": len(attempts),
            "inflight_turn": state.get("inflight_turn"),
            "scoreable": False,
            "state_path": str(state_path),
            "state_sha256": sha256_file(state_path),
            "evidence_manifest": tree_manifest(condition_root),
        }

    @staticmethod
    def _verify_partial_condition(
        pair_root: Path, partial: Mapping[str, Any]
    ) -> None:
        condition = partial.get("condition")
        if condition not in {"N", "L"}:
            raise BenchmarkError("partial condition evidence has invalid identity")
        expected_path = pair_root / "conditions" / str(condition) / "condition_state.json"
        if Path(str(partial.get("state_path", ""))).resolve() != expected_path.resolve():
            raise BenchmarkError("partial condition state path is inconsistent")
        if (
            not expected_path.is_file()
            or expected_path.is_symlink()
            or sha256_file(expected_path) != partial.get("state_sha256")
            or tree_manifest(expected_path.parent) != partial.get("evidence_manifest")
        ):
            raise BenchmarkError("partial condition evidence failed authentication")
        state = load_json(expected_path)
        if (
            state.get("status") != partial.get("status")
            or partial.get("scoreable") is not False
            or state.get("contestant_active_time_complete")
            != partial.get("contestant_active_time_complete")
            or state.get("contestant_active_time_interpretation")
            != partial.get("contestant_active_time_interpretation")
            or state.get("contestant_usage") != partial.get("contestant_usage")
            or state.get("contestant_usage_complete")
            != partial.get("contestant_usage_complete")
            or state.get("contestant_usage_interpretation")
            != partial.get("contestant_usage_interpretation")
            or len(state.get("attempts", [])) != partial.get("submission_count")
            or state.get("inflight_turn") != partial.get("inflight_turn")
        ):
            raise BenchmarkError("partial condition evidence is inconsistent")
        if (
            not isinstance(partial.get("contestant_usage_complete"), bool)
            or partial.get("contestant_usage_interpretation")
            not in {"exact", "observed lower bound"}
        ):
            raise BenchmarkError("partial condition usage interpretation is malformed")
        _active_time_is_complete(partial, label="partial condition")
        state_active_seconds = state.get("active_seconds", 0.0)
        partial_active_seconds = partial.get("active_seconds", 0.0)
        if (
            not isinstance(state_active_seconds, (int, float))
            or isinstance(state_active_seconds, bool)
            or not isinstance(partial_active_seconds, (int, float))
            or isinstance(partial_active_seconds, bool)
            or float(state_active_seconds) != float(partial_active_seconds)
        ):
            raise BenchmarkError("partial condition active time is inconsistent")
        attempts = state.get("attempts")
        if not isinstance(attempts, list):
            raise BenchmarkError("partial condition attempts are malformed")
        for attempt in attempts:
            if not isinstance(attempt, Mapping):
                raise BenchmarkError("partial condition attempt is malformed")
            PairController._verify_attempt_submission(pair_root, attempt)
            PairController._verify_attempt_audit(pair_root, attempt)
        inflight = state.get("inflight_turn")
        if inflight is not None:
            if not isinstance(inflight, Mapping):
                raise BenchmarkError("partial inflight turn is malformed")
            record_path = Path(str(inflight.get("turn_return_path", ""))).resolve()
            condition_root = expected_path.parent.resolve()
            try:
                record_path.relative_to(condition_root / "attempts")
            except ValueError as error:
                raise BenchmarkError("partial inflight turn escapes its condition") from error
            expected_hash = inflight.get("turn_return_sha256")
            if (
                not isinstance(expected_hash, str)
                or len(expected_hash) != 64
                or not record_path.is_file()
                or record_path.is_symlink()
                or sha256_file(record_path) != expected_hash
            ):
                raise BenchmarkError("partial inflight turn record failed authentication")

    @staticmethod
    def _verify_attempt_submission(
        pair_root: Path, attempt: Mapping[str, Any]
    ) -> None:
        journal_state = attempt.get("journal_state")
        if journal_state is None:
            # Older synthetic/development records predate submission journaling.
            return
        if journal_state not in {"provisional", "final"}:
            raise BenchmarkError("condition attempt has invalid journal state")
        artifacts = attempt.get("formalizer_artifacts")
        if not isinstance(artifacts, Mapping) or not artifacts:
            raise BenchmarkError("journaled submission lacks formalizer artifacts")
        resolved_pair = pair_root.resolve()
        for record in artifacts.values():
            if not isinstance(record, Mapping):
                raise BenchmarkError("formalizer artifact binding is malformed")
            raw_path = record.get("path")
            expected_hash = record.get("sha256")
            if not isinstance(raw_path, str) or not isinstance(expected_hash, str):
                raise BenchmarkError("formalizer artifact binding is incomplete")
            unresolved_path = Path(raw_path)
            if unresolved_path.is_symlink():
                raise BenchmarkError("formalizer artifact is a symlink")
            path = unresolved_path.resolve()
            try:
                path.relative_to(resolved_pair)
            except ValueError as error:
                raise BenchmarkError("formalizer artifact escapes the pair root") from error
            if (
                not path.is_file()
                or len(expected_hash) != 64
                or sha256_file(path) != expected_hash
            ):
                raise BenchmarkError("formalizer artifact failed authentication")
        candidate = attempt.get("candidate")
        if journal_state == "provisional" and not isinstance(candidate, Mapping):
            raise BenchmarkError("provisional submission lacks a frozen candidate")
        if isinstance(candidate, Mapping):
            raw_path = candidate.get("path")
            expected_hash = candidate.get("sha256")
            expected_bytes = candidate.get("bytes")
            if (
                not isinstance(raw_path, str)
                or not isinstance(expected_hash, str)
                or not isinstance(expected_bytes, int)
                or isinstance(expected_bytes, bool)
            ):
                raise BenchmarkError("frozen candidate binding is malformed")
            unresolved_path = Path(raw_path)
            if unresolved_path.is_symlink():
                raise BenchmarkError("frozen candidate is a symlink")
            path = unresolved_path.resolve()
            try:
                path.relative_to(resolved_pair)
            except ValueError as error:
                raise BenchmarkError("frozen candidate escapes the pair root") from error
            if (
                not path.is_file()
                or len(expected_hash) != 64
                or path.stat().st_size != expected_bytes
                or sha256_file(path) != expected_hash
            ):
                raise BenchmarkError("frozen candidate failed authentication")

    @staticmethod
    def _verify_attempt_audit(pair_root: Path, attempt: Mapping[str, Any]) -> None:
        audit = attempt.get("audit")
        if audit is None:
            return
        if not isinstance(audit, Mapping):
            raise BenchmarkError("condition attempt has malformed audit metadata")
        if "decision_path" in audit:
            raw_path = audit.get("decision_path")
            expected_hash = audit.get("decision_sha256")
        elif "incident_path" in audit:
            raw_path = audit.get("incident_path")
            expected_hash = audit.get("incident_sha256")
        else:
            raise BenchmarkError("condition attempt audit has no terminal record")
        if not isinstance(raw_path, str) or not isinstance(expected_hash, str):
            raise BenchmarkError("condition attempt audit binding is malformed")
        path = Path(raw_path).resolve()
        audits_root = (pair_root / "audits").resolve()
        try:
            path.relative_to(audits_root)
        except ValueError as error:
            raise BenchmarkError("condition attempt audit escapes the pair root") from error
        if (
            not path.is_file()
            or path.is_symlink()
            or len(expected_hash) != 64
            or sha256_file(path) != expected_hash
        ):
            raise BenchmarkError("condition attempt audit record failed authentication")
        terminal = load_json(path)
        if terminal.get("evidence_manifest") != audit_evidence_manifest(path.parent):
            raise BenchmarkError("condition attempt audit evidence closure changed")

    def _verify_condition_summary(
        self, pair_root: Path, condition: str, summary: Mapping[str, Any]
    ) -> dict[str, Any]:
        expected_path = pair_root / "conditions" / condition / "condition_state.json"
        recorded_path = Path(str(summary.get("state_path", ""))).resolve()
        if recorded_path != expected_path.resolve():
            raise BenchmarkError("recorded condition state path is inconsistent")
        expected_sha256 = summary.get("state_sha256")
        if (
            not isinstance(expected_sha256, str)
            or len(expected_sha256) != 64
            or not expected_path.is_file()
            or expected_path.is_symlink()
            or sha256_file(expected_path) != expected_sha256
        ):
            raise BenchmarkError("recorded condition state failed authentication")
        condition_state = load_json(expected_path)
        self._verify_condition_active_time_contract(condition_state)
        expected_evidence = summary.get("evidence_manifest")
        if expected_evidence != tree_manifest(expected_path.parent):
            raise BenchmarkError("recorded condition evidence closure changed")
        shutdown = PairController._condition_shutdown_binding(expected_path.parent)
        if summary.get("conversation_shutdown") != shutdown:
            recorded_shutdown = summary.get("conversation_shutdown")
            recorded_paths = (
                [item.get("record_path") for item in recorded_shutdown]
                if isinstance(recorded_shutdown, list)
                else []
            )
            observed_paths = [item.get("record_path") for item in shutdown]
            raise BenchmarkError(
                "recorded condition shutdown binding changed "
                f"(recorded_paths={recorded_paths!r}, observed_paths={observed_paths!r})"
            )
        if condition_state.get("status") not in INCIDENT_CONDITION_STATES and (
            not shutdown or not all(item.get("graceful") is True for item in shutdown)
        ):
            raise BenchmarkError("scored condition lacks a graceful conversation shutdown")
        if (
            condition_state.get("condition") != condition
            or condition_state.get("status") not in TERMINAL_CONDITION_STATES
            or summary.get("status") != condition_state.get("status")
            or summary.get("active_seconds") != condition_state.get("active_seconds")
            or summary.get("contestant_active_time_complete")
            != condition_state.get("contestant_active_time_complete")
            or summary.get("contestant_active_time_interpretation")
            != condition_state.get("contestant_active_time_interpretation")
            or summary.get("end_to_end_wall_seconds")
            != condition_state.get("end_to_end_wall_seconds")
            or summary.get("excluded_end_to_end_wall_seconds")
            != condition_state.get("excluded_end_to_end_wall_seconds")
            or summary.get("contestant_usage") != condition_state.get("contestant_usage")
            or summary.get("contestant_usage_complete")
            != condition_state.get("contestant_usage_complete")
            or summary.get("contestant_usage_interpretation")
            != condition_state.get("contestant_usage_interpretation")
            or summary.get("submission_count") != len(condition_state.get("attempts", []))
        ):
            raise BenchmarkError("recorded condition summary is inconsistent")
        attempts = condition_state.get("attempts")
        if not isinstance(attempts, list):
            raise BenchmarkError("recorded condition attempts are malformed")
        for attempt in attempts:
            if not isinstance(attempt, Mapping):
                raise BenchmarkError("recorded condition attempt is malformed")
            PairController._verify_attempt_submission(pair_root, attempt)
            PairController._verify_attempt_audit(pair_root, attempt)
        return condition_state

    def _index_path(self, task_id: str) -> Path:
        return self.deployment.run_root / "index" / f"{task_id}.json"

    def _registry_index_path(self, task_id: str) -> Path | None:
        root = getattr(self.deployment, "global_registry_root", None)
        if root is None:
            return None
        return root / "index" / str(self.config["pilot_id"]) / f"{task_id}.json"

    def _index_identity(self) -> dict[str, Any]:
        deployment = load_json(self.deployment.path)
        return {
            "pilot_id": self.config["pilot_id"],
            "release_commit": deployment.get("release_commit"),
            "manifest_sha256": sha256_file(MANIFEST_PATH),
            "manifest_payload_sha256": self.manifest["manifest_payload_sha256"],
            "deployment_sha256": sha256_file(self.deployment.path),
        }

    def _reconcile_global_reservation(self, task_id: str) -> None:
        """Finish a torn two-file index commit without allocating a new pair."""

        registry_path = self._registry_index_path(task_id)
        index_path = self._index_path(task_id)
        if registry_path is None or not registry_path.exists() or index_path.exists():
            return
        if not registry_path.is_file() or registry_path.is_symlink():
            raise BenchmarkError("account-global pilot/task reservation is unsafe")
        index = load_json(registry_path)
        if (
            index.get("schema_version") != "formalization-task-index-2"
            or index.get("task_id") != task_id
            or any(index.get(key) != value for key, value in self._index_identity().items())
        ):
            raise BenchmarkError("account-global pilot/task reservation identity changed")
        pair_root_raw = index.get("pair_root")
        state_path_raw = index.get("pair_state_path")
        if not isinstance(pair_root_raw, str) or not isinstance(state_path_raw, str):
            raise BenchmarkError("account-global pilot/task reservation paths are malformed")
        pair_root_path = Path(pair_root_raw)
        pair_root = pair_root_path.resolve()
        if (
            pair_root_path.is_symlink()
            or pair_root.parent != (self.deployment.run_root / "pairs").resolve()
            or Path(state_path_raw).resolve() != pair_root / "pair_state.json"
        ):
            raise BenchmarkError("account-global reservation escaped this deployment")
        state_path = pair_root / "pair_state.json"
        staging = pair_root / "pair_staging.json"
        admission = pair_root / "admission.json"
        if any(
            not path.is_file() or path.is_symlink()
            for path in (state_path, staging, admission)
        ):
            raise BenchmarkError("reserved pair has incomplete immutable staging")
        state = load_json(state_path)
        if (
            state.get("task_id") != task_id
            or state.get("run_id") != index.get("run_id")
            or state.get("pilot_id") != self.config["pilot_id"]
            or state.get("manifest_sha256") != sha256_file(MANIFEST_PATH)
            or state.get("admission_sha256") != sha256_file(admission)
            or state.get("dry_run") is not False
        ):
            raise BenchmarkError("reserved pair failed its state/admission binding")
        self._verify_qualification_binding(load_json(admission))
        index_path.parent.mkdir(parents=True, exist_ok=True)
        if index_path.exists() or index_path.is_symlink():
            raise BenchmarkError("task index appeared during reservation recovery")
        write_json_atomic(index_path, index, mode=0o600)

    def _verify_pair_report(
        self,
        report: Path,
        pair_state: Mapping[str, Any],
        *,
        expected_sha256: str | None,
        allow_report_ahead: bool = False,
    ) -> str:
        if not report.is_file() or report.is_symlink():
            raise BenchmarkError("terminal pair report is missing or unsafe")
        actual_sha256 = sha256_file(report)
        if expected_sha256 is not None and expected_sha256 != actual_sha256:
            raise BenchmarkError("terminal pair report hash mismatch")
        sealed = load_json(report)
        self._verify_terminal_pair_payload(report.parent, sealed)
        if allow_report_ahead:
            immutable_fields = (
                "schema_version",
                "pilot_id",
                "run_id",
                "task_id",
                "created_at_utc",
                "created_unix_ns",
                "pair_root",
                "pair_state_path",
                "condition_order",
                "manifest_sha256",
                "admission_sha256",
                "dry_run",
                "strict_hardware_enforced",
                "measurement_admissible",
            )
            if any(
                sealed.get(field) != pair_state.get(field)
                for field in immutable_fields
            ):
                raise BenchmarkError(
                    "terminal pair report changed an immutable pre-report field"
                )
            stale_conditions = pair_state.get("conditions")
            sealed_conditions = sealed.get("conditions")
            if not isinstance(stale_conditions, Mapping) or not isinstance(
                sealed_conditions, Mapping
            ):
                raise BenchmarkError("pair report recovery has malformed condition maps")
            if any(
                condition not in sealed_conditions
                or sealed_conditions[condition] != summary
                for condition, summary in stale_conditions.items()
            ):
                raise BenchmarkError(
                    "terminal pair report does not extend the durable condition prefix"
                )
            stale_partial = pair_state.get("partial_condition_evidence")
            if (
                stale_partial is not None
                and stale_partial != sealed.get("partial_condition_evidence")
            ):
                raise BenchmarkError(
                    "terminal pair report changed durable partial-condition evidence"
                )
        elif any(
            sealed.get(field) != pair_state.get(field)
            for field in SEALED_PAIR_REPORT_FIELDS
        ):
            raise BenchmarkError("terminal pair report is inconsistent with pair state")
        return actual_sha256

    def _verify_terminal_pair_payload(
        self, pair_root: Path, sealed: Mapping[str, Any]
    ) -> None:
        """Authenticate a report without trusting a possibly stale pair state."""

        if (
            sealed.get("schema_version") != "formalization-pair-state-1"
            or sealed.get("pilot_id") != self.config.get("pilot_id")
            or sealed.get("status") not in {"COMPLETE", "PAIR_INCIDENT"}
            or sealed.get("dry_run") is not False
            or sealed.get("strict_hardware_enforced") is not True
            or sealed.get("measurement_admissible") is not True
            or sealed.get("manifest_sha256") != sha256_file(MANIFEST_PATH)
        ):
            raise BenchmarkError("terminal pair report has an invalid release identity")
        task_id = sealed.get("task_id")
        if not isinstance(task_id, str):
            raise BenchmarkError("terminal pair report has no task identity")
        # This also rejects task IDs outside the frozen manifest.
        task_record(self.manifest, task_id)
        if sealed.get("condition_order") != _condition_order(self.config, task_id):
            raise BenchmarkError("terminal pair report changed the frozen condition order")
        expected_pair_root = pair_root.resolve()
        if (
            Path(str(sealed.get("pair_root", ""))).resolve() != expected_pair_root
            or Path(str(sealed.get("pair_state_path", ""))).resolve()
            != expected_pair_root / "pair_state.json"
        ):
            raise BenchmarkError("terminal pair report has inconsistent result paths")
        admission = pair_root / "admission.json"
        if (
            not admission.is_file()
            or admission.is_symlink()
            or sealed.get("admission_sha256") != sha256_file(admission)
        ):
            raise BenchmarkError("terminal pair report lost its admission binding")
        self._verify_qualification_binding(load_json(admission))

        order = sealed["condition_order"]
        conditions = sealed.get("conditions")
        if not isinstance(conditions, Mapping) or any(
            condition not in order or not isinstance(summary, Mapping)
            for condition, summary in conditions.items()
        ):
            raise BenchmarkError("terminal pair report has malformed conditions")
        observed_order = [condition for condition in order if condition in conditions]
        if set(conditions) != set(observed_order) or observed_order != order[: len(observed_order)]:
            raise BenchmarkError("terminal pair report conditions are not a frozen-order prefix")
        for condition in observed_order:
            self._verify_condition_summary(pair_root, condition, conditions[condition])

        partial = sealed.get("partial_condition_evidence")
        if partial is not None:
            if (
                not isinstance(partial, Mapping)
                or sealed.get("status") != "PAIR_INCIDENT"
                or partial.get("condition") in conditions
                or len(observed_order) >= len(order)
                or partial.get("condition") != order[len(observed_order)]
            ):
                raise BenchmarkError("terminal pair report has invalid partial evidence")
            self._verify_partial_condition(pair_root, partial)

        if sealed.get("status") == "COMPLETE":
            if observed_order != order or partial is not None:
                raise BenchmarkError("complete pair report lacks two scored conditions")
            if any(
                conditions[condition].get("status") in INCIDENT_CONDITION_STATES
                for condition in order
            ):
                raise BenchmarkError("complete pair report contains a condition incident")
        else:
            incident = sealed.get("incident")
            if (
                not isinstance(incident, Mapping)
                or incident.get("condition") not in order
                or not isinstance(incident.get("classification"), str)
                or not incident.get("classification")
                or not isinstance(incident.get("message"), str)
                or not incident.get("message")
                or not isinstance(incident.get("recorded_at_utc"), str)
                or not incident.get("recorded_at_utc")
            ):
                raise BenchmarkError("pair incident report has malformed incident metadata")

        created_ns = sealed.get("created_unix_ns")
        completed_ns = sealed.get("completed_unix_ns")
        if (
            not isinstance(created_ns, int)
            or isinstance(created_ns, bool)
            or not isinstance(completed_ns, int)
            or isinstance(completed_ns, bool)
            or completed_ns < created_ns
        ):
            raise BenchmarkError("terminal pair report has malformed wall-clock bounds")
        active_components = [conditions[condition] for condition in observed_order]
        if isinstance(partial, Mapping):
            active_components.append(partial)
        expected_active = sum(
            float(component.get("active_seconds", 0.0))
            for component in active_components
        )
        expected_active_complete, expected_active_interpretation = (
            _aggregate_active_time_completeness(active_components)
        )
        expected_wall = (completed_ns - created_ns) / 1_000_000_000
        expected_excluded = max(0.0, expected_wall - expected_active)
        if (
            sealed.get("contestant_active_seconds_total") != expected_active
            or sealed.get("contestant_active_time_complete")
            != expected_active_complete
            or sealed.get("contestant_active_time_interpretation")
            != expected_active_interpretation
            or sealed.get("end_to_end_wall_seconds") != expected_wall
            or sealed.get("excluded_end_to_end_wall_seconds") != expected_excluded
            or sealed.get("updated_at_utc") != sealed.get("completed_at_utc")
        ):
            raise BenchmarkError("terminal pair report has inconsistent measured totals")
        credential_scan = sealed.get("credential_scan")
        if (
            not isinstance(credential_scan, Mapping)
            or credential_scan.get("schema_version")
            != "formalization-terminal-credential-closure-1"
            or credential_scan.get("passed") is not True
            or credential_scan.get("prospective_terminal_payloads_scanned") != 2
            or not isinstance(credential_scan.get("preseal_tree"), Mapping)
            or credential_scan["preseal_tree"].get("passed") is not True
        ):
            raise BenchmarkError("terminal pair report has invalid credential closure")

    def _seal_pair_terminal(
        self, *, pair_root: Path, pair_state_path: Path, pair_state: dict[str, Any]
    ) -> dict[str, Any]:
        """Seal a scored completion or unscored incident report before terminal state."""

        if pair_state.get("status") not in {"COMPLETE", "PAIR_INCIDENT"}:
            raise BenchmarkError("cannot seal a nonterminal official pair")
        if "completed_unix_ns" not in pair_state:
            pair_state["completed_at_utc"] = utc_now()
            pair_state["completed_unix_ns"] = time.time_ns()
        created_unix_ns = pair_state.get("created_unix_ns")
        if isinstance(created_unix_ns, int) and not isinstance(created_unix_ns, bool):
            pair_state["end_to_end_wall_seconds"] = (
                int(pair_state["completed_unix_ns"]) - created_unix_ns
            ) / 1_000_000_000
        active_components = [
            summary
            for summary in pair_state.get("conditions", {}).values()
            if isinstance(summary, Mapping)
        ]
        partial = pair_state.get("partial_condition_evidence")
        if isinstance(partial, Mapping):
            active_components.append(partial)
        pair_state["contestant_active_seconds_total"] = sum(
            float(component.get("active_seconds", 0.0))
            for component in active_components
        )
        (
            pair_state["contestant_active_time_complete"],
            pair_state["contestant_active_time_interpretation"],
        ) = _aggregate_active_time_completeness(active_components)
        if "end_to_end_wall_seconds" in pair_state:
            pair_state["excluded_end_to_end_wall_seconds"] = max(
                0.0,
                float(pair_state["end_to_end_wall_seconds"])
                - float(pair_state["contestant_active_seconds_total"]),
            )
        pair_state["updated_at_utc"] = pair_state["completed_at_utc"]
        tree_scan = self._credential_scan(pair_root)
        pair_state["credential_scan"] = {
            "schema_version": "formalization-terminal-credential-closure-1",
            "passed": True,
            "preseal_tree": tree_scan,
            "prospective_terminal_payloads_scanned": 2,
        }
        report = pair_root / "pair_report.json"
        if report.exists() or report.is_symlink():
            raise BenchmarkError("refusing to replace an existing pair report")
        report_payload = dict(pair_state)
        report_payload.pop("pair_report_sha256", None)
        report_bytes = canonical_json_bytes(report_payload)
        assert_no_credentials_in_bytes(
            [("pair_report.json", report_bytes)], self.deployment.auth_file
        )
        write_json_atomic(report, report_payload, mode=0o400)
        pair_state["pair_report_sha256"] = sha256_file(report)
        state_bytes = canonical_json_bytes(
            {
                **pair_state,
                # _write_state refreshes this field; bind it now so the bytes
                # scanned below are exactly the bytes eventually persisted.
                "updated_at_utc": pair_state["completed_at_utc"],
            }
        )
        assert_no_credentials_in_bytes(
            [("pair_state.json", state_bytes)], self.deployment.auth_file
        )
        _write_state(pair_state_path, pair_state)
        return pair_state

    def _verify_nonterminal_evidence(
        self, pair_root: Path, state: Mapping[str, Any]
    ) -> None:
        """Authenticate durable evidence only after generated trees are bounded."""

        summaries = state.get("conditions")
        if not isinstance(summaries, Mapping):
            raise BenchmarkError("indexed pair has malformed condition summaries")
        for condition, summary in summaries.items():
            if condition not in ("N", "L") or not isinstance(summary, Mapping):
                raise BenchmarkError("indexed pair has an invalid condition summary")
            self._verify_condition_summary(pair_root, condition, summary)
        if state.get("partial_condition_evidence") is not None:
            raise BenchmarkError("nonterminal indexed pair has partial condition evidence")

    def _load_indexed_pair(self, task_id: str) -> tuple[Path, Path, dict[str, Any]] | None:
        index_path = self._index_path(task_id)
        registry_path = self._registry_index_path(task_id)
        if registry_path is not None and registry_path.exists() and not index_path.exists():
            raise BenchmarkError(
                "pilot/task already reserved in the account-global registry"
            )
        if not index_path.exists():
            return None
        if not index_path.is_file() or index_path.is_symlink():
            raise BenchmarkError(f"unsafe task index: {index_path}")
        index = load_json(index_path)
        if (
            index.get("schema_version") != "formalization-task-index-2"
            or index.get("task_id") != task_id
            or any(
                index.get(key) != value
                for key, value in self._index_identity().items()
            )
        ):
            raise BenchmarkError("task index identity mismatch")
        if registry_path is not None:
            if not registry_path.is_file() or registry_path.is_symlink():
                raise BenchmarkError("account-global pilot/task reservation is missing or unsafe")
            if load_json(registry_path) != index:
                raise BenchmarkError("account-global pilot/task reservation differs from index")
        pair_root_raw = index.get("pair_root")
        state_path_raw = index.get("pair_state_path")
        if not isinstance(pair_root_raw, str) or not isinstance(state_path_raw, str):
            raise BenchmarkError("task index paths are malformed")
        pair_root = Path(pair_root_raw).resolve()
        pairs_root = (self.deployment.run_root / "pairs").resolve()
        try:
            pair_root.relative_to(pairs_root)
        except ValueError as error:
            raise BenchmarkError("indexed pair root escapes the run root") from error
        state_path = Path(state_path_raw).resolve()
        if state_path != pair_root / "pair_state.json":
            raise BenchmarkError("indexed pair state path is inconsistent")
        if not state_path.is_file() or state_path.is_symlink():
            raise BenchmarkError("indexed pair state is missing or unsafe")
        state = load_json(state_path)
        if (
            state.get("task_id") != task_id
            or state.get("pilot_id") != self.config["pilot_id"]
            or state.get("run_id") != index.get("run_id")
            or Path(str(state.get("pair_root", ""))).resolve() != pair_root
            or state.get("manifest_sha256") != sha256_file(MANIFEST_PATH)
            or state.get("dry_run") is not False
            or state.get("strict_hardware_enforced") is not True
            or state.get("measurement_admissible") is not True
        ):
            raise BenchmarkError("indexed pair failed its identity or release binding")
        summaries = state.get("conditions")
        if not isinstance(summaries, dict):
            raise BenchmarkError("indexed pair has malformed condition summaries")
        admission = pair_root / "admission.json"
        if (
            not admission.is_file()
            or admission.is_symlink()
            or state.get("admission_sha256") != sha256_file(admission)
        ):
            raise BenchmarkError("indexed pair admission record failed authentication")
        self._verify_qualification_binding(load_json(admission))
        if state.get("status") in {"COMPLETE", "PAIR_INCIDENT"}:
            report = pair_root / "pair_report.json"
            expected_report_sha256 = state.get("pair_report_sha256")
            if (
                not isinstance(expected_report_sha256, str)
                or len(expected_report_sha256) != 64
                or not report.is_file()
                or report.is_symlink()
                or sha256_file(report) != expected_report_sha256
            ):
                raise BenchmarkError("terminal indexed pair report failed authentication")
            self._verify_pair_report(
                report, state, expected_sha256=expected_report_sha256
            )
            self._credential_scan(pair_root)
        return pair_root, state_path, state

    def status(self, task_id: str) -> dict[str, Any]:
        # Full status authentication hashes sealed evidence. Refuse it while a
        # measured pair owns the campaign instead of competing for its CPUs or
        # racing a mutable workspace.
        with self._campaign_lock():
            indexed = self._load_indexed_pair(task_id)
            if indexed is None:
                return {"task_id": task_id, "status": "NOT_STARTED"}
            pair_root, _state_path, state = indexed
            report = pair_root / "pair_report.json"
            if state.get("status") not in TERMINAL_PAIR_STATES and report.exists():
                if not report.is_file() or report.is_symlink():
                    raise BenchmarkError("pair report is unsafe")
                report_sha256 = self._verify_pair_report(
                    report,
                    state,
                    expected_sha256=None,
                    allow_report_ahead=True,
                )
                recovered = load_json(report)
                recovered["pair_report_sha256"] = report_sha256
                return recovered
            return state

    def _continue_pair(
        self,
        *,
        pair_root: Path,
        pair_state_path: Path,
        pair_state: dict[str, Any],
    ) -> dict[str, Any]:
        report = pair_root / "pair_report.json"
        if pair_state.get("status") in {"COMPLETE", "PAIR_INCIDENT"}:
            self._credential_scan(pair_root)
            if not report.exists():
                # Recovery for the former state-first seal order. All condition
                # summaries were already durable before terminal state was written.
                if pair_state.get("pair_report_sha256") is not None:
                    raise BenchmarkError("terminal pair lost its sealed report")
                report_payload = dict(pair_state)
                report_payload.pop("pair_report_sha256", None)
                assert_no_credentials_in_bytes(
                    [("pair_report.json", canonical_json_bytes(report_payload))],
                    self.deployment.auth_file,
                )
                write_json_atomic(report, report_payload, mode=0o400)
            elif not report.is_file() or report.is_symlink():
                raise BenchmarkError("terminal pair report is missing or unsafe")
            actual_report_sha256 = sha256_file(report)
            recorded_report_sha256 = pair_state.get("pair_report_sha256")
            if (
                recorded_report_sha256 is not None
                and recorded_report_sha256 != actual_report_sha256
            ):
                raise BenchmarkError("terminal pair report hash mismatch")
            self._verify_pair_report(
                report, pair_state, expected_sha256=recorded_report_sha256
            )
            pair_state["pair_report_sha256"] = actual_report_sha256
            assert_no_credentials_in_bytes(
                [("pair_state.json", canonical_json_bytes(pair_state))],
                self.deployment.auth_file,
            )
            _write_state(pair_state_path, pair_state)
            return pair_state
        if report.exists():
            if not report.is_file() or report.is_symlink():
                raise BenchmarkError("pair report is unsafe")
            sealed = load_json(report)
            report_sha256 = self._verify_pair_report(
                report,
                pair_state,
                expected_sha256=None,
                allow_report_ahead=True,
            )
            pair_state = sealed
            pair_state["pair_report_sha256"] = report_sha256
            self._credential_scan(pair_root)
            assert_no_credentials_in_bytes(
                [("pair_state.json", canonical_json_bytes(pair_state))],
                self.deployment.auth_file,
            )
            _write_state(pair_state_path, pair_state)
            return pair_state
        if pair_state.get("status") in TERMINAL_PAIR_STATES:
            self._credential_scan(pair_root)
            return pair_state
        task_id = str(pair_state["task_id"])
        paper_path, _packet_path, packet = self._paper_and_packet(task_id)
        recovered_quarantines: dict[str, dict[str, Any]] = {}
        for staged_condition in ("N", "L"):
            quarantine = self._quarantine_workspace_if_unsafe(
                pair_root=pair_root,
                task_id=task_id,
                condition=staged_condition,
                paper_path=paper_path,
                packet=packet,
            )
            if quarantine is not None:
                recovered_quarantines[staged_condition] = quarantine
        self._stage_pair(
            pair_root=pair_root,
            task_id=task_id,
            paper_path=paper_path,
            packet=packet,
        )
        if recovered_quarantines:
            condition = next(iter(recovered_quarantines))
            pair_state["status"] = "PAIR_INCIDENT"
            pair_state["incident"] = {
                "condition": condition,
                "classification": "workspace_quarantined_on_recovery",
                "message": (
                    "An interrupted condition left an unsafe or unbounded generated "
                    "workspace; it was atomically quarantined outside the result closure."
                ),
                "recorded_at_utc": utc_now(),
            }
            condition_state_path = (
                pair_root / "conditions" / condition / "condition_state.json"
            )
            if condition_state_path.is_file() and not condition_state_path.is_symlink():
                recovered = load_json(condition_state_path)
                recovered["status"] = "RULE_VIOLATION"
                recovered["workspace_quarantine"] = recovered_quarantines[condition]
                _write_state(condition_state_path, recovered)
                pair_state["partial_condition_evidence"] = (
                    self._summarize_partial_condition(pair_root, condition, recovered)
                )
                self._verify_partial_condition(
                    pair_root, pair_state["partial_condition_evidence"]
                )
            return self._seal_pair_terminal(
                pair_root=pair_root,
                pair_state_path=pair_state_path,
                pair_state=pair_state,
            )
        self._verify_nonterminal_evidence(pair_root, pair_state)
        self.doctor(task_id)
        if pair_state.get("status") not in {"ADMITTED", "RUNNING"}:
            raise BenchmarkError(
                f"pair was interrupted outside a resumable boundary: {pair_state.get('status')}"
            )
        pair_state["status"] = "RUNNING"
        _write_state(pair_state_path, pair_state)
        for condition in pair_state["condition_order"]:
            summary = pair_state["conditions"].get(condition)
            if isinstance(summary, dict):
                self._verify_condition_summary(pair_root, condition, summary)
                if summary.get("status") in INCIDENT_CONDITION_STATES:
                    pair_state["status"] = "PAIR_INCIDENT"
                    pair_state["incident"] = {
                        "condition": condition,
                        "classification": "sealed_condition_incident",
                        "message": (
                            "Recovered a sealed condition incident before starting "
                            "another condition."
                        ),
                        "recorded_at_utc": utc_now(),
                    }
                    pair_state["credential_scan"] = self._credential_scan(pair_root)
                    return self._seal_pair_terminal(
                        pair_root=pair_root,
                        pair_state_path=pair_state_path,
                        pair_state=pair_state,
                    )
                continue
            try:
                result = self._run_condition(
                    pair_root=pair_root,
                    task_id=task_id,
                    condition=condition,
                    paper_path=paper_path,
                    packet=packet,
                )
            except BenchmarkError as error:
                self._quarantine_workspace_if_unsafe(
                    pair_root=pair_root,
                    task_id=task_id,
                    condition=condition,
                    paper_path=paper_path,
                    packet=packet,
                )
                pair_state["status"] = "PAIR_INCIDENT"
                pair_state["incident"] = {
                    "condition": condition,
                    "classification": "nonresumable_or_infrastructure_failure",
                    "message": str(error),
                    "recorded_at_utc": utc_now(),
                }
                # A teardown failure may occur after the condition state was
                # durably finalized. Preserve and authenticate those measured
                # hours/tokens in the incident instead of dropping them.
                condition_state_path = (
                    pair_root / "conditions" / condition / "condition_state.json"
                )
                if condition_state_path.is_file() and not condition_state_path.is_symlink():
                    recovered = load_json(condition_state_path)
                    if recovered.get("status") in TERMINAL_CONDITION_STATES:
                        try:
                            recovered_summary = self._summarize_condition(
                                pair_root, condition, recovered
                            )
                            self._verify_condition_summary(
                                pair_root, condition, recovered_summary
                            )
                        except BenchmarkError:
                            # A terminal state without an authenticated graceful
                            # app-server shutdown is preserved for accounting but
                            # must never be promoted to a scored condition.
                            pair_state[
                                "partial_condition_evidence"
                            ] = self._summarize_partial_condition(
                                pair_root, condition, recovered
                            )
                            self._verify_partial_condition(
                                pair_root, pair_state["partial_condition_evidence"]
                            )
                        else:
                            pair_state["conditions"][condition] = recovered_summary
                    else:
                        pair_state[
                            "partial_condition_evidence"
                        ] = self._summarize_partial_condition(
                            pair_root, condition, recovered
                        )
                        self._verify_partial_condition(
                            pair_root, pair_state["partial_condition_evidence"]
                        )
                return self._seal_pair_terminal(
                    pair_root=pair_root,
                    pair_state_path=pair_state_path,
                    pair_state=pair_state,
                )
            quarantine = self._quarantine_workspace_if_unsafe(
                pair_root=pair_root,
                task_id=task_id,
                condition=condition,
                paper_path=paper_path,
                packet=packet,
            )
            if quarantine is not None:
                capability_incident = any(
                    attempt.get("incident_classification")
                    == "provider_capability_incompatibility"
                    for attempt in result.get("attempts", [])
                )
                if not capability_incident:
                    result["status"] = "RULE_VIOLATION"
                result["workspace_quarantine"] = quarantine
                _write_state(
                    pair_root / "conditions" / condition / "condition_state.json",
                    result,
                )
            pair_state["conditions"][condition] = self._summarize_condition(
                pair_root, condition, result
            )
            self._verify_condition_summary(
                pair_root, condition, pair_state["conditions"][condition]
            )
            _write_state(pair_state_path, pair_state)
            if result["status"] in INCIDENT_CONDITION_STATES:
                pair_state["status"] = "PAIR_INCIDENT"
                capability_incident = any(
                    attempt.get("incident_classification")
                    == "provider_capability_incompatibility"
                    for attempt in result.get("attempts", [])
                )
                pair_state["incident"] = {
                    "condition": condition,
                    "classification": (
                        "provider_capability_incompatibility"
                        if capability_incident
                        else "sealed_condition_incident"
                    ),
                    "message": "The condition ended in a sealed unscored incident state.",
                    "recorded_at_utc": utc_now(),
                }
                return self._seal_pair_terminal(
                    pair_root=pair_root,
                    pair_state_path=pair_state_path,
                    pair_state=pair_state,
                )
        if set(pair_state["conditions"]) != set(pair_state["condition_order"]):
            raise BenchmarkError("cannot complete a pair without two sealed conditions")
        for condition in pair_state["condition_order"]:
            summary = pair_state["conditions"][condition]
            self._verify_condition_summary(pair_root, condition, summary)
            if summary.get("status") in INCIDENT_CONDITION_STATES:
                raise BenchmarkError("cannot complete a pair containing a condition incident")
        pair_state["status"] = "COMPLETE"
        return self._seal_pair_terminal(
            pair_root=pair_root,
            pair_state_path=pair_state_path,
            pair_state=pair_state,
        )

    def run(self, task_id: str, *, dry_run: bool = False) -> dict[str, Any]:
        if not dry_run and not self.strict_hardware:
            raise BenchmarkError(
                "official measured runs require strict hardware and release enforcement"
            )
        with self._campaign_lock(), _task_lock(
            self.deployment.run_root, task_id
        ):
            if not dry_run:
                self._reconcile_global_reservation(task_id)
            indexed = self._load_indexed_pair(task_id)
            if indexed is not None:
                if dry_run:
                    raise BenchmarkError(
                        "an official pair already exists; use status or live run to resume it"
                    )
                return self._continue_pair(
                    pair_root=indexed[0], pair_state_path=indexed[1], pair_state=indexed[2]
                )
            admission = self.doctor(task_id)
            if not dry_run:
                qualification = self._qualify_provider()
                if qualification.get("status") != "PASSED":
                    raise BenchmarkError("provider qualification did not pass")
                qualification_path = Path(str(qualification.get("record_path", "")))
                if (
                    not qualification_path.is_file()
                    or qualification_path.is_symlink()
                    or qualification.get("record_sha256")
                    != sha256_file(qualification_path)
                ):
                    raise BenchmarkError("provider qualification record failed authentication")
                admission = dict(admission)
                admission["provider_qualification"] = {
                    "record_path": str(qualification_path),
                    "record_sha256": qualification["record_sha256"],
                    "charged_to_contestant": False,
                }
                self._verify_qualification_binding(admission)
            timestamp = time.strftime("%Y%m%dT%H%M%SZ", time.gmtime())
            run_id = f"{task_id}-{timestamp}-{secrets.token_hex(4)}"
            root_kind = "preflights" if dry_run else "pairs"
            pair_root = self.deployment.run_root / root_kind / run_id
            pair_root.mkdir(parents=True, mode=0o700)
            paper_path, packet_path, packet = self._paper_and_packet(task_id)
            order = admission["condition_order"]
            pair_state_path = pair_root / "pair_state.json"
            pair_state = {
                "schema_version": "formalization-pair-state-1",
                "pilot_id": self.config["pilot_id"],
                "run_id": run_id,
                "task_id": task_id,
                "pair_root": str(pair_root),
                "pair_state_path": str(pair_state_path),
                "status": "ADMITTED",
                "condition_order": order,
                "conditions": {},
                "created_at_utc": utc_now(),
                "created_unix_ns": time.time_ns(),
                "manifest_sha256": sha256_file(MANIFEST_PATH),
                "admission_sha256": None,
                "dry_run": dry_run,
                "strict_hardware_enforced": self.strict_hardware,
                "measurement_admissible": bool(not dry_run and self.strict_hardware),
            }
            write_json_atomic(pair_root / "admission.json", admission, mode=0o400)
            pair_state["admission_sha256"] = sha256_file(pair_root / "admission.json")
            _write_state(pair_state_path, pair_state)
            self._stage_pair(
                pair_root=pair_root,
                task_id=task_id,
                paper_path=paper_path,
                packet=packet,
            )

            if dry_run:
                pair_state["status"] = "DRY_RUN_COMPLETE"
                pair_state["staging_sha256"] = sha256_file(pair_root / "pair_staging.json")
                completed_unix_ns = time.time_ns()
                pair_state["completed_at_utc"] = utc_now()
                pair_state["completed_unix_ns"] = completed_unix_ns
                pair_state["end_to_end_wall_seconds"] = (
                    completed_unix_ns - int(pair_state["created_unix_ns"])
                ) / 1_000_000_000
                pair_state["contestant_active_seconds_total"] = 0.0
                pair_state["contestant_active_time_complete"] = True
                pair_state["contestant_active_time_interpretation"] = "exact"
                pair_state["excluded_end_to_end_wall_seconds"] = pair_state[
                    "end_to_end_wall_seconds"
                ]
                pair_state["updated_at_utc"] = pair_state["completed_at_utc"]
                pair_state["credential_scan"] = {
                    "schema_version": "formalization-terminal-credential-closure-1",
                    "passed": True,
                    "preseal_tree": self._credential_scan(pair_root),
                    "prospective_terminal_payloads_scanned": 1,
                }
                assert_no_credentials_in_bytes(
                    [("pair_state.json", canonical_json_bytes(pair_state))],
                    self.deployment.auth_file,
                )
                _write_state(pair_state_path, pair_state)
                return pair_state
            index_path = self._index_path(task_id)
            index_path.parent.mkdir(parents=True, exist_ok=True)
            if index_path.exists():
                raise BenchmarkError("task index appeared during locked pair creation")
            index = {
                "schema_version": "formalization-task-index-2",
                **self._index_identity(),
                "task_id": task_id,
                "run_id": run_id,
                "pair_root": str(pair_root),
                "pair_state_path": str(pair_state_path),
            }
            registry_path = self._registry_index_path(task_id)
            if registry_path is not None:
                registry_path.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
                if registry_path.parent.is_symlink() or registry_path.exists():
                    raise BenchmarkError("pilot/task already reserved in the account-global registry")
                write_json_atomic(registry_path, index, mode=0o600)
            write_json_atomic(
                index_path,
                index,
                mode=0o600,
            )
            return self._continue_pair(
                pair_root=pair_root,
                pair_state_path=pair_state_path,
                pair_state=pair_state,
            )
