from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import platform
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

from common import BenchmarkToolError, read_json, sha256_file, write_json  # noqa: E402
from hashes import create_manifest, stage_manifest_files  # noqa: E402
import run_matrix  # noqa: E402
import run_token_control_canary as token_canary  # noqa: E402
import refresh_snapshot  # noqa: E402


LEAN_COMMIT = "1" * 40
MATHLIB_COMMIT = "2" * 40
NUMSTABILITY_COMMIT = "3" * 40
P01_PAPER_SHA256 = "4" * 64
P02_PAPER_SHA256 = "5" * 64


def _valid_sse_call_fixture(*, content_type_present: bool = True) -> dict[str, object]:
    response_id = "response-fixture"
    body_sha256 = "6" * 64
    return {
        "upstream_status": 200,
        "upstream_content_type": (
            "text/event-stream; charset=\"utf-8\"" if content_type_present else None
        ),
        "upstream_content_type_occurrences": 1 if content_type_present else 0,
        "upstream_content_encoding": None,
        "upstream_content_encoding_occurrences": 0,
        "upstream_body_sha256": body_sha256,
        "upstream_body_bytes": 123,
        "response_id": response_id,
        "upstream_sse_authentication": {
            "schema_version": 1,
            "protocol": run_matrix.ultra_canary.runner.PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT[
                "protocol"
            ],
            "parser": run_matrix.ultra_canary.runner.PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT[
                "parser"
            ],
            "complete": True,
            "content_type_basis": (
                "declared_text_event_stream"
                if content_type_present
                else "authenticated_stream_request_header_absent"
            ),
            "content_encoding_basis": "implicit_identity_header_absent",
            "json_event_count": 2,
            "completed_event_index": 1,
            "done_count": 1,
            "body_sha256": body_sha256,
            "body_bytes": 123,
            "response_id": response_id,
            "downstream_content_type_synthesized": not content_type_present,
        },
    }


def _production_components_fixture() -> dict[str, str]:
    return {
        field: format(index, "064x")
        for index, field in enumerate(
            run_matrix.EXECUTION_COMPONENT_FIELDS, start=1
        )
    }


def _exact_nested_submission_boundary_fixture() -> dict[str, object]:
    return {
        "schema_version": run_matrix.ultra_canary.codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
        "submission_transport": run_matrix.ultra_canary.codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT,
        "candidate_path": "Candidate.lean",
        "call_id": "inner-submit-call",
        "inner_dynamic_call_id": "inner-submit-call",
        "inner_dynamic_tool_name": "submit_proof",
        "inner_dynamic_arguments": {"candidate_path": "Candidate.lean"},
        "outer_raw_item_id": "outer-raw-item",
        "outer_raw_item_type": "custom_tool_call",
        "outer_exec_name": "exec",
        "outer_exec_call_id": "outer-exec-call",
        "outer_exec_program": run_matrix.ultra_canary.codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE,
        "outer_exec_program_bytes": run_matrix.ultra_canary.codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_BYTES,
        "outer_exec_program_sha256": run_matrix.ultra_canary.codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_SHA256,
        **run_matrix.ultra_canary.codex_isolated.nested_submission_exec_yield_record(),
        "outer_raw_item_observed_at_monotonic_ns": 8,
        "inner_dynamic_item_started_at_monotonic_ns": 9,
        "outer_raw_item_observed_before_inner_dynamic_call": True,
        "submission_event_order": (
            run_matrix.ultra_canary.codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
        ),
        "dynamic_call_observed_before_raw_response_completed": True,
        "raw_response_completed_before_dynamic_call_observed": False,
        "raw_response_completed_before_boundary_publication": True,
        "sequence": 1,
        "jsonrpc_request_id": 7,
        "thread_id": "root",
        "turn_id": "root-turn",
        "response_id": "submit-response",
        "raw_response_notification_sequence": 1,
        "candidate_sha256": "a" * 64,
        "candidate_size_bytes": 64,
        "request_published_at_monotonic_ns": 30,
        "sole_model_tool_call_in_response": True,
        "outer_exec_final_raw_item": True,
        "inner_dynamic_call_observed": True,
        "inner_dynamic_item_started": True,
        "inner_submit_invocation_exact": True,
        "inner_submit_only_nested_tool_call": True,
        "inner_dynamic_call_left_blocked": True,
        "inner_dynamic_tool_response_sent": False,
        "outer_exec_output_emitted": False,
        "provider_gate_close": {
            "won": True,
            "requested_reason": "accepted_submission",
            "effective_reason": "accepted_submission",
            "phase": "CLOSED",
            "sequence": 7,
        },
    }


def _seal_retained_request(
    root: Path,
    boundary: dict[str, object],
    *,
    label: str,
) -> dict[str, object]:
    dynamic_before = boundary[
        "dynamic_call_observed_before_raw_response_completed"
    ]
    captured_ns = 10 if dynamic_before is True else 20
    response_ns = 20 if dynamic_before is True else 10
    request = {
        **boundary,
        "kind": "highambench_submission_request",
        "captured_at_monotonic_ns": captured_ns,
        "raw_response_observed_at_monotonic_ns": response_ns,
    }
    for field in (
        "authenticated",
        "status",
        "exact",
        "inner_dynamic_call_left_blocked",
        "inner_dynamic_tool_response_sent",
        "outer_exec_output_emitted",
        "later_model_response_possible",
        "provider_gate_close",
    ):
        request.pop(field, None)
    authenticated = run_matrix.ultra_canary.codex_isolated.authenticated_record(
        request, "request_sha256"
    )
    boundary["request_sha256"] = authenticated["request_sha256"]
    path = (root / f"{label}.submission-request.json").resolve()
    write_json(path, authenticated)
    path.chmod(0o444)
    return {
        "verified": True,
        "artifacts": {
            "request": {
                "path": str(path),
                "record_sha256": authenticated["request_sha256"],
                "file_sha256": run_matrix.sha256_file(path),
            }
        },
    }


def _allocation_host_class() -> dict[str, object]:
    return {
        "kernel": "Linux fixture x86_64",
        "virtualization": "NONE",
        "cpu_vendor": "GenuineIntel",
        "cpu_family": 6,
        "cpu_model": 143,
        "cpu_stepping": 8,
        "processor": "Intel(R) Xeon(R) Gold 6448H",
        "online_logical_cpus": 4,
        "allocated_physical_cores": 2,
        "allocated_sockets": 1,
        "allocated_threads_per_core": [2, 2],
        "visible_memory_bytes": 512 * 1024**3,
        "allocation_memory_limit_bytes": 32 * 1024**3,
        "slurm_num_nodes": 1,
        "slurm_num_cpus": 4,
        "slurm_num_tasks": 1,
        "slurm_cpus_per_task": 4,
        "slurm_allocated_memory_bytes": 32 * 1024**3,
    }


def _allocation_freeze_check() -> dict[str, object]:
    return {
        "schema_version": 1,
        "kind": "highambench-frozen-run-verification",
        "ok": True,
        "environment_id": "highambench-fixture-0123456789abcdef",
        "environment_bundle_sha256": "a" * 64,
        "release_manifest": {"sha256": "b" * 64},
        "host_class": _allocation_host_class(),
        "agent": {
            "id": "codex-cli",
            "version": "1.2.3",
            "binary_sha256": "c" * 64,
            "model": "gpt-5.6-sol",
            "reasoning_effort": "ultra",
        },
        "limits": {
            "wall_clock_seconds": 1800,
            "total_model_tokens": 5_000_000,
            "prompt_startup_timeout_seconds": 120.0,
            "post_submission_validation_reserve_seconds": 369.0,
        },
    }


def _scheduler_sharing() -> dict[str, object]:
    return {
        "partition": "KFOUNTOU",
        "job_oversubscribe": "OK",
        "partition_oversubscribe": "FORCE:1",
        "node_list": "watgpu108",
        "exclusive": False,
        "sharing_policy": "partition_forced_oversubscription",
        "dynamic_co_tenant_count_recorded": False,
    }


def _slurm_gpu_provenance() -> dict[str, object]:
    return {
        "alloc_tres": "billing=4,cpu=4,mem=32G,node=1",
        "allocated_gpu_count": 0,
        "gpu_environment": {
            "SLURM_GPUS_ON_NODE": None,
            "SLURM_JOB_GPUS": None,
            "CUDA_VISIBLE_DEVICES": None,
        },
    }


def _assignment_fixture(
    *,
    condition: str = "N",
    run_id: str | None = None,
    order_index: int | None = None,
) -> dict[str, object]:
    if run_id is None:
        run_id = f"P01-T1-rep-01-{condition}"
    if order_index is None:
        order_index = 1 if condition == "N" else 2
    return {
        "task_id": "P01-T1",
        "paper_id": "P01",
        "paper_sha256": P01_PAPER_SHA256,
        "tier": "T1",
        "pair_id": "P01-T1-rep-01",
        "repetition_id": "rep-01",
        "condition": condition,
        "condition_order": ["N", "L"],
        "order_index": order_index,
        "run_id": run_id,
    }


def _historical_allocation_descriptor(
    results: Path,
    freeze: dict[str, object],
    *,
    job_id: str = "1505507",
) -> dict[str, str]:
    record = run_matrix._allocation_hardware_record_payload(
        freeze,
        job_id=job_id,
        hostname="watgpu108",
        cpu_affinity_logical_cpus=[8, 9, 56, 57],
        scheduler_sharing=_scheduler_sharing(),
        slurm_gpu_provenance=_slurm_gpu_provenance(),
    )
    record["record_sha256"] = run_matrix.allocation_hardware_record_digest(record)
    path = results / "allocation_hardware" / f"slurm-{job_id}.json"
    write_json(path, record)
    return run_matrix._allocation_hardware_descriptor(results, path, record)


def _sealed_final_record(
    assignment: dict[str, object],
    freeze: dict[str, object],
    allocation: dict[str, str],
    *,
    attempt: int = 1,
    passed: bool = False,
) -> dict[str, object]:
    identity = run_matrix._planned_assignment_record_identity(assignment)
    if passed:
        usage: dict[str, object] = {
            "usage_scope": "rooted_attempt_thread_tree_completed_responses",
            "measurement_exact": True,
            "submission_boundary_exact": True,
            "submission_boundary": {
                **_exact_nested_submission_boundary_fixture(),
                "authenticated": True,
                "status": "accepted",
                "exact": True,
                "root_only": True,
                "descendants_quiescent": True,
                "later_model_response_possible": False,
            },
            "drain_complete": False,
            "tree_quiescent": False,
            "stop_reason": "first_valid_proof",
            "root_thread_id": "root",
            "active_thread_ids": ["root"],
            "unresolved_thread_ids": [],
            "invalid_reasons": [],
        }
        boundary: dict[str, object] = {"verified": True}
        failure_code = None
    else:
        usage = {
            "usage_scope": "rooted_attempt_thread_tree_completed_responses",
            "measurement_exact": True,
            "submission_boundary_exact": False,
            "submission_boundary": None,
            "drain_complete": True,
            "tree_quiescent": True,
            "active_thread_ids": [],
            "unresolved_thread_ids": [],
            "invalid_reasons": [],
        }
        boundary = {"verified": False}
        failure_code = "NO_SUBMISSION"
    record: dict[str, object] = {
        "schema_version": 1,
        "kind": "highambench-run",
        **identity,
        "agent": {
            key: freeze["agent"][key]
            for key in ("id", "version", "model", "reasoning_effort")
        },
        "environment_id": freeze["environment_id"],
        "frozen_run_verification": {
            "freeze_check_sha256": run_matrix.canonical_document_digest(freeze),
            "freeze_check": json.loads(json.dumps(freeze)),
        },
        "limits": {
            "time_seconds": freeze["limits"]["wall_clock_seconds"],
            "model_tokens": freeze["limits"]["total_model_tokens"],
            "prompt_startup_seconds": freeze["limits"][
                "prompt_startup_timeout_seconds"
            ],
            "post_acceptance_usage_grace_seconds": 2.0,
        },
        "allocation_hardware": allocation,
        "matrix_attempt": attempt,
        "useful_work_started": True,
        "agent_exit_code": 0,
        "pass": passed,
        "scored": True,
        "protocol": {"complete": True},
        "failure_code": failure_code,
        "token_usage": usage,
        "ultra_submission_boundary": boundary,
    }
    run_matrix._bind_matrix_record_sha256(record)
    return record


def _ultra_projection_fixture() -> dict[str, object]:
    baseline = {"total_tokens": 132}
    projected = {"total_tokens": 239}
    allowed_id = "call_allowed_root"
    blocked_ids = ["call_blocked_child", "call_blocked_root"]
    policy_static = run_matrix.ultra_canary.codex_isolated.ultra_fork_policy_static_record()

    def call_evidence(
        call_id: str,
        *,
        parent: str,
        turn_id: str,
        response_id: str,
        allowed: bool,
    ) -> dict[str, object]:
        return {
            "call_id": call_id,
            "parent_thread_id": parent,
            "parent_turn_id": turn_id,
            "parent_response_id": response_id,
            "fork_turns": "all" if allowed else "3",
            "fork_semantics": (
                "full_history_parent_pre_response"
                if allowed
                else "unsupported_positive_turn_suffix"
            ),
            "hook_run_id": f"pre-tool-use:0:{policy_static['source_path']}:{call_id}",
            "hook_source_path": policy_static["source_path"],
            "hook_thread_id": parent,
            "hook_turn_id": turn_id,
            "hook_started_observed": True,
            "hook_started_count": 1,
            "hook_completed_observed": True,
            "hook_completed_count": 1,
            "hook_status": (
                run_matrix.ultra_canary.codex_isolated.ULTRA_FORK_POLICY_ALLOW_STATUS
                if allowed
                else run_matrix.ultra_canary.codex_isolated.ULTRA_FORK_POLICY_BLOCK_STATUS
            ),
            "decision": (
                run_matrix.ultra_canary.codex_isolated.ULTRA_FORK_POLICY_ALLOW_DECISION
                if allowed
                else run_matrix.ultra_canary.codex_isolated.ULTRA_FORK_POLICY_BLOCK_DECISION
            ),
            "feedback": (
                None
                if allowed
                else run_matrix.ultra_canary.codex_isolated.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
                    call_id=call_id
                )
            ),
            "resolution_status": (
                "resolved_child"
                if allowed
                else run_matrix.ultra_canary.codex_isolated.ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS
            ),
            "child_activity_observed": allowed,
        }

    policy = {
        **policy_static,
        "call_evidence": [
            call_evidence(
                allowed_id,
                parent="root",
                turn_id="root-turn",
                response_id="root-spawn-response",
                allowed=True,
            ),
            call_evidence(
                "call_blocked_child",
                parent="child-0",
                turn_id="child-turn-0",
                response_id="child-blocked-response",
                allowed=False,
            ),
            call_evidence(
                "call_blocked_root",
                parent="root",
                turn_id="root-turn",
                response_id="root-blocked-response",
                allowed=False,
            ),
        ],
        "complete": True,
    }
    appserver_usage = {
        "input_tokens": 20,
        "cached_input_tokens": 0,
        "cache_write_input_tokens": 0,
        "output_tokens": 1,
        "reasoning_output_tokens": 0,
        "total_tokens": 21,
    }
    suppressed_usage = {
        "input_tokens": 10,
        "cached_input_tokens": 0,
        "cache_write_input_tokens": 0,
        "output_tokens": 1,
        "reasoning_output_tokens": 0,
        "total_tokens": 11,
    }
    reconciliation = {
        "schema_version": 3,
        "provider_response_count": 2,
        "appserver_response_count": 1,
        "suppressed_collaboration_wait_response_count": 1,
        "provider_usage": {
            field: appserver_usage[field] + suppressed_usage[field]
            for field in appserver_usage
        },
        "appserver_usage": appserver_usage,
        "suppressed_collaboration_wait_usage": suppressed_usage,
        "provider_response_ids": ["suppressed-wait-response", "accepted-response"],
        "appserver_response_ids": ["accepted-response"],
        "suppressed_collaboration_wait_response_ids": ["suppressed-wait-response"],
        "suppressed_collaboration_wait_evidence": [
            {
                "response_id": "suppressed-wait-response",
                "provider_call_id": "provider-wait-call",
                "thread_id": "root",
                "turn_id": "root-turn",
                "successor_response_id": "accepted-response",
                "successor_call_id": "provider-accepted-call",
                "agent_message_item_id": "child-result-message",
                "agent_message_sha256": "a" * 64,
                "agent_message_author": "child-0",
                "agent_message_recipient": "/root",
                "agent_message_observed_at_unix_ns": 2,
                "agent_message_observed_at_monotonic_ns": 1,
            }
        ],
        "superseded_by_collaboration_message_response_count": 0,
        "superseded_by_collaboration_message_usage": {
            field: 0 for field in appserver_usage
        },
        "superseded_by_collaboration_message_response_ids": [],
        "superseded_by_collaboration_message_evidence": [],
        "discarded_after_explicit_child_interrupt_response_count": 0,
        "discarded_after_explicit_child_interrupt_usage": {
            field: 0 for field in appserver_usage
        },
        "discarded_after_explicit_child_interrupt_response_ids": [],
        "discarded_after_explicit_child_interrupt_evidence": [],
    }
    projection: dict[str, object] = {
        "accounting_projection_schema_version": (
            run_matrix.ultra_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "provider_gate_protocol": run_matrix.ultra_canary.runner.PROVIDER_GATE_PROTOCOL,
        "provider_gate_record_sha256": "f" * 64,
        "provider_gate_close_reason": "accepted_submission",
        "provider_gate_response_ids": reconciliation["provider_response_ids"],
        "provider_gate_deliveries_reconciled": True,
        "provider_usage_reconciliation": reconciliation,
        "provider_gate_setup_requests_empty": True,
        "provider_requests_quiescent": True,
        "adapter_teardown_complete": True,
        "spawn_binding_source": run_matrix.ultra_canary.SPAWN_BINDING_SOURCE,
        "raw_spawn_call_ids": [allowed_id, *blocked_ids],
        "activity_spawn_call_ids": [allowed_id],
        "collab_spawn_call_ids": [],
        "resolved_spawn_call_ids": [allowed_id],
        "failed_spawn_call_ids": blocked_ids,
        "policy_blocked_spawn_call_ids": blocked_ids,
        "unresolved_spawn_call_ids": [],
        "unsupported_spawn_call_ids": [],
        "inference_child_thread_ids": ["child-0"],
        "hook_observed_spawn_call_ids": [allowed_id, *blocked_ids],
        "hook_allowed_spawn_call_ids": [allowed_id],
        "hook_blocked_spawn_call_ids": blocked_ids,
        "hook_invalid_spawn_call_ids": [],
        "spawn_parent_response_ids": {allowed_id: "root-spawn-response"},
        "pre_spawn_completed_root_response_counts": {allowed_id: 2},
        "raw_call_activity_id_match": True,
        "completed_root_response_before_spawn": True,
        "fork_turns_all_child_thread_count": 1,
        "nonzero_inherited_baseline_child_thread_ids": ["child-0"],
        "spawn_linkage_complete": True,
        "descendant_accounting_complete": True,
        "cumulative_projection_complete": True,
        "fork_policy_complete": True,
        "accounting_complete": True,
        "fork_policy": policy,
        "thread_accounting": [
            {
                "thread_id": "child-0",
                "parent_thread_id": "root",
                "agent_path": "/root/child-0",
                "spawn_call_id": allowed_id,
                "spawn_parent_response_id": "root-spawn-response",
                "spawn_fork_turns": "all",
                "spawn_binding_status": "resolved",
                "expected_cumulative_baseline": baseline,
                "cumulative_projection_status": "matched_full_projection",
                "cumulative_projection_match": True,
                "last_cumulative": projected,
                "expected_cumulative_projection": projected,
                "accounting_complete": True,
            },
            {
                "thread_id": "root",
                "parent_thread_id": None,
                "agent_path": "/root",
                "spawn_binding_status": "root_zero",
                "expected_cumulative_baseline": {"total_tokens": 0},
                "accounting_complete": True,
            },
        ],
    }
    projection["projection_payload_sha256"] = (
        run_matrix.canonical_document_digest(projection)
    )
    return projection


def _token_projection_fixture() -> dict[str, object]:
    provider_usage = {
        "input_tokens": 180_000,
        "cached_input_tokens": 0,
        "cache_write_input_tokens": 0,
        "output_tokens": 1,
        "reasoning_output_tokens": 0,
        "total_tokens": 180_001,
    }
    response_ids = ["initial-response", "crossing-response"]
    projection: dict[str, object] = {
        "accounting_projection_schema_version": (
            token_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "provider_gate_protocol": token_canary.runner.PROVIDER_GATE_PROTOCOL,
        "provider_gate_record_sha256": "e" * 64,
        "provider_gate_close_reason": "token_limit",
        "provider_gate_response_ids": response_ids,
        "provider_gate_deliveries_reconciled": True,
        "provider_usage_reconciliation": {
            "schema_version": 3,
            "provider_response_count": 2,
            "appserver_response_count": 2,
            "suppressed_collaboration_wait_response_count": 0,
            "provider_usage": provider_usage,
            "appserver_usage": provider_usage,
            "suppressed_collaboration_wait_usage": {
                field: 0 for field in provider_usage
            },
            "provider_response_ids": response_ids,
            "appserver_response_ids": response_ids,
            "suppressed_collaboration_wait_response_ids": [],
            "suppressed_collaboration_wait_evidence": [],
            "superseded_by_collaboration_message_response_count": 0,
            "superseded_by_collaboration_message_usage": {
                "input_tokens": 0,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 0,
                "reasoning_output_tokens": 0,
                "total_tokens": 0,
            },
            "superseded_by_collaboration_message_response_ids": [],
            "superseded_by_collaboration_message_evidence": [],
            "discarded_after_explicit_child_interrupt_response_count": 0,
            "discarded_after_explicit_child_interrupt_usage": {
                field: 0 for field in provider_usage
            },
            "discarded_after_explicit_child_interrupt_response_ids": [],
            "discarded_after_explicit_child_interrupt_evidence": [],
        },
        "provider_gate_setup_requests_empty": True,
        "provider_requests_quiescent": True,
        "adapter_teardown_complete": True,
        "spawn_binding_source": token_canary.SPAWN_BINDING_SOURCE,
        "root_thread_id": "synthetic-root",
        "root_expected_cumulative_baseline": {
            "input_tokens": 0,
            "cached_input_tokens": 0,
            "cache_write_input_tokens": 0,
            "output_tokens": 0,
            "reasoning_output_tokens": 0,
            "total_tokens": 0,
        },
        "root_cumulative_projection_status": "cumulative_projection_mismatch",
        "spawn_linkage_complete": True,
        "descendant_accounting_complete": True,
        "cumulative_projection_complete": False,
        "raw_spawn_call_ids": [],
        "activity_spawn_call_ids": [],
        "collab_spawn_call_ids": [],
        "resolved_spawn_call_ids": [],
        "failed_spawn_call_ids": [],
        "policy_blocked_spawn_call_ids": [],
        "unresolved_spawn_call_ids": [],
        "unsupported_spawn_call_ids": [],
        "inference_child_thread_ids": [],
        "hook_observed_spawn_call_ids": [],
        "hook_allowed_spawn_call_ids": [],
        "hook_blocked_spawn_call_ids": [],
        "hook_invalid_spawn_call_ids": [],
        "fork_policy_complete": True,
        "fork_policy": {
            **token_canary.codex_isolated.ultra_fork_policy_static_record(),
            "call_evidence": [],
            "complete": True,
        },
        "accounting_complete": False,
        "root_only": True,
    }
    projection["projection_payload_sha256"] = (
        run_matrix.canonical_document_digest(projection)
    )
    return projection


def _token_prompt_release_fixture() -> dict[str, object]:
    released = 1_000_000_000
    wall = 300
    return {
        "schema_version": 1,
        "protocol_version": "highambench-prompt-release-v1",
        "status": "released_authenticated",
        "authenticated": True,
        "timing_exact": True,
        "useful_work_basis": "authenticated_release",
        "startup_timeout_seconds": 120.0,
        "startup_timeout_triggered": False,
        "go_minimum_release_window_seconds": 5.0,
        "artifact_content_verified": True,
        "artifact_count": 3,
        "artifacts": {
            label: {
                "path": f"/trusted/logs/token.prompt-{label}.json",
                "file_sha256": character * 64,
                "record_sha256": character * 64,
            }
            for label, character in (("ready", "1"), ("go", "2"), ("release", "3"))
        },
        "canonical_encoding": "compact_sorted_key_utf8_json_newline",
        "sealed_mode": "0444",
        "handshake_nonce": "4" * 64,
        "root_thread_id": "synthetic-root",
        "effective_prompt_sha256": "5" * 64,
        "effective_prompt_bytes": 123,
        "turn_start_request_sha256": "6" * 64,
        "turn_start_wire_verified": True,
        "command_binding_verified": True,
        "root_identity_verified": True,
        "ready_sha256": "7" * 64,
        "go_sha256": "8" * 64,
        "release_sha256": "9" * 64,
        "measurement_time_origin": "RELEASED.released_at_monotonic_ns",
        "released_at_monotonic_ns": released,
        "deadline_monotonic_ns": released + wall * 1_000_000_000,
        "deadline_derivation": (
            "released_at_monotonic_ns + wall_time_seconds*1000000000"
        ),
        "wall_time_seconds": wall,
        "actual_stop_seconds": 10.0,
        "token_crossing_within_deadline": True,
        "first_valid_seconds": None,
        "submission_boundary": None,
        "sanitized_provider_gate_crossing": True,
        "top_level_artifact_count_unchanged": len(token_canary.ARTIFACT_LABELS),
    }


def _token_canary_summary_fixture() -> dict[str, object]:
    crossing = token_canary.DEFAULT_CANARY_TOKEN_LIMIT + 1
    return {
        "status": "passed",
        "canary_limit_tokens": token_canary.DEFAULT_CANARY_TOKEN_LIMIT,
        "first_crossing_tokens": crossing,
        "final_endpoint_tokens": crossing,
        "thread_count": 1,
        "observed_child_thread_count": 0,
        "response_count": 2,
        "drain_complete": False,
        "provider_gate_quiescent": True,
        "measurement_exact": True,
        "synthetic_input": True,
        "matrix_assignment": False,
        "benchmark_task_bytes_used": False,
        "prompt_protocol": token_canary.PROMPT_PROTOCOL,
        "prompt_release": _token_prompt_release_fixture(),
        "source_separation_audit_sha256": "a" * 64,
        "accounting_projection": _token_projection_fixture(),
        "artifacts": {
            label: {
                "path": f"artifacts/{label}.json",
                "sha256": "b" * 64,
                "bytes": 1,
            }
            for label in token_canary.ARTIFACT_LABELS
        },
    }


def _ultra_prompt_release_fixture(*, wall_time_seconds: int = 300) -> dict[str, object]:
    released = 1_000_000_000
    return {
        "schema_version": 1,
        "protocol_version": "highambench-prompt-release-v1",
        "authenticated": True,
        "timing_exact": True,
        "elapsed_clock": "CLOCK_MONOTONIC",
        "startup_timeout_seconds": 120,
        "artifact_count": 3,
        "artifacts_reauthenticated": True,
        "released_at_monotonic_ns": released,
        "measurement_deadline_monotonic_ns": (
            released + wall_time_seconds * 1_000_000_000
        ),
        "request_published_at_monotonic_ns": released + 1_000_000,
        "request_publication_timing_verified": True,
    }


def _ultra_canary_summary_fixture(
    *,
    descriptor_sha256: str,
    projection: dict[str, object],
    wall_time_seconds: int = 300,
) -> dict[str, object]:
    return {
        "path": run_matrix.FROZEN_ULTRA_CANARY_PATH,
        "sha256": descriptor_sha256,
        "status": "passed",
        "thread_count": 2,
        "observed_descendant_thread_count": 1,
        "positive_usage_descendant_thread_count": 1,
        "response_count": 2,
        "drain_complete": False,
        "measurement_exact": True,
        "submission_boundary_exact": True,
        "barrier": {
            **_exact_nested_submission_boundary_fixture(),
            "outer_raw_item_observed_at_monotonic_ns": 1_000_100_000,
            "inner_dynamic_item_started_at_monotonic_ns": 1_000_200_000,
            "captured_at_monotonic_ns": 1_000_300_000,
            "raw_response_observed_at_monotonic_ns": 1_000_400_000,
            "request_published_at_monotonic_ns": 1_001_000_000,
            "retained_read_only": True,
        },
        "accounting_projection": projection,
        "prompt_release": _ultra_prompt_release_fixture(
            wall_time_seconds=wall_time_seconds
        ),
        "dependency_audit": {
            "complete": True,
            "helper_sha256": "c" * 64,
            "command_sha256": "d" * 64,
            "library_use": False,
            "library_declarations": [],
            "target_seen": True,
            "semantic_type_equal": True,
        },
        "artifacts": {
            label: {
                "path": f"artifacts/{label}.json",
                "sha256": "e" * 64,
                "bytes": 1,
            }
            for label in run_matrix.ultra_canary.ARTIFACT_LABELS
        },
    }


def _executable(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text, encoding="utf-8")
    path.chmod(path.stat().st_mode | stat.S_IXUSR)


def _write_two_paper_task_records(root: Path) -> list[str]:
    shared_files = [
        {
            "path": "paper_bencmark/highambench/shared/HighamBench/Core.lean",
            "paper_ids": ["P01", "P02"],
            "sha256": "6" * 64,
        },
        {
            "path": "paper_bencmark/highambench/shared/HighamBench/P01Definitions.lean",
            "paper_ids": ["P01"],
            "sha256": "7" * 64,
        },
        {
            "path": "paper_bencmark/highambench/shared/HighamBench/P02Definitions.lean",
            "paper_ids": ["P02"],
            "sha256": "8" * 64,
        },
    ]
    papers = []
    task_ids: list[str] = []
    for paper_id, paper_sha256 in (
        ("P01", P01_PAPER_SHA256),
        ("P02", P02_PAPER_SHA256),
    ):
        targets = []
        included_tasks = []
        for tier in ("T1", "T2", "T3"):
            task_id = f"{paper_id}-{tier}"
            theorem_name = f"{paper_id.lower()}_{tier.lower()}_fixture"
            target_dir = root / "tasks" / paper_id / tier
            target_dir.mkdir(parents=True, exist_ok=True)
            (target_dir / "Target.lean").write_text(
                f"theorem {theorem_name} : True := by trivial\n", encoding="utf-8"
            )
            (target_dir / "context.md").write_text("fixture context\n", encoding="utf-8")
            declared_target = (
                f"paper_bencmark/highambench/tasks/{paper_id}/{tier}/Target.lean"
            )
            write_json(
                target_dir / "task.json",
                {
                    "schema_version": "highambench-task-0.3",
                    "task_id": task_id,
                    "paper_id": paper_id,
                    "tier": tier,
                    "source_tags": ["EQN"],
                    "author_label": None,
                    "classification_frozen_before_runs": True,
                    "source_locations": [{"anchor": "equation (1.1)"}],
                    "paper_source": {"sha256": paper_sha256},
                    "context_file": (
                        f"paper_bencmark/highambench/tasks/{paper_id}/{tier}/context.md"
                    ),
                    "formal_statement": {
                        "namespace": "HighamBench",
                        "theorem_name": theorem_name,
                        "target_file": declared_target,
                    },
                    "validation": {
                        "required_declaration": f"HighamBench.{theorem_name}",
                        "controlled_target_file": declared_target,
                    },
                },
            )
            controlled = root / "metadata" / "controlled" / f"{task_id}.json"
            controlled.parent.mkdir(parents=True, exist_ok=True)
            write_json(controlled, {"task_id": task_id})
            targets.append(
                {
                    "task_id": task_id,
                    "tier": tier,
                    "availability": "available",
                    "lean_target": {
                        "declaration": theorem_name,
                        "file": declared_target,
                        "shared_files": [
                            "paper_bencmark/highambench/shared/HighamBench/Core.lean",
                            (
                                "paper_bencmark/highambench/shared/HighamBench/"
                                f"{paper_id}Definitions.lean"
                            ),
                        ],
                    },
                }
            )
            included_tasks.append(task_id)
            task_ids.append(task_id)
        write_json(
            root / "tasks" / paper_id / "paper.json",
            {
                "paper_id": paper_id,
                "source": {"sha256": paper_sha256},
                "included_tasks": included_tasks,
            },
        )
        papers.append(
            {
                "paper_id": paper_id,
                "source": {"sha256": paper_sha256},
                "targets": targets,
            }
        )
    write_json(
        root / "metadata" / "manifest.json",
        {
            "benchmark_id": "two-paper-fixture",
            "corpus": {"paper_count": 2, "paper_ids": ["P01", "P02"]},
            "controlled_shared_files": shared_files,
            "papers": papers,
        },
    )
    return task_ids


class FrozenEnvironmentFixture:
    def __init__(self, parent: Path) -> None:
        self.project = parent / "project"
        self.root = self.project / "paper_bencmark" / "highambench"
        self.metadata = self.root / "metadata"
        self.toolchain = parent / "toolchain"
        self.packages = self.project / ".lake" / "packages"
        self.packages_runtime = parent / "packages-runtime"
        self.library_olean = parent / "library-olean"
        self.shared_olean = parent / "shared-olean"
        self.offline_shell = parent / "offline-shell"
        self.codex = parent / "codex"
        self.auth = parent / "auth.json"
        self.results = parent / "results"
        self._make_files()

    def _make_files(self) -> None:
        shared_source_root = self.root / "shared" / "HighamBench"
        shared_source_root.mkdir(parents=True)
        (shared_source_root / "Core.lean").write_text(
            "namespace HighamBench\nend HighamBench\n", encoding="utf-8"
        )
        (shared_source_root / "P01Definitions.lean").write_text(
            "import HighamBench.Core\n", encoding="utf-8"
        )
        benchmark_manifest = {
            "schema_version": "0.1.0",
            "benchmark_id": "test-benchmark",
            "corpus": {"paper_count": 1, "paper_ids": ["P01"]},
            "controlled_shared_files": [
                {
                    "path": "paper_bencmark/highambench/shared/HighamBench/Core.lean",
                    "paper_ids": ["P01"],
                    "sha256": sha256_file(shared_source_root / "Core.lean"),
                },
                {
                    "path": (
                        "paper_bencmark/highambench/shared/HighamBench/"
                        "P01Definitions.lean"
                    ),
                    "paper_ids": ["P01"],
                    "sha256": sha256_file(
                        shared_source_root / "P01Definitions.lean"
                    ),
                },
            ],
            "papers": [
                {
                    "paper_id": "P01",
                    "source": {"sha256": P01_PAPER_SHA256},
                    "targets": [
                        {
                            "task_id": "P01-T1",
                            "tier": "T1",
                            "availability": "available",
                            "lean_target": {
                                "declaration": "p01_t1_fixture",
                                "file": "paper_bencmark/highambench/tasks/P01/T1/Target.lean",
                                "shared_files": [
                                    "paper_bencmark/highambench/shared/HighamBench/Core.lean",
                                    (
                                        "paper_bencmark/highambench/shared/HighamBench/"
                                        "P01Definitions.lean"
                                    ),
                                ],
                            },
                        }
                    ],
                }
            ],
        }
        _executable(
            self.codex,
            "#!/bin/sh\n"
            "if [ \"$1\" = features ]; then\n"
            "  echo 'rollout_budget under development false'\n"
            "else\n"
            "  echo 'codex-cli 1.2.3'\n"
            "fi\n",
        )
        _executable(
            self.toolchain / "bin" / "lean",
            "#!/bin/sh\necho 'Lean (version 4.29.0, x86_64-unknown-linux-gnu, "
            f"commit {LEAN_COMMIT}, Release)'\n",
        )
        (self.toolchain / "lib" / "lean").mkdir(parents=True)
        (self.toolchain / "lib" / "lean" / "Init.olean").write_bytes(b"lean")
        mathlib_olean = self.packages / "mathlib" / ".lake" / "build" / "lib" / "lean"
        mathlib_olean.mkdir(parents=True)
        (mathlib_olean / "Mathlib.olean").write_bytes(b"mathlib")
        (mathlib_olean / "Mathlib.olean.server").write_bytes(b"server")
        (mathlib_olean / "Mathlib.olean.private").write_bytes(b"private")
        (mathlib_olean / "Mathlib.ir").write_bytes(b"ir")
        (mathlib_olean / "Mathlib.trace").write_bytes(b"not exposed")
        (self.packages / "mathlib" / "Mathlib").mkdir()
        (self.packages / "mathlib" / "Mathlib.lean").write_text(
            "import Mathlib.Basic\n", encoding="utf-8"
        )
        (self.packages / "mathlib" / "Mathlib" / "Basic.lean").write_text(
            "def fixture := 1\n", encoding="utf-8"
        )

        (self.project / "NumStability").mkdir(parents=True)
        (self.project / "NumStability" / "Basic.lean").write_text("def x := 1\n", encoding="utf-8")
        (self.project / "NumStability.lean").write_text(
            "import NumStability.Basic\n", encoding="utf-8"
        )
        (self.library_olean / "NumStability").mkdir(parents=True)
        (self.library_olean / "NumStability" / "Basic.olean").write_bytes(b"ns")
        (self.shared_olean / "P01" / "HighamBench").mkdir(parents=True)
        (self.shared_olean / "P01" / "HighamBench" / "Core.olean").write_bytes(
            b"shared-core"
        )
        (self.shared_olean / "P01" / "HighamBench" / "P01Definitions.olean").write_bytes(
            b"shared-p01"
        )
        self.offline_shell.write_bytes(b"offline")
        self.auth.write_text("{}\n", encoding="utf-8")

        for relative in run_matrix.required_release_files(benchmark_manifest):
            path = self.root / relative
            if path.exists():
                continue
            path.parent.mkdir(parents=True, exist_ok=True)
            if relative == "agent_prompt.md":
                path.write_text("prove the target\n", encoding="utf-8")
            else:
                path.write_text(f"fixture {relative}\n", encoding="utf-8")

        write_json(self.metadata / "manifest.json", benchmark_manifest)
        write_json(
            self.root / "tasks" / "P01" / "paper.json",
            {
                "paper_id": "P01",
                "source": {"sha256": P01_PAPER_SHA256},
                "included_tasks": ["P01-T1"],
            },
        )
        write_json(
            self.root / "tasks" / "P01" / "T1" / "task.json",
            {
                "schema_version": "highambench-task-0.3",
                "task_id": "P01-T1",
                "paper_id": "P01",
                "tier": "T1",
                "source_tags": ["EQN"],
                "author_label": None,
                "classification_frozen_before_runs": True,
                "source_locations": [{"anchor": "equation (1.1)"}],
                "paper_source": {"sha256": P01_PAPER_SHA256},
                "context_file": "paper_bencmark/highambench/tasks/P01/T1/context.md",
                "formal_statement": {
                    "namespace": "HighamBench",
                    "theorem_name": "p01_t1_fixture",
                    "target_file": "paper_bencmark/highambench/tasks/P01/T1/Target.lean",
                },
                "validation": {
                    "required_declaration": "HighamBench.p01_t1_fixture",
                    "controlled_target_file": "paper_bencmark/highambench/tasks/P01/T1/Target.lean",
                },
            },
        )
        write_json(
            self.metadata / "run_order.json",
            {"schema_version": 1, "benchmark_id": "test-benchmark", "pairs": []},
        )
        write_json(
            self.metadata / "library_source.json",
            create_manifest(
                self.project,
                requested=["NumStability", "NumStability.lean"],
                label="source",
            ),
        )
        write_json(
            self.metadata / "library_olean.json",
            create_manifest(self.library_olean, label="compiled-library"),
        )
        packages_runtime_manifest = create_manifest(
            self.packages,
            requested=sorted(run_matrix.expected_packages_runtime_files(self.packages)),
            label="packages-runtime",
        )
        write_json(
            self.metadata / "packages_runtime.json", packages_runtime_manifest
        )
        stage_manifest_files(
            self.packages, self.packages_runtime, packages_runtime_manifest
        )
        with mock.patch.object(run_matrix, "_git_head", return_value=MATHLIB_COMMIT), mock.patch.object(
            run_matrix, "_require_git_sources_clean"
        ):
            compiled = run_matrix.compiled_environment_summary(self.toolchain, self.packages)
        write_json(self.metadata / "packages_olean.json", compiled)

        prompt_sha = sha256_file(self.root / "agent_prompt.md")
        condition_prompt = self.root / run_matrix.CONDITION_L_PROMPT_RELATIVE
        prompt_protocol = {
            "version": run_matrix.PROMPT_PROTOCOL_VERSION,
            "composition_order": [
                "common_prompt",
                "condition_L_supplement_if_condition_L",
                "task_context",
                "fixed_target",
            ],
            "common_prompt": {
                "path": "agent_prompt.md",
                "sha256": prompt_sha,
                "bytes": (self.root / "agent_prompt.md").stat().st_size,
            },
            "condition_supplements": {
                "L": {
                    "path": run_matrix.CONDITION_L_PROMPT_RELATIVE,
                    "sha256": sha256_file(condition_prompt),
                    "bytes": condition_prompt.stat().st_size,
                }
            },
            "N_receives_condition_supplement": False,
            "relevant_theorem_or_module_hints_supplied": False,
        }
        execution_components = {
            "filesystem_adapter_sha256": sha256_file(
                self.root / "tools" / "codex_isolated.py"
            ),
            "provider_token_gate_sha256": sha256_file(
                self.root / "tools" / "provider_token_gate.py"
            ),
            "lean_adapter_sha256": sha256_file(
                self.root / "tools" / "lean_isolated.py"
            ),
            "offline_shell_source_sha256": sha256_file(
                self.root / "tools" / "offline_shell.c"
            ),
            "offline_shell_binary_sha256": sha256_file(self.offline_shell),
            "runner_sha256": sha256_file(self.root / "tools" / "runner.py"),
            "validator_sha256": sha256_file(
                self.root / "tools" / "validator.py"
            ),
            "dependency_audit_sha256": sha256_file(
                self.root / "tools" / "dependency_audit.lean"
            ),
        }
        self.provider_gate_record = {
            "schema_version": 2,
            "kind": "fixture-provider-token-gate-freeze",
            "protocol": run_matrix.ultra_canary.runner.PROVIDER_GATE_PROTOCOL,
            "implementation": {
                "version": run_matrix.ultra_canary.runner.PROVIDER_GATE_IMPLEMENTATION_VERSION,
                "source_sha256": execution_components[
                    "provider_token_gate_sha256"
                ]
            },
            "static_configuration": {
                "counted_request_kinds": ["turn", "compaction"],
                "upstream_response_contract": dict(
                    run_matrix.ultra_canary.runner.PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT
                ),
            },
        }
        ultra_orchestration = run_matrix.ultra_orchestration_record()

        canary_root = self.project / "canary-artifacts"
        (canary_root / "attempts").mkdir(parents=True)
        (canary_root / "logs").mkdir()
        canary_record_path = canary_root / "attempts" / "canary.json"
        canary_raw_path = canary_root / "attempts" / "canary.jsonl"
        canary_log_path = canary_root / "logs" / "canary.log"
        canary_usage_path = canary_root / "logs" / "canary.usage.json"
        canary_environment_id = "fixture-pre-canary-environment"
        canary_freeze_check = {
            "benchmark_id": "test-benchmark",
            "environment_id": canary_environment_id,
            "agent": {
                "id": "codex-cli",
                "version": "1.2.3",
                "binary_sha256": sha256_file(self.codex),
                "model": "gpt-5.6-sol",
                "reasoning_effort": "ultra",
                "ultra_orchestration": ultra_orchestration,
            },
            "prompt_protocol": prompt_protocol,
            "execution_components": execution_components,
        }
        canary_freeze_check_sha256 = run_matrix.canonical_document_digest(
            canary_freeze_check
        )
        canary_record = {
            "environment_id": canary_environment_id,
            "agent_command": [
                "adapter",
                "--token-limit",
                "90",
                "--advisory-rollout-budget-limit",
                "100",
                "--model",
                "gpt-5.6-sol",
                "--reasoning-effort",
                "ultra",
            ],
            "frozen_run_verification": {
                "freeze_check": canary_freeze_check,
                "freeze_check_sha256": canary_freeze_check_sha256,
            },
            "pass": False,
            "failure_code": "TOKEN_LIMIT",
            "token_usage": {
                "input_tokens": 100,
                "cached_input_tokens": 40,
                "output_tokens": 10,
                "model_tokens": 110,
                "measurement_source": (
                    "codex_app_server_rawResponse/completed"
                ),
                "live_cumulative": True,
                "input_includes_cached": True,
                "notification_sequence": 1,
                "observed_at_unix_ns": 1,
                "call_count": 1,
                "usage_scope": "rooted_attempt_thread_tree_completed_responses",
                "response_id_deduplicated": True,
                "response_count": 1,
                "thread_count": 2,
                "drain_complete": True,
                "measurement_exact": True,
            },
            "token_measurement": {
                "limit_enforcement": {
                    "triggered": True,
                    "first_crossing_tokens": 100,
                    "first_crossing_overshoot_tokens": 10,
                    "final_endpoint_tokens": 110,
                    "final_overshoot_tokens": 20,
                }
            },
            "network_violation": {"detected": False, "integrity_ok": True},
        }
        write_json(canary_record_path, canary_record)
        write_json(canary_raw_path, canary_record)
        write_json(canary_usage_path, canary_record["token_usage"])
        canary_log_path.write_text(
            '{"method":"rawResponse/completed"}\n', encoding="utf-8"
        )
        canary_evidence_path = (
            self.metadata / "evidence" / "token_control_live_canary.json"
        )
        write_json(
            canary_evidence_path,
            {
                "schema_version": 1,
                "kind": "highambench-live-token-control-canary",
                "status": "passed",
                "public_release": False,
                "benchmark_id": "test-benchmark",
                "agent": {
                    "id": "codex-cli",
                    "version": "1.2.3",
                    "binary_sha256": sha256_file(self.codex),
                    "model": "gpt-5.6-sol",
                    "reasoning_effort": "ultra",
                    "ultra_orchestration": ultra_orchestration,
                },
                "artifact_root": "canary-artifacts",
                "freeze_check_sha256": canary_freeze_check_sha256,
                "pre_canary_environment_id": canary_environment_id,
                "controls": {
                    "frozen_benchmark_token_limit": 100,
                    "outer_canary_token_limit": 90,
                    "nested_advisory_rollout_budget_limit": 100,
                    "measurement_source": "codex_app_server_rawResponse/completed",
                    "notification": "rawResponse/completed",
                    "usage_scope": "rooted_attempt_thread_tree_completed_responses",
                    "live_cumulative": True,
                    "cached_input_counted_once": True,
                    "all_descendant_threads_included": True,
                    "response_ids_deduplicated": True,
                    "drain_complete_required": True,
                    "measurement_exact_required": True,
                    "root_completion_is_tree_barrier": False,
                    "trusted_adapter_freezes_first_threshold": False,
                    "trusted_adapter_latches_first_threshold": True,
                    "trusted_usage_path_outside_workspace": True,
                },
                "outcome": {
                    "input_tokens_including_cached": 100,
                    "cached_input_tokens": 40,
                    "output_tokens": 10,
                    "total_model_tokens": 110,
                    "first_crossing_tokens": 100,
                    "first_crossing_overshoot_tokens": 10,
                    "overshoot_tokens": 10,
                    "final_endpoint_tokens": 110,
                    "final_overshoot_tokens": 20,
                    "notification_sequence": 1,
                    "response_count": 1,
                    "thread_count": 2,
                    "observed_child_thread_count": 1,
                    "notification_count_in_audit_log": 1,
                    "drain_complete": True,
                    "measurement_exact": True,
                },
                "artifacts": {
                    "record": {
                        "path": "attempts/canary.json",
                        "sha256": sha256_file(canary_record_path),
                    },
                    "raw_jsonl": {
                        "path": "attempts/canary.jsonl",
                        "sha256": sha256_file(canary_raw_path),
                    },
                    "agent_log": {
                        "path": "logs/canary.log",
                        "sha256": sha256_file(canary_log_path),
                    },
                    "usage": {
                        "path": "logs/canary.usage.json",
                        "sha256": sha256_file(canary_usage_path),
                    },
                },
            },
        )
        canary_descriptor = {
            "path": run_matrix.FROZEN_TOKEN_CANARY_PATH,
            "sha256": sha256_file(canary_evidence_path),
            "status": "passed",
        }

        release_paths = sorted(run_matrix._release_tree_files(self.root))
        write_json(
            self.metadata / "release_files.json",
            create_manifest(
                self.root,
                requested=release_paths,
                label="evaluation-package-snapshot",
            ),
        )

        source_sha = sha256_file(self.metadata / "library_source.json")
        library_sha = sha256_file(self.metadata / "library_olean.json")
        packages_sha = sha256_file(self.metadata / "packages_olean.json")
        packages_runtime_sha = sha256_file(self.metadata / "packages_runtime.json")
        release_sha = sha256_file(self.metadata / "release_files.json")
        bundle_placeholder = "0" * 64
        frozen = {
            "lean_toolchain": "leanprover/lean4:v4.29.0",
            "lean_commit": LEAN_COMMIT,
            "lean_binary_sha256": sha256_file(self.toolchain / "bin" / "lean"),
            "mathlib_commit": MATHLIB_COMMIT,
            "numstability_commit": NUMSTABILITY_COMMIT,
            "agent_id": "codex-cli",
            "agent_version": "1.2.3",
            "agent_binary_sha256": sha256_file(self.codex),
            "model_version": "gpt-5.6-sol",
            "model_reasoning_effort": "ultra",
            "ultra_orchestration": ultra_orchestration,
            "prompt_sha256": prompt_sha,
            "prompt_protocol": prompt_protocol,
            "allowed_tools": ["shell", "Lean"],
            "hardware_class": "fixture host",
            "operating_system": "fixture",
            "bubblewrap_binary_sha256": sha256_file(Path("/bin/bwrap")),
            "bubblewrap_version": "bubblewrap 0.6.1",
            "numstability_source_manifest": "paper_bencmark/highambench/metadata/library_source.json",
            "numstability_source_manifest_sha256": source_sha,
            "numstability_compiled_manifest": "paper_bencmark/highambench/metadata/library_olean.json",
            "numstability_compiled_manifest_sha256": library_sha,
            "compiled_environment_summary": "paper_bencmark/highambench/metadata/packages_olean.json",
            "compiled_environment_summary_sha256": packages_sha,
            "packages_runtime_manifest": run_matrix.FROZEN_PACKAGES_RUNTIME_MANIFEST_PATH,
            "packages_runtime_manifest_sha256": packages_runtime_sha,
            "python_version": platform.python_version(),
            "python_binary_sha256": sha256_file(Path(sys.executable)),
            "release_manifest": run_matrix.FROZEN_RELEASE_MANIFEST_PATH,
            "release_manifest_sha256": release_sha,
            "token_control_canary": canary_descriptor,
            "provider_token_gate_sha256": run_matrix.canonical_document_digest(
                self.provider_gate_record
            ),
            "environment_id": "placeholder",
            "environment_bundle_sha256": bundle_placeholder,
            "container_image_digest": "sha256:" + "f" * 64,
        }
        token_control = refresh_snapshot._token_control_record(100)
        session_isolation = {
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
        config = {
            "schema_version": "0.1.0",
            "benchmark_id": "test-benchmark",
            "frozen_environment": frozen,
            "failure_reason_priority": list(
                run_matrix.EXPECTED_FAILURE_REASON_PRIORITY
            ),
            "isolation": session_isolation,
            "limits": {
                "wall_clock_seconds": 1800,
                "total_model_tokens": 100,
                "failure_scored_time_seconds": 1800,
                "prompt_startup_timeout_seconds": 120,
                "post_submission_validation_reserve_seconds": 369,
            },
            "token_control": token_control,
        }
        environment = {
            "schema_version": "0.1.0",
            "kind": "highambench-environment-record",
            "environment_id": "placeholder",
            "environment_bundle_sha256": bundle_placeholder,
            "environment_bundle_definition": run_matrix.ENVIRONMENT_BUNDLE_DEFINITION,
            "release_manifest": run_matrix.FROZEN_RELEASE_MANIFEST_PATH,
            "release_manifest_sha256": release_sha,
            "lean": {
                "version": "4.29.0",
                "commit": LEAN_COMMIT,
                "binary_sha256": frozen["lean_binary_sha256"],
                "mathlib_commit": MATHLIB_COMMIT,
                "numstability_commit": NUMSTABILITY_COMMIT,
                "numstability_source_manifest": frozen["numstability_source_manifest"],
                "numstability_source_manifest_sha256": source_sha,
                "numstability_compiled_manifest": frozen["numstability_compiled_manifest"],
                "numstability_compiled_manifest_sha256": library_sha,
                "compiled_environment_summary": frozen["compiled_environment_summary"],
                "compiled_environment_summary_sha256": packages_sha,
                "shared_sources": {
                    "HighamBench/Core.lean": sha256_file(
                        self.root / "shared" / "HighamBench" / "Core.lean"
                    ),
                    "HighamBench/P01Definitions.lean": sha256_file(
                        self.root
                        / "shared"
                        / "HighamBench"
                        / "P01Definitions.lean"
                    ),
                },
                "shared_olean_bundles": {
                    "P01": {
                        "HighamBench/Core.olean": sha256_file(
                            self.shared_olean
                            / "P01"
                            / "HighamBench"
                            / "Core.olean"
                        ),
                        "HighamBench/P01Definitions.olean": sha256_file(
                            self.shared_olean
                            / "P01"
                            / "HighamBench"
                            / "P01Definitions.olean"
                        ),
                    }
                },
            },
            "agent": {
                "id": "codex-cli",
                "version": "1.2.3",
                "binary_sha256": sha256_file(self.codex),
                "model": "gpt-5.6-sol",
                "reasoning_effort": "ultra",
                "ultra_orchestration": ultra_orchestration,
                "prompt_sha256": prompt_sha,
                "prompt_protocol": prompt_protocol,
            },
            "isolation": {
                **session_isolation,
                "filesystem_adapter_sha256": sha256_file(self.root / "tools" / "codex_isolated.py"),
                "provider_token_gate_sha256": sha256_file(
                    self.root / "tools" / "provider_token_gate.py"
                ),
                "lean_adapter_sha256": sha256_file(self.root / "tools" / "lean_isolated.py"),
                "offline_shell_source_sha256": sha256_file(self.root / "tools" / "offline_shell.c"),
                "offline_shell_binary_sha256": sha256_file(self.offline_shell),
                "runner_sha256": sha256_file(self.root / "tools" / "runner.py"),
                "validator_sha256": sha256_file(self.root / "tools" / "validator.py"),
                "dependency_audit_sha256": sha256_file(
                    self.root / "tools" / "dependency_audit.lean"
                ),
                "bubblewrap_binary_sha256": frozen["bubblewrap_binary_sha256"],
                "bubblewrap_version": frozen["bubblewrap_version"],
            },
            "runtime": {
                "prompt_startup_timeout_seconds": 120,
                "post_submission_validation_reserve_seconds": 369,
                "python": {
                    "version": frozen["python_version"],
                    "binary_sha256": frozen["python_binary_sha256"],
                },
                "packages_runtime_manifest": frozen["packages_runtime_manifest"],
                "packages_runtime_manifest_sha256": packages_runtime_sha,
            },
            "host_class": {
                "kernel": "fixture",
                "virtualization": "LXC",
                "processor": "fixture",
                "online_logical_cpus": 1,
                "visible_memory_bytes": 1,
            },
            "token_control": token_control,
            "token_control_canary": canary_descriptor,
            "provider_token_gate": self.provider_gate_record,
        }
        bundle = run_matrix.environment_bundle_digest(config, environment)
        environment_id = f"highambench-p01-{bundle[:16]}"
        frozen["environment_id"] = environment_id
        frozen["environment_bundle_sha256"] = bundle
        environment["environment_id"] = environment_id
        environment["environment_bundle_sha256"] = bundle
        write_json(self.metadata / "config.json", config)
        write_json(self.metadata / "environment.json", environment)

    def args(self) -> argparse.Namespace:
        return argparse.Namespace(
            benchmark_root=self.root,
            project_root=self.project,
            results_root=self.results,
            codex=self.codex,
            auth_file=self.auth,
            offline_shell=self.offline_shell,
            toolchain_root=self.toolchain,
            packages_root=self.packages,
            packages_runtime_root=self.packages_runtime,
            shared_olean_root=self.shared_olean,
            library_source=self.project / "NumStability",
            library_root_file=self.project / "NumStability.lean",
            library_olean=self.library_olean,
            release_manifest=None,
            agent_id=None,
            agent_version=None,
            model=None,
            reasoning_effort=None,
            time_limit_seconds=None,
            token_limit=None,
            agent_network_verified=True,
            token_control_verified=False,
            force=False,
        )


class RunMatrixTests(unittest.TestCase):
    def setUp(self) -> None:
        self.temporary = tempfile.TemporaryDirectory()
        self.base = Path(self.temporary.name)

    def tearDown(self) -> None:
        self.temporary.cleanup()

    def test_provider_reconciliation_v3_accepts_authenticated_collaboration_supersession(
        self,
    ) -> None:
        appserver_usage = {
            "input_tokens": 20,
            "cached_input_tokens": 4,
            "cache_write_input_tokens": 0,
            "output_tokens": 2,
            "reasoning_output_tokens": 1,
            "total_tokens": 22,
        }
        superseded_usage = {
            "input_tokens": 10,
            "cached_input_tokens": 0,
            "cache_write_input_tokens": 0,
            "output_tokens": 1,
            "reasoning_output_tokens": 0,
            "total_tokens": 11,
        }
        zero = {field: 0 for field in run_matrix.PROVIDER_USAGE_FIELDS}
        value = {
            "schema_version": 3,
            "provider_response_count": 2,
            "appserver_response_count": 1,
            "suppressed_collaboration_wait_response_count": 0,
            "superseded_by_collaboration_message_response_count": 1,
            "provider_usage": {
                field: appserver_usage[field] + superseded_usage[field]
                for field in appserver_usage
            },
            "appserver_usage": appserver_usage,
            "suppressed_collaboration_wait_usage": zero,
            "superseded_by_collaboration_message_usage": superseded_usage,
            "provider_response_ids": ["superseded-response", "direct-response"],
            "appserver_response_ids": ["direct-response"],
            "suppressed_collaboration_wait_response_ids": [],
            "suppressed_collaboration_wait_evidence": [],
            "superseded_by_collaboration_message_response_ids": [
                "superseded-response"
            ],
            "superseded_by_collaboration_message_evidence": [
                {
                    "response_id": "superseded-response",
                    "provider_call_id": "provider-call-1",
                    "thread_id": "root-thread",
                    "turn_id": "root-turn",
                    "successor_response_id": "direct-response",
                    "successor_call_id": "provider-call-2",
                    "collaboration_messages": [
                        {
                            "item_id": "agent-message-1",
                            "item_sha256": "a" * 64,
                            "author": "/root/child",
                            "recipient": "/root",
                            "observed_at_unix_ns": 2,
                            "observed_at_monotonic_ns": 3,
                        }
                    ],
                }
            ],
            "discarded_after_explicit_child_interrupt_response_count": 0,
            "discarded_after_explicit_child_interrupt_usage": zero,
            "discarded_after_explicit_child_interrupt_response_ids": [],
            "discarded_after_explicit_child_interrupt_evidence": [],
        }
        thread_accounting = [
            {
                "thread_id": "root-thread",
                "parent_thread_id": None,
                "agent_path": "root",
            },
            {
                "thread_id": "child-thread",
                "parent_thread_id": "root-thread",
                "agent_path": "/root/child",
            },
        ]
        direct_ledger = [
            {
                "response_id": "direct-response",
                "thread_id": "root-thread",
                "turn_id": "root-turn",
                "provider_gate_call": {
                    "response_id": "direct-response",
                    "call_id": "provider-call-2",
                    "request_metadata": {
                        "thread_id": "root-thread",
                        "turn_id": "root-turn",
                        "request_kind": "turn",
                    },
                },
            }
        ]
        verified = run_matrix.verify_provider_usage_reconciliation(
            value,
            expected_thread_accounting=thread_accounting,
            expected_root_thread_id="root-thread",
            expected_appserver_response_ledger=direct_ledger,
        )
        self.assertEqual(
            verified["superseded_by_collaboration_message_usage"],
            superseded_usage,
        )

        parent_to_child = json.loads(json.dumps(value))
        parent_to_child["superseded_by_collaboration_message_evidence"][0][
            "thread_id"
        ] = "child-thread"
        parent_to_child["superseded_by_collaboration_message_evidence"][0][
            "turn_id"
        ] = "child-turn"
        message = parent_to_child[
            "superseded_by_collaboration_message_evidence"
        ][0]["collaboration_messages"][0]
        message["author"] = "/root"
        message["recipient"] = "/root/child"
        child_direct_ledger = json.loads(json.dumps(direct_ledger))
        child_direct_ledger[0]["thread_id"] = "child-thread"
        child_direct_ledger[0]["turn_id"] = "child-turn"
        child_direct_ledger[0]["provider_gate_call"]["request_metadata"].update(
            {"thread_id": "child-thread", "turn_id": "child-turn"}
        )
        run_matrix.verify_provider_usage_reconciliation(
            parent_to_child,
            expected_thread_accounting=thread_accounting,
            expected_root_thread_id="root-thread",
            expected_appserver_response_ledger=child_direct_ledger,
        )

        wrong_target = json.loads(json.dumps(parent_to_child))
        wrong_target["superseded_by_collaboration_message_evidence"][0][
            "thread_id"
        ] = "root-thread"
        with self.assertRaisesRegex(BenchmarkToolError, "route changed"):
            run_matrix.verify_provider_usage_reconciliation(
                wrong_target,
                expected_thread_accounting=thread_accounting,
                expected_root_thread_id="root-thread",
                expected_appserver_response_ledger=child_direct_ledger,
            )

        malformed = json.loads(json.dumps(value))
        malformed["superseded_by_collaboration_message_evidence"][0][
            "collaboration_messages"
        ] = []
        with self.assertRaisesRegex(
            BenchmarkToolError, "lacks message evidence"
        ):
            run_matrix.verify_provider_usage_reconciliation(
                malformed,
                expected_thread_accounting=thread_accounting,
                expected_root_thread_id="root-thread",
                expected_appserver_response_ledger=direct_ledger,
            )

    def test_provider_reconciliation_v3_superseded_successor_is_route_local(
        self,
    ) -> None:
        zero = {field: 0 for field in run_matrix.PROVIDER_USAGE_FIELDS}
        direct_usage = {**zero, "input_tokens": 30, "total_tokens": 30}
        superseded_usage = {**zero, "input_tokens": 10, "total_tokens": 10}
        provider_usage = {**zero, "input_tokens": 40, "total_tokens": 40}
        provider_ids = [
            "root-superseded",
            "child-direct-1",
            "child-direct-2",
            "root-direct",
        ]
        appserver_ids = provider_ids[1:]
        value = {
            "schema_version": 3,
            "provider_response_count": 4,
            "appserver_response_count": 3,
            "suppressed_collaboration_wait_response_count": 0,
            "superseded_by_collaboration_message_response_count": 1,
            "discarded_after_explicit_child_interrupt_response_count": 0,
            "provider_usage": provider_usage,
            "appserver_usage": direct_usage,
            "suppressed_collaboration_wait_usage": zero,
            "superseded_by_collaboration_message_usage": superseded_usage,
            "discarded_after_explicit_child_interrupt_usage": zero,
            "provider_response_ids": provider_ids,
            "appserver_response_ids": appserver_ids,
            "suppressed_collaboration_wait_response_ids": [],
            "suppressed_collaboration_wait_evidence": [],
            "superseded_by_collaboration_message_response_ids": [
                "root-superseded"
            ],
            "superseded_by_collaboration_message_evidence": [
                {
                    "response_id": "root-superseded",
                    "provider_call_id": "root-call-1",
                    "thread_id": "root-thread",
                    "turn_id": "root-turn",
                    "successor_response_id": "root-direct",
                    "successor_call_id": "root-call-2",
                    "collaboration_messages": [
                        {
                            "item_id": "child-message",
                            "item_sha256": "a" * 64,
                            "author": "/root/child",
                            "recipient": "/root",
                            "observed_at_unix_ns": 2,
                            "observed_at_monotonic_ns": 3,
                        }
                    ],
                }
            ],
            "discarded_after_explicit_child_interrupt_response_ids": [],
            "discarded_after_explicit_child_interrupt_evidence": [],
        }

        def direct(
            response_id: str,
            call_id: str,
            thread_id: str,
            turn_id: str,
        ) -> dict:
            return {
                "response_id": response_id,
                "thread_id": thread_id,
                "turn_id": turn_id,
                "provider_gate_call": {
                    "response_id": response_id,
                    "call_id": call_id,
                    "request_metadata": {
                        "thread_id": thread_id,
                        "turn_id": turn_id,
                        "request_kind": "turn",
                    },
                },
            }

        ledger = [
            direct("child-direct-1", "child-call-1", "child-thread", "child-turn"),
            direct("child-direct-2", "child-call-2", "child-thread", "child-turn"),
            direct("root-direct", "root-call-2", "root-thread", "root-turn"),
        ]
        threads = [
            {
                "thread_id": "root-thread",
                "parent_thread_id": None,
                "agent_path": "root",
            },
            {
                "thread_id": "child-thread",
                "parent_thread_id": "root-thread",
                "agent_path": "/root/child",
            },
        ]
        verified = run_matrix.verify_provider_usage_reconciliation(
            value,
            expected_thread_accounting=threads,
            expected_root_thread_id="root-thread",
            expected_appserver_response_ledger=ledger,
        )
        self.assertEqual(
            verified["superseded_by_collaboration_message_response_ids"],
            ["root-superseded"],
        )

        same_route_between = json.loads(json.dumps(ledger))
        same_route_between[0]["thread_id"] = "root-thread"
        same_route_between[0]["turn_id"] = "root-turn"
        same_route_between[0]["provider_gate_call"]["request_metadata"].update(
            {"thread_id": "root-thread", "turn_id": "root-turn"}
        )
        mutations = {
            "same_route_intervening": (value, same_route_between),
            "wrong_successor_call": (json.loads(json.dumps(value)), ledger),
            "wrong_successor_response": (json.loads(json.dumps(value)), ledger),
            "wrong_successor_thread": (value, json.loads(json.dumps(ledger))),
            "wrong_successor_turn": (value, json.loads(json.dumps(ledger))),
        }
        mutations["wrong_successor_call"][0][
            "superseded_by_collaboration_message_evidence"
        ][0]["successor_call_id"] = "wrong-call"
        wrong_response = mutations["wrong_successor_response"][0][
            "superseded_by_collaboration_message_evidence"
        ][0]
        wrong_response["successor_response_id"] = "child-direct-2"
        wrong_response["successor_call_id"] = "child-call-2"
        for name, field, replacement in (
            ("wrong_successor_thread", "thread_id", "child-thread"),
            ("wrong_successor_turn", "turn_id", "other-root-turn"),
        ):
            target = mutations[name][1][-1]
            target[field] = replacement
            target["provider_gate_call"]["request_metadata"][field] = replacement
        for name, (mutated_value, mutated_ledger) in mutations.items():
            with self.subTest(name=name), self.assertRaisesRegex(
                BenchmarkToolError, "immediate same-route successor"
            ):
                run_matrix.verify_provider_usage_reconciliation(
                    mutated_value,
                    expected_thread_accounting=threads,
                    expected_root_thread_id="root-thread",
                    expected_appserver_response_ledger=mutated_ledger,
                )

    def test_provider_reconciliation_v3_accepts_explicit_child_interrupt_discard(
        self,
    ) -> None:
        direct = {
            "input_tokens": 20,
            "cached_input_tokens": 4,
            "cache_write_input_tokens": 0,
            "output_tokens": 2,
            "reasoning_output_tokens": 1,
            "total_tokens": 22,
        }
        discarded = {
            "input_tokens": 10,
            "cached_input_tokens": 0,
            "cache_write_input_tokens": 0,
            "output_tokens": 1,
            "reasoning_output_tokens": 0,
            "total_tokens": 11,
        }
        zero = {field: 0 for field in run_matrix.PROVIDER_USAGE_FIELDS}
        times = {
            "interrupt_function_observed_at_unix_ns": 1_000_000,
            "interrupt_function_observed_at_monotonic_ns": 10,
            "interrupt_activity_observed_at_unix_ns": 2_000_000,
            "interrupt_activity_observed_at_monotonic_ns": 20,
            "interrupt_output_observed_at_unix_ns": 3_000_000,
            "interrupt_output_observed_at_monotonic_ns": 30,
            "interrupted_turn_observed_at_unix_ns": 4_000_000,
            "interrupted_turn_observed_at_monotonic_ns": 40,
        }
        value = {
            "schema_version": 3,
            "provider_response_count": 2,
            "appserver_response_count": 1,
            "suppressed_collaboration_wait_response_count": 0,
            "superseded_by_collaboration_message_response_count": 0,
            "discarded_after_explicit_child_interrupt_response_count": 1,
            "provider_usage": {
                field: direct[field] + discarded[field] for field in direct
            },
            "appserver_usage": direct,
            "suppressed_collaboration_wait_usage": zero,
            "superseded_by_collaboration_message_usage": zero,
            "discarded_after_explicit_child_interrupt_usage": discarded,
            "provider_response_ids": ["interrupt-response", "discard-response"],
            "appserver_response_ids": ["interrupt-response"],
            "suppressed_collaboration_wait_response_ids": [],
            "suppressed_collaboration_wait_evidence": [],
            "superseded_by_collaboration_message_response_ids": [],
            "superseded_by_collaboration_message_evidence": [],
            "discarded_after_explicit_child_interrupt_response_ids": [
                "discard-response"
            ],
            "discarded_after_explicit_child_interrupt_evidence": [
                {
                    "response_id": "discard-response",
                    "provider_call_id": "discard-call",
                    "thread_id": "child-thread",
                    "turn_id": "child-turn",
                    "interrupting_response_id": "interrupt-response",
                    "interrupting_provider_call_id": "interrupt-provider-call",
                    "interrupt_function_item_id": "interrupt-item",
                    "interrupt_function_call_id": "interrupt-tool-call",
                    "interrupt_function_arguments_sha256": "a" * 64,
                    "interrupt_parent_thread_id": "root-thread",
                    "interrupt_parent_turn_id": "root-turn",
                    "interrupted_agent_path": "/root/child",
                    "interrupt_activity_item_sha256": "b" * 64,
                    "interrupt_output_item_id": "interrupt-output",
                    "interrupt_output_item_sha256": "c" * 64,
                    **times,
                }
            ],
        }
        thread_accounting = [
            {
                "thread_id": "root-thread",
                "parent_thread_id": None,
                "agent_path": "root",
            },
            {
                "thread_id": "child-thread",
                "parent_thread_id": "root-thread",
                "agent_path": "/root/child",
            },
        ]
        verified = run_matrix.verify_provider_usage_reconciliation(
            value,
            expected_thread_accounting=thread_accounting,
            expected_root_thread_id="root-thread",
        )
        self.assertEqual(
            verified["discarded_after_explicit_child_interrupt_usage"], discarded
        )

        wrong_parent = json.loads(json.dumps(value))
        wrong_parent["discarded_after_explicit_child_interrupt_evidence"][0][
            "interrupt_parent_thread_id"
        ] = "child-thread"
        with self.assertRaisesRegex(BenchmarkToolError, "child edge"):
            run_matrix.verify_provider_usage_reconciliation(
                wrong_parent,
                expected_thread_accounting=thread_accounting,
                expected_root_thread_id="root-thread",
            )

    def test_gate_v3_sse_authentication_is_exact_and_tamper_evident(self) -> None:
        for content_type_present in (True, False):
            call = _valid_sse_call_fixture(
                content_type_present=content_type_present
            )
            checked = run_matrix._validate_provider_gate_call_sse_authentication(
                call, label="fixture"
            )
            self.assertEqual(checked["completed_event_index"], 1)
            self.assertIs(
                checked["downstream_content_type_synthesized"],
                not content_type_present,
            )

        mutations = (
            (
                "legacy_protocol",
                lambda call: call["upstream_sse_authentication"].__setitem__(
                    "protocol", "highambench-provider-token-gate-v2"
                ),
            ),
            (
                "legacy_parser",
                lambda call: call["upstream_sse_authentication"].__setitem__(
                    "parser", "legacy-sse-parser-v2"
                ),
            ),
            (
                "duplicate_content_type",
                lambda call: call.__setitem__("upstream_content_type_occurrences", 2),
            ),
            (
                "wrong_absence_basis",
                lambda call: call["upstream_sse_authentication"].__setitem__(
                    "content_type_basis", "authenticated_stream_request_header_absent"
                ),
            ),
            (
                "synthesized_flip",
                lambda call: call["upstream_sse_authentication"].__setitem__(
                    "downstream_content_type_synthesized", True
                ),
            ),
            (
                "body_digest",
                lambda call: call["upstream_sse_authentication"].__setitem__(
                    "body_sha256", "0" * 64
                ),
            ),
            (
                "completion_index",
                lambda call: call["upstream_sse_authentication"].__setitem__(
                    "completed_event_index", 0
                ),
            ),
            (
                "content_encoding",
                lambda call: call.update(
                    {
                        "upstream_content_encoding": "gzip",
                        "upstream_content_encoding_occurrences": 1,
                    }
                ),
            ),
        )
        for label, mutate in mutations:
            with self.subTest(label=label):
                call = json.loads(json.dumps(_valid_sse_call_fixture()))
                mutate(call)
                with self.assertRaises(BenchmarkToolError):
                    run_matrix._validate_provider_gate_call_sse_authentication(
                        call, label="fixture"
                    )

    def test_paper_boundary_index_requires_a_known_contiguous_paper_block(self) -> None:
        assignments = [
            {"paper_id": "P01"},
            {"paper_id": "P01"},
            {"paper_id": "P02"},
        ]
        self.assertEqual(run_matrix._paper_boundary_index(assignments, "P01"), 2)
        self.assertIsNone(run_matrix._paper_boundary_index(assignments, None))
        with self.assertRaisesRegex(Exception, "unknown paper"):
            run_matrix._paper_boundary_index(assignments, "P03")
        with self.assertRaisesRegex(Exception, "revisits paper"):
            run_matrix._paper_boundary_index(
                [{"paper_id": "P01"}, {"paper_id": "P02"}, {"paper_id": "P01"}],
                "P01",
            )

    def test_allocated_hardware_helpers_measure_topology_and_cgroup_limit(self) -> None:
        sysfs = self.base / "sys" / "devices" / "system" / "cpu"
        for cpu_id, package_id, core_id in ((0, 0, 2), (4, 0, 2), (1, 0, 3)):
            topology = sysfs / f"cpu{cpu_id}" / "topology"
            topology.mkdir(parents=True)
            (topology / "physical_package_id").write_text(
                f"{package_id}\n", encoding="utf-8"
            )
            (topology / "core_id").write_text(f"{core_id}\n", encoding="utf-8")
        self.assertEqual(
            run_matrix._allocated_cpu_topology({0, 1, 4}, sysfs_root=sysfs),
            {
                "online_logical_cpus": 3,
                "allocated_physical_cores": 2,
                "allocated_sockets": 1,
                "allocated_threads_per_core": [1, 2],
            },
        )

        proc_cgroup = self.base / "proc-self-cgroup"
        proc_cgroup.write_text(
            "9:memory:/slurm/uid_1/job_7/step/task_0\n", encoding="utf-8"
        )
        cgroup_root = self.base / "cgroup"
        task_limit = (
            cgroup_root
            / "memory"
            / "slurm"
            / "uid_1"
            / "job_7"
            / "step"
            / "task_0"
            / "memory.limit_in_bytes"
        )
        task_limit.parent.mkdir(parents=True)
        task_limit.write_text("9223372036854771712\n", encoding="utf-8")
        job_limit = task_limit.parents[2] / "memory.limit_in_bytes"
        job_limit.write_text("34359738368\n", encoding="utf-8")
        self.assertEqual(
            run_matrix._cgroup_memory_limit_bytes(
                proc_cgroup=proc_cgroup, cgroup_root=cgroup_root
            ),
            34359738368,
        )
        self.assertEqual(run_matrix._slurm_memory_bytes("32G"), 34359738368)
        self.assertEqual(
            run_matrix._slurm_allocation_shape(
                "JobId=7 NumNodes=1 NumCPUs=4 NumTasks=1 CPUs/Task=4 "
                "AllocTRES=billing=4,cpu=4,mem=32G,node=1"
            ),
            {
                "slurm_num_nodes": 1,
                "slurm_num_cpus": 4,
                "slurm_num_tasks": 1,
                "slurm_cpus_per_task": 4,
                "slurm_allocated_memory_bytes": 34359738368,
            },
        )

    def test_slurm_gpu_provenance_records_exact_zero_allocation(self) -> None:
        raw_alloc_tres = "billing=4,cpu=4,mem=32G,node=1"
        provenance = run_matrix._slurm_gpu_provenance(
            "1505507",
            job_output=(
                "JobId=1505507 JobName=highambench Partition=KFOUNTOU "
                f"AllocTRES={raw_alloc_tres} NodeList=watgpu108"
            ),
            environ={
                "SLURM_GPUS_ON_NODE": "0",
                "SLURM_JOB_GPUS": "",
            },
        )
        self.assertEqual(
            provenance,
            {
                "alloc_tres": raw_alloc_tres,
                "allocated_gpu_count": 0,
                "gpu_environment": {
                    "SLURM_GPUS_ON_NODE": "0",
                    "SLURM_JOB_GPUS": "",
                    "CUDA_VISIBLE_DEVICES": None,
                },
            },
        )
        self.assertEqual(
            run_matrix._slurm_gpu_provenance(
                "1505507",
                job_output=(
                    "JobId=1505507 "
                    "AllocTRES=billing=4,cpu=4,mem=32G,node=1,"
                    "gres/gpu=0,gres/gpu:a100=0"
                ),
                environ={
                    "SLURM_GPUS_ON_NODE": "",
                    "SLURM_JOB_GPUS": "",
                    "CUDA_VISIBLE_DEVICES": "",
                },
            )["allocated_gpu_count"],
            0,
        )

    def test_slurm_gpu_provenance_rejects_nonzero_or_malformed_tres(self) -> None:
        bad_alloc_tres = (
            "billing=4,cpu=4,mem=32G,node=1,gres/gpu=1",
            "billing=4,cpu=4,mem=32G,node=1,gres/gpu:a100=2",
            "billing=4,cpu=4,mem=32G,node=1,gres/gpu=",
            "billing=4,cpu=4,mem=32G,node=1,gres/gpu:a100=zero",
            "billing=4,cpu=4,mem=32G,node=1,gres/gpu::a100=0",
            "billing=4,cpu=4,mem=32G,node=1,gres/gpu/a100=0",
            "billing=4,cpu=4,mem=32G,node=1,GRES/GPU=0",
            "billing=4,cpu=4,mem=32G,node=1,gres/gpu=00",
            "billing=4,cpu=4,mem=32G,node=1,gres/gpu=0,gres/gpu=0",
            "billing=4,cpu=4,mem=32G,node=1,,gres/gpu=0",
        )
        for alloc_tres in bad_alloc_tres:
            with self.subTest(alloc_tres=alloc_tres), self.assertRaisesRegex(
                Exception, "GPU|AllocTRES"
            ):
                run_matrix._slurm_gpu_provenance(
                    "1505507",
                    job_output=f"JobId=1505507 AllocTRES={alloc_tres}",
                    environ={},
                )
        for output in (
            "JobId=1505507 NodeList=watgpu108",
            "JobId=1505507 AllocTRES=cpu=4 AllocTRES=cpu=4",
            "JobId=1505508 AllocTRES=cpu=4,mem=32G,node=1",
        ):
            with self.subTest(output=output), self.assertRaisesRegex(
                Exception, "AllocTRES|job IDs"
            ):
                run_matrix._slurm_gpu_provenance(
                    "1505507", job_output=output, environ={}
                )

    def test_slurm_gpu_provenance_rejects_visible_gpu_environment(self) -> None:
        output = (
            "JobId=1505507 "
            "AllocTRES=billing=4,cpu=4,mem=32G,node=1"
        )
        bad_environments = (
            {"SLURM_GPUS_ON_NODE": "1"},
            {"SLURM_GPUS_ON_NODE": " 0"},
            {"SLURM_JOB_GPUS": "0"},
            {"SLURM_JOB_GPUS": "gpu:a100:0"},
            {"CUDA_VISIBLE_DEVICES": "0"},
            {"CUDA_VISIBLE_DEVICES": "-1"},
        )
        for environment in bad_environments:
            with self.subTest(environment=environment), self.assertRaisesRegex(
                Exception,
                "SLURM_GPUS_ON_NODE|SLURM_JOB_GPUS|CUDA_VISIBLE_DEVICES",
            ):
                run_matrix._slurm_gpu_provenance(
                    "1505507", job_output=output, environ=environment
                )

    def test_slurm_sharing_provenance_is_factual_and_nonexclusive(self) -> None:
        sharing = run_matrix._slurm_scheduler_sharing(
            "1505507",
            job_output=(
                "JobId=1505507 Partition=KFOUNTOU NumNodes=1 "
                "Shared=OK NodeList=watgpu108"
            ),
            partition_output=(
                "PartitionName=KFOUNTOU Nodes=watgpu108 OverSubscribe=FORCE:1"
            ),
        )
        self.assertEqual(sharing, _scheduler_sharing())
        with self.assertRaisesRegex(Exception, "non-exclusive"):
            run_matrix._slurm_scheduler_sharing(
                "1505507",
                job_output=(
                    "JobId=1505507 Partition=KFOUNTOU Shared=NO "
                    "NodeList=watgpu108"
                ),
                partition_output=(
                    "PartitionName=KFOUNTOU OverSubscribe=FORCE:1"
                ),
            )

    def test_allocation_hardware_record_is_created_idempotently_and_bound(self) -> None:
        results = self.base / "results"
        freeze = _allocation_freeze_check()
        with mock.patch.dict(
            os.environ, {run_matrix.SLURM_JOB_ID_ENV: "1505507"}
        ), mock.patch.object(
            run_matrix.platform, "node", return_value="watgpu108"
        ), mock.patch.object(
            run_matrix, "_current_cpu_affinity", return_value=[8, 9, 56, 57]
        ), mock.patch.object(
            run_matrix, "_slurm_scheduler_sharing", return_value=_scheduler_sharing()
        ), mock.patch.object(
            run_matrix, "_slurm_gpu_provenance", return_value=_slurm_gpu_provenance()
        ):
            first = run_matrix.create_or_verify_allocation_hardware_record(
                results, freeze
            )
            path = results / first["path"]
            first_bytes = path.read_bytes()
            first_mtime_ns = path.stat().st_mtime_ns
            second = run_matrix.create_or_verify_allocation_hardware_record(
                results, freeze
            )

        self.assertEqual(first, second)
        self.assertEqual(path.read_bytes(), first_bytes)
        self.assertEqual(path.stat().st_mtime_ns, first_mtime_ns)
        self.assertEqual(
            first["path"], "allocation_hardware/slurm-1505507.json"
        )
        hardware = read_json(path)
        self.assertEqual(hardware["job_id"], "1505507")
        self.assertEqual(hardware["hostname"], "watgpu108")
        self.assertEqual(hardware["slurm"]["node_list"], "watgpu108")
        self.assertEqual(
            hardware["slurm"]["alloc_tres"],
            "billing=4,cpu=4,mem=32G,node=1",
        )
        self.assertEqual(hardware["slurm"]["allocated_gpu_count"], 0)
        self.assertEqual(
            hardware["slurm"]["gpu_environment"],
            {
                "SLURM_GPUS_ON_NODE": None,
                "SLURM_JOB_GPUS": None,
                "CUDA_VISIBLE_DEVICES": None,
            },
        )
        self.assertEqual(
            hardware["allocation"]["cpu_affinity_logical_cpus"],
            [8, 9, 56, 57],
        )
        self.assertFalse(hardware["scheduler_sharing"]["exclusive"])
        self.assertEqual(
            hardware["measurement_environment"]["freeze_check_sha256"],
            run_matrix.canonical_document_digest(freeze),
        )
        self.assertEqual(
            hardware["record_sha256"],
            run_matrix.allocation_hardware_record_digest(hardware),
        )
        self.assertEqual(first["sha256"], sha256_file(path))
        run_matrix.verify_allocation_hardware_descriptor(results, first, freeze)

        attempt = {"kind": "highambench-run", "run_id": "P01-T1-rep-01-N"}
        run_matrix._bind_allocation_hardware(attempt, first)
        run_matrix._bind_allocation_hardware(attempt, first)
        self.assertEqual(attempt["allocation_hardware"], first)
        changed = dict(first)
        changed["job_id"] = "1505508"
        with self.assertRaisesRegex(Exception, "different allocation"):
            run_matrix._bind_allocation_hardware(attempt, changed)

    def test_allocation_hardware_record_rejects_tamper_and_stale_freeze(self) -> None:
        freeze = _allocation_freeze_check()

        def produce(results: Path, current_freeze: dict[str, object]) -> dict[str, str]:
            with mock.patch.dict(
                os.environ, {run_matrix.SLURM_JOB_ID_ENV: "1505507"}
            ), mock.patch.object(
                run_matrix.platform, "node", return_value="watgpu108"
            ), mock.patch.object(
                run_matrix, "_current_cpu_affinity", return_value=[8, 9, 56, 57]
            ), mock.patch.object(
                run_matrix,
                "_slurm_scheduler_sharing",
                return_value=_scheduler_sharing(),
            ), mock.patch.object(
                run_matrix,
                "_slurm_gpu_provenance",
                return_value=_slurm_gpu_provenance(),
            ):
                return run_matrix.create_or_verify_allocation_hardware_record(
                    results, current_freeze
                )

        tampered_results = self.base / "tampered"
        descriptor = produce(tampered_results, freeze)
        path = tampered_results / descriptor["path"]
        hardware = read_json(path)
        hardware["host"]["cpu_model"] = 999
        hardware["record_sha256"] = run_matrix.allocation_hardware_record_digest(
            hardware
        )
        write_json(path, hardware)
        with self.assertRaisesRegex(Exception, "stale|differs"):
            produce(tampered_results, freeze)

        gpu_tampered_results = self.base / "gpu-tampered"
        gpu_descriptor = produce(gpu_tampered_results, freeze)
        gpu_path = gpu_tampered_results / gpu_descriptor["path"]
        gpu_hardware = read_json(gpu_path)
        gpu_hardware["slurm"]["gpu_environment"]["CUDA_VISIBLE_DEVICES"] = "0"
        gpu_hardware["record_sha256"] = (
            run_matrix.allocation_hardware_record_digest(gpu_hardware)
        )
        write_json(gpu_path, gpu_hardware)
        with self.assertRaisesRegex(Exception, "GPU provenance is stale"):
            produce(gpu_tampered_results, freeze)

        stale_results = self.base / "stale"
        produce(stale_results, freeze)
        changed_freeze = json.loads(json.dumps(freeze))
        changed_freeze["environment_id"] = "highambench-fixture-fedcba9876543210"
        with self.assertRaisesRegex(Exception, "stale|differs"):
            produce(stale_results, changed_freeze)

    @mock.patch.object(
        run_matrix, "authenticate_runner_provider_gate_summary", return_value={}
    )
    def test_final_record_authentication_rejects_tamper_swap_and_stale_provenance(
        self, _gate: mock.Mock
    ) -> None:
        results = self.base / "results"
        records = results / "records"
        records.mkdir(parents=True)
        freeze = _allocation_freeze_check()
        assignment = _assignment_fixture()
        allocation = _historical_allocation_descriptor(results, freeze)
        path = records / f"{assignment['run_id']}.json"
        valid = _sealed_final_record(assignment, freeze, allocation)
        write_json(path, valid)
        authenticated = run_matrix._authenticate_final_assignment_record(
            results, path, assignment, freeze
        )
        self.assertEqual(authenticated, valid)

        tampered = json.loads(json.dumps(valid))
        tampered["failure_code"] = "PROOF_ERROR"
        write_json(path, tampered)
        with self.assertRaisesRegex(Exception, "self-hash"):
            run_matrix._authenticate_final_assignment_record(
                results, path, assignment, freeze
            )

        swapped = json.loads(json.dumps(valid))
        swapped["run_id"] = "P01-T1-rep-01-L"
        swapped[run_matrix.MATRIX_RECORD_SHA256_FIELD] = (
            run_matrix.matrix_record_digest(swapped)
        )
        write_json(path, swapped)
        with self.assertRaisesRegex(Exception, "planned run_id"):
            run_matrix._authenticate_final_assignment_record(
                results, path, assignment, freeze
            )

        write_json(path, valid)
        stale_freeze = json.loads(json.dumps(freeze))
        stale_freeze["environment_id"] = "highambench-fixture-stale000000000"
        stale_freeze["release_manifest"]["sha256"] = "d" * 64
        with self.assertRaisesRegex(Exception, "stale .*provenance|stale environment"):
            run_matrix._authenticate_final_assignment_record(
                results, path, assignment, stale_freeze
            )

        missing_descriptor = json.loads(json.dumps(valid))
        missing_descriptor.pop("allocation_hardware")
        missing_descriptor[run_matrix.MATRIX_RECORD_SHA256_FIELD] = (
            run_matrix.matrix_record_digest(missing_descriptor)
        )
        write_json(path, missing_descriptor)
        with self.assertRaisesRegex(Exception, "no allocation hardware"):
            run_matrix._authenticate_final_assignment_record(
                results, path, assignment, freeze
            )

        wrong_descriptor = json.loads(json.dumps(valid))
        wrong_descriptor["allocation_hardware"]["record_sha256"] = "e" * 64
        wrong_descriptor[run_matrix.MATRIX_RECORD_SHA256_FIELD] = (
            run_matrix.matrix_record_digest(wrong_descriptor)
        )
        write_json(path, wrong_descriptor)
        with self.assertRaisesRegex(Exception, "descriptor self-hash"):
            run_matrix._authenticate_final_assignment_record(
                results, path, assignment, freeze
            )

        write_json(path, valid)
        (results / allocation["path"]).unlink()
        with self.assertRaisesRegex(Exception, "missing or a symlink"):
            run_matrix._authenticate_final_assignment_record(
                results, path, assignment, freeze
            )

        conflicting = {"run_id": assignment["run_id"], "matrix_record_sha256": "0" * 64}
        with self.assertRaisesRegex(Exception, "conflicting"):
            run_matrix._bind_matrix_record_sha256(conflicting)

    def test_ultra_canary_verifier_requires_projection_v6_and_v12_prompt(self) -> None:
        project = self.base / "project"
        evidence_path = project / run_matrix.FROZEN_ULTRA_CANARY_PATH
        descriptor = {
            "path": run_matrix.FROZEN_ULTRA_CANARY_PATH,
            "sha256": "d" * 64,
            "status": "passed",
        }
        frozen = {"ultra_orchestration_canary": descriptor}
        environment = {"ultra_orchestration_canary": descriptor}
        projection = _ultra_projection_fixture()
        token_limit = 5_000_000
        write_json(
            evidence_path,
            {
                "canary_id": run_matrix.ultra_canary.CANARY_ID,
                "prompt": run_matrix.ultra_canary.prompt_record(),
                "controls": run_matrix.ultra_canary.controls_record(
                    token_limit, 300
                ),
                "outcome": {
                    "accounting_projection": projection,
                    "prompt_release": _ultra_prompt_release_fixture(),
                },
            },
        )
        summary = _ultra_canary_summary_fixture(
            descriptor_sha256=str(descriptor["sha256"]),
            projection=projection,
        )
        with mock.patch.object(
            run_matrix.ultra_canary,
            "verify_frozen_attestation",
            return_value=summary,
        ) as verify:
            checked = run_matrix._verify_ultra_orchestration_canary(
                project,
                frozen,
                environment,
                benchmark_id="fixture-benchmark",
                token_limit=token_limit,
                agent_id="codex-cli",
                agent_version="fixture",
                model="gpt-5.6-sol",
                reasoning_effort="ultra",
                agent_binary_sha256="a" * 64,
                prompt_protocol={"version": "fixture-production-prompt-v1"},
                execution_components=_production_components_fixture(),
            )
        self.assertEqual(checked["accounting_projection"], projection)
        verify.assert_called_once()
        self.assertEqual(
            verify.call_args.kwargs["expected_prompt_protocol"],
            {"version": "fixture-production-prompt-v1"},
        )
        self.assertEqual(
            verify.call_args.kwargs["expected_execution_components"],
            _production_components_fixture(),
        )

    def test_ultra_canary_verifier_rejects_projection_and_control_tamper(self) -> None:
        project = self.base / "project"
        evidence_path = project / run_matrix.FROZEN_ULTRA_CANARY_PATH
        descriptor = {
            "path": run_matrix.FROZEN_ULTRA_CANARY_PATH,
            "sha256": "d" * 64,
            "status": "passed",
        }
        token_limit = 5_000_000

        def invoke(
            projection: dict[str, object],
            *,
            prompt: dict[str, object] | None = None,
            controls: dict[str, object] | None = None,
            summary: dict[str, object] | None = None,
        ) -> None:
            checked_summary = (
                _ultra_canary_summary_fixture(
                    descriptor_sha256=str(descriptor["sha256"]),
                    projection=projection,
                )
                if summary is None
                else summary
            )
            write_json(
                evidence_path,
                {
                    "canary_id": run_matrix.ultra_canary.CANARY_ID,
                    "prompt": (
                        run_matrix.ultra_canary.prompt_record()
                        if prompt is None
                        else prompt
                    ),
                    "controls": (
                        run_matrix.ultra_canary.controls_record(token_limit, 300)
                        if controls is None
                        else controls
                    ),
                    "outcome": {
                        "accounting_projection": projection,
                        "prompt_release": checked_summary["prompt_release"],
                    },
                },
            )
            with mock.patch.object(
                run_matrix.ultra_canary,
                "verify_frozen_attestation",
                return_value=checked_summary,
            ):
                run_matrix._verify_ultra_orchestration_canary(
                    project,
                    {"ultra_orchestration_canary": descriptor},
                    {"ultra_orchestration_canary": descriptor},
                    benchmark_id="fixture-benchmark",
                    token_limit=token_limit,
                    agent_id="codex-cli",
                    agent_version="fixture",
                    model="gpt-5.6-sol",
                    reasoning_effort="ultra",
                    agent_binary_sha256="a" * 64,
                    prompt_protocol={"version": "fixture-production-prompt-v1"},
                    execution_components=_production_components_fixture(),
                )

        bad_digest = _ultra_projection_fixture()
        bad_digest["projection_payload_sha256"] = "0" * 64
        with self.assertRaisesRegex(Exception, "payload SHA-256"):
            invoke(bad_digest)

        zero_baseline = _ultra_projection_fixture()
        zero_baseline["thread_accounting"][0]["expected_cumulative_baseline"] = {  # type: ignore[index]
            "total_tokens": 0
        }
        zero_baseline.pop("projection_payload_sha256")
        zero_baseline["projection_payload_sha256"] = (
            run_matrix.canonical_document_digest(zero_baseline)
        )
        with self.assertRaisesRegex(Exception, "inherited accounting"):
            invoke(zero_baseline)

        controls = run_matrix.ultra_canary.controls_record(token_limit, 300)
        controls["nonzero_inherited_child_baseline_required"] = False
        with self.assertRaisesRegex(Exception, "controls"):
            invoke(_ultra_projection_fixture(), controls=controls)

        prompt = run_matrix.ultra_canary.prompt_record()
        prompt["protocol"] = "synthetic-v2"
        with self.assertRaisesRegex(Exception, "V12 prompt protocol"):
            invoke(_ultra_projection_fixture(), prompt=prompt)

        stale_release = _ultra_canary_summary_fixture(
            descriptor_sha256=str(descriptor["sha256"]),
            projection=_ultra_projection_fixture(),
        )
        stale_release["prompt_release"]["startup_timeout_seconds"] = 119  # type: ignore[index]
        with self.assertRaisesRegex(Exception, "prompt release"):
            invoke(
                stale_release["accounting_projection"],  # type: ignore[arg-type]
                summary=stale_release,
            )

        wrong_deadline = _ultra_canary_summary_fixture(
            descriptor_sha256=str(descriptor["sha256"]),
            projection=_ultra_projection_fixture(),
        )
        wrong_deadline["prompt_release"]["measurement_deadline_monotonic_ns"] += 1  # type: ignore[index,operator]
        with self.assertRaisesRegex(Exception, "prompt release"):
            invoke(
                wrong_deadline["accounting_projection"],  # type: ignore[arg-type]
                summary=wrong_deadline,
            )

        missing_artifact = _ultra_canary_summary_fixture(
            descriptor_sha256=str(descriptor["sha256"]),
            projection=_ultra_projection_fixture(),
        )
        missing_artifact["artifacts"].pop(  # type: ignore[union-attr]
            run_matrix.ultra_canary.ARTIFACT_LABELS[-1]
        )
        with self.assertRaisesRegex(Exception, "artifact set"):
            invoke(
                missing_artifact["accounting_projection"],  # type: ignore[arg-type]
                summary=missing_artifact,
            )

        incomplete_audit = _ultra_canary_summary_fixture(
            descriptor_sha256=str(descriptor["sha256"]),
            projection=_ultra_projection_fixture(),
        )
        incomplete_audit["dependency_audit"]["complete"] = False  # type: ignore[index]
        with self.assertRaisesRegex(Exception, "dependency audit"):
            invoke(
                incomplete_audit["accounting_projection"],  # type: ignore[arg-type]
                summary=incomplete_audit,
            )

    def test_slurm_deadline_reserves_a_complete_pair_and_guard(self) -> None:
        args = argparse.Namespace(allocation_end_epoch=None)
        with mock.patch.dict(
            os.environ, {run_matrix.SLURM_JOB_END_TIME_ENV: "2000000000"}
        ):
            self.assertEqual(run_matrix._allocation_end_epoch(args), 2_000_000_000.0)

        records = self.base / "records"
        records.mkdir()
        assignments = [
            _assignment_fixture(),
            _assignment_fixture(condition="L"),
        ]
        freeze = _allocation_freeze_check()
        allocation = _historical_allocation_descriptor(self.base, freeze)
        self.assertEqual(
            run_matrix._unfinished_runs_in_pair(
                assignments, 0, records, self.base, freeze
            ),
            2,
        )
        self.assertEqual(
            run_matrix._required_allocation_seconds(
                2,
                run_limit_seconds=900,
                prompt_startup_timeout_seconds=120,
                post_submission_validation_reserve_seconds=369,
                guard_seconds=600,
            ),
            3618,
        )
        self.assertEqual(
            run_matrix._required_allocation_seconds(
                2,
                run_limit_seconds=1800,
                prompt_startup_timeout_seconds=120,
                post_submission_validation_reserve_seconds=369,
                guard_seconds=600,
            ),
            5418,
        )
        write_json(
            records / "P01-T1-rep-01-N.json",
            _sealed_final_record(assignments[0], freeze, allocation),
        )
        self.assertEqual(
            run_matrix._unfinished_runs_in_pair(
                assignments, 1, records, self.base, freeze
            ),
            1,
        )

    @mock.patch.object(
        run_matrix, "authenticate_runner_provider_gate_summary", return_value={}
    )
    def test_interrupted_active_attempt_cannot_be_silently_retried(
        self, _gate: mock.Mock
    ) -> None:
        records = self.base / "records"
        records.mkdir()
        marker = self.base / run_matrix.ACTIVE_RUN_MARKER
        assignment = _assignment_fixture()
        freeze = _allocation_freeze_check()
        allocation = _historical_allocation_descriptor(self.base, freeze)
        marker_value = {
            "schema_version": run_matrix.ACTIVE_RUN_MARKER_SCHEMA_VERSION,
            "kind": "highambench-active-hosted-attempt",
            "assignment": run_matrix._planned_assignment_record_identity(assignment),
            "attempt": 1,
            "attempt_output": "attempts/P01-T1-rep-01-N.attempt-1.json",
            "started_at_unix": 1.0,
            "allocation_hardware": allocation,
        }
        write_json(
            marker,
            marker_value,
        )
        with self.assertRaisesRegex(Exception, "cannot be silently discarded or retried"):
            run_matrix._clear_or_reject_interrupted_run(
                marker, records, self.base, [assignment], freeze
            )
        self.assertTrue(marker.is_file())

        final = _sealed_final_record(assignment, freeze, allocation)
        write_json(
            records / "P01-T1-rep-01-N.json",
            final,
        )
        write_json(
            self.base / marker_value["attempt_output"],
            final,
        )

        mismatched_marker = json.loads(json.dumps(marker_value))
        mismatched_marker["attempt"] = 2
        mismatched_marker["attempt_output"] = (
            "attempts/P01-T1-rep-01-N.attempt-2.json"
        )
        write_json(marker, mismatched_marker)
        write_json(self.base / mismatched_marker["attempt_output"], final)
        with self.assertRaisesRegex(Exception, "attempt does not match"):
            run_matrix._clear_or_reject_interrupted_run(
                marker, records, self.base, [assignment], freeze
            )
        self.assertTrue(marker.is_file())

        write_json(marker, marker_value)
        run_matrix._clear_or_reject_interrupted_run(
            marker, records, self.base, [assignment], freeze
        )
        self.assertFalse(marker.exists())

    def test_useful_work_uses_positive_exactness_allowlist(self) -> None:
        self.assertEqual(
            run_matrix._matrix_incident_control(
                "retryable_pre_prompt_system_error", True
            ),
            {
                "status": "retryable_pre_prompt_system_error",
                "retry_allowed": True,
                "scored": False,
                "final_assignment_record_written": False,
            },
        )
        with self.assertRaisesRegex(Exception, "status/retry policy"):
            run_matrix._matrix_incident_control(
                "retryable_pre_prompt_system_error", False
            )
        record = {
            "run_id": "P01-T1-rep-01-N",
            "useful_work_started": True,
            "pass": False,
            "scored": False,
            "agent_exit_code": 0,
            "failure_code": "TIME_LIMIT",
            "token_usage": {
                "usage_scope": "rooted_attempt_thread_tree_completed_responses",
                "measurement_exact": False,
            },
            "token_measurement": {
                "provider_cumulative_total_exact": False,
                "measurement_error": (
                    "completed-response aggregate is only a lower bound at "
                    "the wall-clock endpoint"
                ),
            },
        }
        self.assertTrue(run_matrix._useful_work_attempt_requires_abort(record))

        exact_failure = {
            "run_id": "P01-T1-rep-01-N",
            "useful_work_started": True,
            "pass": False,
            "scored": True,
            "agent_exit_code": 0,
            "failure_code": "NO_SUBMISSION",
            "token_usage": {
                "usage_scope": "rooted_attempt_thread_tree_completed_responses",
                "measurement_exact": True,
                "submission_boundary_exact": False,
                "submission_boundary": None,
                "drain_complete": True,
                "tree_quiescent": True,
                "active_thread_ids": [],
                "unresolved_thread_ids": [],
                "invalid_reasons": [],
            },
        }
        self.assertFalse(run_matrix._useful_work_attempt_requires_abort(exact_failure))
        self.assertTrue(run_matrix._failed_attempt_has_exact_natural_drain(exact_failure))

        forged_exact_timeout = {
            **exact_failure,
            "failure_code": "TIME_LIMIT",
        }
        self.assertFalse(
            run_matrix._failed_attempt_has_exact_natural_drain(
                forged_exact_timeout
            )
        )
        self.assertTrue(
            run_matrix._useful_work_attempt_requires_abort(forged_exact_timeout)
        )

        exact_pass = {
            "run_id": "P01-T1-rep-01-L",
            "useful_work_started": True,
            "pass": True,
            "scored": True,
            "agent_exit_code": 0,
            "failure_code": None,
            "token_usage": {
                "usage_scope": "rooted_attempt_thread_tree_completed_responses",
                "measurement_exact": True,
                "submission_boundary_exact": True,
                "drain_complete": False,
                "tree_quiescent": False,
                "stop_reason": "first_valid_proof",
                "root_thread_id": "root",
                "active_thread_ids": ["root"],
                "unresolved_thread_ids": [],
                "invalid_reasons": [],
                "submission_boundary": {
                    **_exact_nested_submission_boundary_fixture(),
                    "authenticated": True,
                    "status": "accepted",
                    "exact": True,
                    "root_only": True,
                    "descendants_quiescent": True,
                    "later_model_response_possible": False,
                },
            },
            "ultra_submission_boundary": {"verified": True},
        }
        exact_boundary = exact_pass["token_usage"]["submission_boundary"]
        exact_pass["ultra_submission_boundary"] = _seal_retained_request(
            self.base, exact_boundary, label="exact-pass"
        )
        self.assertFalse(run_matrix._useful_work_attempt_requires_abort(exact_pass))
        self.assertTrue(run_matrix._accepted_pass_has_exact_boundary(exact_pass))

        reverse_order = json.loads(json.dumps(exact_pass))
        reverse_boundary = reverse_order["token_usage"]["submission_boundary"]
        reverse_boundary["submission_event_order"] = (
            run_matrix.ultra_canary.codex_isolated.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER
        )
        reverse_boundary["dynamic_call_observed_before_raw_response_completed"] = False
        reverse_boundary["raw_response_completed_before_dynamic_call_observed"] = True
        reverse_order["ultra_submission_boundary"] = _seal_retained_request(
            self.base, reverse_boundary, label="reverse-order-pass"
        )
        self.assertTrue(run_matrix._accepted_pass_has_exact_boundary(reverse_order))

        timestamp_mismatch = json.loads(json.dumps(exact_pass))
        timestamp_boundary = timestamp_mismatch["token_usage"]["submission_boundary"]
        timestamp_mismatch["ultra_submission_boundary"] = _seal_retained_request(
            self.base, timestamp_boundary, label="timestamp-mismatch-pass"
        )
        request_descriptor = timestamp_mismatch["ultra_submission_boundary"][
            "artifacts"
        ]["request"]
        request_path = Path(request_descriptor["path"])
        request_path.chmod(0o644)
        request = read_json(request_path)
        request["captured_at_monotonic_ns"] = (
            request["raw_response_observed_at_monotonic_ns"] + 1
        )
        request = run_matrix.ultra_canary.codex_isolated.authenticated_record(
            request, "request_sha256"
        )
        timestamp_boundary["request_sha256"] = request["request_sha256"]
        write_json(request_path, request)
        request_path.chmod(0o444)
        request_descriptor["record_sha256"] = request["request_sha256"]
        request_descriptor["file_sha256"] = run_matrix.sha256_file(request_path)
        self.assertFalse(
            run_matrix._accepted_pass_has_exact_boundary(timestamp_mismatch)
        )

        for event_order, first_flag, second_flag in (
            ("invalid-order", True, False),
            (
                run_matrix.ultra_canary.codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE,
                True,
                True,
            ),
            (
                run_matrix.ultra_canary.codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE,
                False,
                False,
            ),
        ):
            malformed_order = json.loads(json.dumps(exact_pass))
            malformed_boundary = malformed_order["token_usage"]["submission_boundary"]
            malformed_boundary["submission_event_order"] = event_order
            malformed_boundary[
                "dynamic_call_observed_before_raw_response_completed"
            ] = first_flag
            malformed_boundary[
                "raw_response_completed_before_dynamic_call_observed"
            ] = second_flag
            self.assertFalse(
                run_matrix._accepted_pass_has_exact_boundary(malformed_order)
            )

        for malformed in (
            {"useful_work_started": True, "pass": False, "scored": False},
            {
                **exact_failure,
                "token_usage": {
                    **exact_failure["token_usage"],
                    "usage_scope": "wrong_scope",
                },
            },
            {
                **exact_pass,
                "ultra_submission_boundary": {"verified": False},
            },
            {**exact_pass, "agent_exit_code": 2},
            {**exact_failure, "agent_exit_code": 2},
            {**exact_pass, "agent_exit_code": False},
            {**exact_failure, "agent_exit_code": 0.0},
            {**exact_pass, "agent_exit_code": None},
        ):
            self.assertTrue(run_matrix._useful_work_attempt_requires_abort(malformed))

    @mock.patch.object(run_matrix, "_verify_host_class", return_value={"verified": True})
    @mock.patch.object(
        run_matrix,
        "_verify_ultra_orchestration_canary",
        return_value={"status": "passed"},
    )
    @mock.patch.object(
        run_matrix,
        "_verify_token_control_canary",
        return_value={"status": "passed"},
    )
    @mock.patch.object(run_matrix, "_require_git_sources_clean")
    @mock.patch.object(run_matrix, "_require_git_paths_equal")
    @mock.patch.object(run_matrix, "_require_git_commit")
    def test_frozen_environment_is_derived_and_rejects_extra_library_olean(
        self,
        _commit: mock.Mock,
        _paths_equal: mock.Mock,
        _clean: mock.Mock,
        _token_canary: mock.Mock,
        _ultra_canary: mock.Mock,
        _host: mock.Mock,
    ) -> None:
        fixture = FrozenEnvironmentFixture(self.base)

        def git_head(path: Path, _label: str) -> str:
            return NUMSTABILITY_COMMIT if path.resolve() == fixture.project.resolve() else MATHLIB_COMMIT

        with mock.patch.object(
            run_matrix, "_git_head", side_effect=git_head
        ), mock.patch.object(
            run_matrix,
            "provider_token_gate_environment_record",
            return_value=fixture.provider_gate_record,
        ):
            args = fixture.args()
            check = run_matrix.verify_frozen_run_environment(args, fixture.root)
            self.assertTrue(check["ok"])
            self.assertEqual(args.environment_id, check["environment_id"])
            self.assertEqual(args.reasoning_effort, "ultra")
            self.assertEqual(args.time_limit_seconds, 1800)
            self.assertEqual(
                args.post_submission_validation_reserve_seconds, 369
            )
            self.assertEqual(
                check["limits"]["post_submission_validation_reserve_seconds"],
                369.0,
            )
            self.assertEqual(
                check["packages_runtime"]["file_count"],
                check["packages_runtime"]["source_file_count"]
                + check["packages_runtime"]["olean_file_count"]
                + check["packages_runtime"]["compiled_support_file_count"],
            )
            self.assertEqual(check["packages_runtime"]["source_file_count"], 2)
            self.assertEqual(check["packages_runtime"]["olean_file_count"], 1)
            self.assertEqual(
                check["packages_runtime"]["compiled_support_file_count"], 3
            )
            self.assertEqual(
                check["prompt_protocol"]["version"],
                run_matrix.PROMPT_PROTOCOL_VERSION,
            )
            self.assertEqual(
                set(check["prompt_protocol"]["condition_supplements"]), {"L"}
            )
            self.assertEqual(
                check["agent"]["ultra_orchestration"]["submission_barrier"],
                run_matrix.ultra_submission_barrier_record(),
            )
            mismatched_reserve = fixture.args()
            mismatched_reserve.post_submission_validation_reserve_seconds = 368
            with self.assertRaisesRegex(Exception, "post-submission.*disagrees"):
                run_matrix.verify_frozen_run_environment(
                    mismatched_reserve, fixture.root
                )

            config_path = fixture.metadata / "config.json"
            environment_path = fixture.metadata / "environment.json"
            original_config = json.loads(config_path.read_text(encoding="utf-8"))
            original_environment = json.loads(
                environment_path.read_text(encoding="utf-8")
            )
            limit_tamper = json.loads(json.dumps(original_config))
            environment_tamper = json.loads(json.dumps(original_environment))
            limit_tamper["limits"]["wall_clock_seconds"] = 1799
            limit_tamper["limits"]["failure_scored_time_seconds"] = 1799
            tampered_bundle = run_matrix.environment_bundle_digest(
                limit_tamper, environment_tamper
            )
            tampered_environment_id = f"highambench-p01-{tampered_bundle[:16]}"
            limit_tamper["frozen_environment"]["environment_id"] = (
                tampered_environment_id
            )
            limit_tamper["frozen_environment"]["environment_bundle_sha256"] = (
                tampered_bundle
            )
            environment_tamper["environment_id"] = tampered_environment_id
            environment_tamper["environment_bundle_sha256"] = tampered_bundle
            write_json(config_path, limit_tamper)
            write_json(environment_path, environment_tamper)
            with self.assertRaisesRegex(Exception, "limits.*yield envelope"):
                run_matrix.verify_frozen_run_environment(
                    fixture.args(), fixture.root
                )
            write_json(config_path, original_config)
            write_json(environment_path, original_environment)

            gate_config_tamper = json.loads(json.dumps(original_config))
            gate_environment_tamper = json.loads(json.dumps(original_environment))
            gate_environment_tamper["provider_token_gate"][
                "static_configuration"
            ]["counted_request_kinds"] = ["turn", "tool"]
            gate_config_tamper["frozen_environment"][
                "provider_token_gate_sha256"
            ] = run_matrix.canonical_document_digest(
                gate_environment_tamper["provider_token_gate"]
            )
            write_json(config_path, gate_config_tamper)
            write_json(environment_path, gate_environment_tamper)
            with self.assertRaisesRegex(
                Exception,
                "actual provider-token-gate source/catalog/transport differs",
            ):
                run_matrix.verify_frozen_run_environment(
                    fixture.args(), fixture.root
                )
            write_json(config_path, original_config)
            write_json(environment_path, original_environment)

            condition_prompt = fixture.root / run_matrix.CONDITION_L_PROMPT_RELATIVE
            original_condition_prompt = condition_prompt.read_bytes()
            condition_prompt.write_bytes(original_condition_prompt + b"tamper\n")
            with self.assertRaisesRegex(Exception, "release files changed|prompt"):
                run_matrix.verify_frozen_run_environment(fixture.args(), fixture.root)
            condition_prompt.write_bytes(original_condition_prompt)

            (fixture.library_olean / "LeanFpAnalysis.olean").write_bytes(b"leak")
            with self.assertRaisesRegex(Exception, "exact pruned manifest tree"):
                run_matrix.verify_frozen_run_environment(fixture.args(), fixture.root)
            (fixture.library_olean / "LeanFpAnalysis.olean").unlink()

            package_leak = (
                fixture.packages
                / "mathlib"
                / ".lake"
                / "build"
                / "lib"
                / "lean"
                / "Hidden.olean"
            )
            package_leak.write_bytes(b"hidden")
            with self.assertRaisesRegex(Exception, "compiled Lean/package trees"):
                run_matrix.verify_frozen_run_environment(fixture.args(), fixture.root)
            package_leak.unlink()

            (fixture.shared_olean / "Hidden.olean").write_bytes(b"hidden")
            with self.assertRaisesRegex(Exception, "shared olean root is not exact"):
                run_matrix.verify_frozen_run_environment(fixture.args(), fixture.root)
            (fixture.shared_olean / "Hidden.olean").unlink()

            (fixture.packages_runtime / "Hidden.olean").write_bytes(b"hidden")
            with self.assertRaisesRegex(Exception, "exact frozen manifest tree"):
                run_matrix.verify_frozen_run_environment(fixture.args(), fixture.root)
            (fixture.packages_runtime / "Hidden.olean").unlink()

            with mock.patch.object(
                run_matrix.platform, "python_version", return_value="0.0.0"
            ):
                with self.assertRaisesRegex(Exception, "actual Python version"):
                    run_matrix.verify_frozen_run_environment(fixture.args(), fixture.root)

            command_args = fixture.args()
            run_matrix.verify_frozen_run_environment(command_args, fixture.root)
            command_args.freeze_check_json = "{}"
            assignment = {
                "pair_id": "P02-T1-rep-01",
                "task_id": "P02-T1",
                "paper_id": "P02",
                "paper_sha256": P02_PAPER_SHA256,
                "tier": "T1",
                "theorem_name": "p02_t1_fixture",
                "required_declaration": "HighamBench.p02_t1_fixture",
                "target_dir": "tasks/P02/T1",
                "target_file": "tasks/P02/T1/Target.lean",
                "context_file": "tasks/P02/T1/context.md",
                "repetition_id": "rep-01",
                "condition": "L",
                "condition_order": ["N", "L"],
                "order_index": 2,
                "run_id": "P02-T1-rep-01-L",
            }
            command = run_matrix.runner_command(
                command_args,
                assignment,
                self.base / "attempt.jsonl",
                self.base / "attempt.json",
                self.base / "base",
            )
            runtime_value = str(fixture.packages_runtime.resolve())
            original_value = str(fixture.packages.resolve())
            nested_commands = [
                json.loads(command[command.index(option) + 1])
                for option in (
                    "--agent-command-json",
                    "--compile-command-json",
                    "--audit-command-json",
                    "--n-probe-command-json",
                )
            ]
            adapter_command = nested_commands[0]
            for option, expected in (
                ("--prompt-ready-output", "{prompt_ready_output}"),
                ("--prompt-go-input", "{prompt_go_input}"),
                ("--prompt-release-output", "{prompt_release_output}"),
                ("--prompt-handshake-nonce", "{prompt_handshake_nonce}"),
                ("--prompt-run-id", "{run_id}"),
            ):
                self.assertEqual(adapter_command.count(option), 1)
                self.assertEqual(
                    adapter_command[adapter_command.index(option) + 1], expected
                )
            self.assertEqual(
                adapter_command[adapter_command.index("--token-limit") + 1],
                "100",
            )
            self.assertEqual(
                adapter_command[
                    adapter_command.index("--advisory-rollout-budget-limit") + 1
                ],
                "100",
            )
            condition_prompt = (
                fixture.root / run_matrix.CONDITION_L_PROMPT_RELATIVE
            ).resolve()
            self.assertEqual(
                adapter_command[adapter_command.index("--condition-prompt-file") + 1],
                str(condition_prompt),
            )
            self.assertEqual(
                adapter_command[
                    adapter_command.index("--condition-prompt-sha256") + 1
                ],
                sha256_file(condition_prompt),
            )
            library_options = {
                "--library-source": str(fixture.project / "NumStability"),
                "--library-root-file": str(fixture.project / "NumStability.lean"),
                "--library-olean": str(fixture.library_olean),
            }
            for nested in nested_commands:
                for option, expected_path in library_options.items():
                    self.assertEqual(nested.count(option), 1)
                    self.assertEqual(
                        nested[nested.index(option) + 1],
                        str(Path(expected_path).resolve()),
                    )
            self.assertTrue(
                all(runtime_value in nested for nested in nested_commands)
            )
            self.assertTrue(
                all(original_value not in nested for nested in nested_commands)
            )
            p02_shared_bundle = str((fixture.shared_olean / "P02").resolve())
            p01_shared_bundle = str((fixture.shared_olean / "P01").resolve())
            self.assertTrue(
                all(p02_shared_bundle in nested for nested in nested_commands)
            )
            self.assertTrue(
                all(p01_shared_bundle not in nested for nested in nested_commands)
            )
            self.assertTrue(command_args.token_control_verified)
            self.assertIn("--token-enforced", command)
            self.assertEqual(command.count("--prompt-startup-timeout-seconds"), 1)
            self.assertEqual(
                command[command.index("--prompt-startup-timeout-seconds") + 1],
                "120",
            )
            self.assertEqual(
                command[command.index("--validation-timeout-seconds") + 1],
                "120.0",
            )
            self.assertEqual(
                command[command.index("--audit-timeout-seconds") + 1],
                "120.0",
            )
            self.assertEqual(
                command.count("--reject-workspace-local-module-imports"), 1
            )
            self.assertEqual(command[command.index("--paper-id") + 1], "P02")
            self.assertEqual(
                command[command.index("--paper-sha256") + 1], P02_PAPER_SHA256
            )
            self.assertEqual(
                command[command.index("--canonical-relative") + 1],
                "task/tasks/P02/T1/Target.lean",
            )
            self.assertEqual(
                command[command.index("--target-theorem") + 1],
                "HighamBench.p02_t1_fixture",
            )

            n_assignment = dict(assignment)
            n_assignment.update(
                condition="N",
                order_index=1,
                run_id="P02-T1-rep-01-N",
            )
            n_command = run_matrix.runner_command(
                command_args,
                n_assignment,
                self.base / "attempt-n.jsonl",
                self.base / "attempt-n.json",
                self.base / "base",
            )
            n_adapter = json.loads(
                n_command[n_command.index("--agent-command-json") + 1]
            )
            self.assertNotIn("--condition-prompt-file", n_adapter)
            self.assertNotIn("--condition-prompt-sha256", n_adapter)
            self.assertNotIn(str(condition_prompt), n_adapter)
            n_nested_commands = [
                json.loads(n_command[n_command.index(option) + 1])
                for option in (
                    "--agent-command-json",
                    "--compile-command-json",
                    "--audit-command-json",
                    "--n-probe-command-json",
                )
            ]
            for nested in n_nested_commands:
                for option, host_path in library_options.items():
                    self.assertNotIn(option, nested)
                    self.assertNotIn(str(Path(host_path).resolve()), nested)
            self.assertEqual(
                n_command.count("--reject-workspace-local-module-imports"), 1
            )

            config_path = fixture.metadata / "config.json"
            changed_config = json.loads(config_path.read_text(encoding="utf-8"))
            changed_config["changed_after_freeze"] = True
            write_json(config_path, changed_config)
            with self.assertRaisesRegex(Exception, "canonical config/environment payload"):
                run_matrix.verify_frozen_run_environment(fixture.args(), fixture.root)

    def test_token_projection_accepts_live_stale_cumulative_notice(self) -> None:
        projection = _token_projection_fixture()
        verified = run_matrix._verify_token_canary_projection(
            projection, token_canary
        )
        self.assertEqual(
            verified["root_cumulative_projection_status"],
            "cumulative_projection_mismatch",
        )

        projection["root_cumulative_projection_status"] = "untrusted_status"
        projection["projection_payload_sha256"] = (
            run_matrix.canonical_document_digest(
                {
                    key: value
                    for key, value in projection.items()
                    if key != "projection_payload_sha256"
                }
            )
        )
        with self.assertRaisesRegex(
            BenchmarkToolError, "root-only exact accounting projection"
        ):
            run_matrix._verify_token_canary_projection(projection, token_canary)

    def test_token_control_canary_uses_canonical_v6_and_rejects_tamper(
        self,
    ) -> None:
        project = self.base / "project"
        artifact_root = project / "canary-artifacts"
        artifact_root.mkdir(parents=True)
        prompt_protocol = {"version": "production-signposted-v1"}
        execution_components = {
            "runner_sha256": "1" * 64,
            "filesystem_adapter_sha256": "2" * 64,
        }
        production_freeze = {
            "benchmark_id": "fixture-benchmark",
            "prompt_protocol": prompt_protocol,
            "execution_components": execution_components,
        }
        artifact_records: dict[str, dict[str, object]] = {
            label: {"label": label} for label in token_canary.ARTIFACT_LABELS
        }
        artifact_records["freeze_check"] = production_freeze
        # This deliberately differs from the production prompt. The matrix gate
        # must authenticate it through the canonical validator, not compare the
        # synthetic runner protocol with the production protocol.
        artifact_records["runner_freeze_check"] = {
            **production_freeze,
            "prompt_protocol": {"version": "synthetic-canary-v1"},
        }
        artifact_descriptors: dict[str, dict[str, object]] = {}
        for label, value in artifact_records.items():
            path = artifact_root / f"{label}.json"
            write_json(path, value)
            artifact_descriptors[label] = {
                "path": path.name,
                "sha256": sha256_file(path),
            }

        evidence_path = project / run_matrix.FROZEN_TOKEN_CANARY_PATH
        evidence = {
            "schema_version": token_canary.EVIDENCE_SCHEMA_VERSION,
            "kind": token_canary.EVIDENCE_KIND,
            "status": "passed",
            "public_release": False,
            "scored": False,
            "matrix_assignment": False,
            "synthetic_input": True,
            "benchmark_task_bytes_used": False,
            "canary_id": token_canary.CANARY_ID,
            "benchmark_id": "fixture-benchmark",
            "prompt": token_canary.prompt_record(),
            "artifact_root": "canary-artifacts",
            "artifacts": artifact_descriptors,
        }
        write_json(evidence_path, evidence)
        descriptor = {
            "path": run_matrix.FROZEN_TOKEN_CANARY_PATH,
            "sha256": sha256_file(evidence_path),
            "status": "passed",
        }
        frozen = {"token_control_canary": descriptor}
        environment = {"token_control_canary": dict(descriptor)}
        arguments = {
            "benchmark_id": "fixture-benchmark",
            "token_limit": 5_000_000,
            "agent_id": "codex-cli",
            "agent_version": "fixture",
            "model": "gpt-5.6-sol",
            "reasoning_effort": "ultra",
            "agent_binary_sha256": "3" * 64,
            "prompt_protocol": prompt_protocol,
            "execution_components": execution_components,
        }
        summary = _token_canary_summary_fixture()

        with mock.patch.object(
            token_canary,
            "validate_attestation_document",
            return_value=summary,
        ) as validator:
            verified = run_matrix._verify_token_control_canary(
                project, frozen, environment, **arguments
            )
        self.assertEqual(
            verified["path"], run_matrix.FROZEN_TOKEN_CANARY_PATH
        )
        self.assertEqual(verified["observed_child_thread_count"], 0)
        self.assertTrue(
            verified["prompt_release"]["sanitized_provider_gate_crossing"]
        )
        self.assertEqual(
            set(verified["artifacts"]), set(token_canary.ARTIFACT_LABELS)
        )
        validator.assert_called_once()
        self.assertEqual(
            validator.call_args.kwargs["expected_frozen_token_limit"],
            5_000_000,
        )

        mismatched_environment = json.loads(json.dumps(environment))
        mismatched_environment["token_control_canary"]["status"] = "failed"
        with mock.patch.object(
            token_canary, "validate_attestation_document"
        ) as validator:
            with self.assertRaisesRegex(Exception, "disagrees across frozen metadata"):
                run_matrix._verify_token_control_canary(
                    project, frozen, mismatched_environment, **arguments
                )
            validator.assert_not_called()

        original_evidence = evidence_path.read_bytes()
        evidence_path.write_bytes(original_evidence + b" ")
        with mock.patch.object(
            token_canary, "validate_attestation_document"
        ) as validator:
            with self.assertRaisesRegex(Exception, "evidence has the wrong SHA-256"):
                run_matrix._verify_token_control_canary(
                    project, frozen, environment, **arguments
                )
            validator.assert_not_called()
        evidence_path.write_bytes(original_evidence)

        adversarial_summaries: list[tuple[str, dict[str, object]]] = []
        child_summary = json.loads(json.dumps(summary))
        child_summary["observed_child_thread_count"] = 1
        adversarial_summaries.append(("root-only exact V8", child_summary))
        missing_artifact = json.loads(json.dumps(summary))
        missing_artifact["artifacts"].pop(token_canary.ARTIFACT_LABELS[-1])
        adversarial_summaries.append(("artifact set", missing_artifact))
        stale_release = json.loads(json.dumps(summary))
        stale_release["prompt_release"]["startup_timeout_seconds"] = 119
        adversarial_summaries.append(("prompt release", stale_release))
        wrong_deadline = json.loads(json.dumps(summary))
        wrong_deadline["prompt_release"]["deadline_monotonic_ns"] += 1
        adversarial_summaries.append(("prompt release", wrong_deadline))
        bad_source = json.loads(json.dumps(summary))
        bad_source["source_separation_audit_sha256"] = "not-a-hash"
        adversarial_summaries.append(("source-separation", bad_source))
        for message, malformed in adversarial_summaries:
            with self.subTest(message=message), mock.patch.object(
                token_canary,
                "validate_attestation_document",
                return_value=malformed,
            ):
                with self.assertRaisesRegex(Exception, message):
                    run_matrix._verify_token_control_canary(
                        project, frozen, environment, **arguments
                    )

        stale_prompt = {**arguments, "prompt_protocol": {"version": "changed"}}
        with mock.patch.object(
            token_canary,
            "validate_attestation_document",
            return_value=summary,
        ):
            with self.assertRaisesRegex(Exception, "production prompt protocol is stale"):
                run_matrix._verify_token_control_canary(
                    project, frozen, environment, **stale_prompt
                )

        stale_components = {
            **arguments,
            "execution_components": {
                **execution_components,
                "runner_sha256": "0" * 64,
            },
        }
        with mock.patch.object(
            token_canary,
            "validate_attestation_document",
            return_value=summary,
        ):
            with self.assertRaisesRegex(
                Exception, "production execution components are stale"
            ):
                run_matrix._verify_token_control_canary(
                    project, frozen, environment, **stale_components
                )

        freeze_path = artifact_root / "freeze_check.json"
        freeze_path.write_text('{"tampered":true}\n', encoding="utf-8")
        with mock.patch.object(
            token_canary,
            "validate_attestation_document",
            return_value=summary,
        ):
            with self.assertRaisesRegex(Exception, "freeze_check has the wrong SHA-256"):
                run_matrix._verify_token_control_canary(
                    project, frozen, environment, **arguments
                )

    def test_package_runtime_projection_includes_only_required_split_artifacts(
        self,
    ) -> None:
        fixture = FrozenEnvironmentFixture(self.base)
        files = run_matrix.expected_packages_runtime_files(fixture.packages)
        compiled_prefix = "mathlib/.lake/build/lib/lean/"
        self.assertIn(compiled_prefix + "Mathlib.olean", files)
        self.assertIn(compiled_prefix + "Mathlib.olean.server", files)
        self.assertIn(compiled_prefix + "Mathlib.olean.private", files)
        self.assertIn(compiled_prefix + "Mathlib.ir", files)
        self.assertNotIn(compiled_prefix + "Mathlib.trace", files)
        self.assertEqual(
            len(files),
            sum(path.endswith(".lean") for path in files)
            + sum(path.endswith(".olean") for path in files)
            + sum(
                path.endswith(run_matrix.PACKAGE_COMPILED_SUPPORT_SUFFIXES)
                for path in files
            ),
        )

    def test_exact_tree_digest_changes_for_path_and_content(self) -> None:
        tree = self.base / "tree"
        tree.mkdir()
        (tree / "a").write_bytes(b"one")
        first = run_matrix.exact_tree_digest(tree)
        (tree / "a").write_bytes(b"two")
        second = run_matrix.exact_tree_digest(tree)
        self.assertNotEqual(first["tree_sha256"], second["tree_sha256"])
        (tree / "a").rename(tree / "b")
        third = run_matrix.exact_tree_digest(tree)
        self.assertNotEqual(second["tree_sha256"], third["tree_sha256"])

        (tree / "alias").symlink_to("b")
        fourth = run_matrix.exact_tree_digest(tree)
        self.assertEqual(fourth["regular_file_count"], 1)
        self.assertEqual(fourth["symlink_count"], 1)
        self.assertNotEqual(third["tree_sha256"], fourth["tree_sha256"])
        (tree / "alias").unlink()
        (tree / "alias").symlink_to("missing")
        with self.assertRaisesRegex(Exception, "broken or external symlink"):
            run_matrix.exact_tree_digest(tree)

    def test_task_catalog_rejects_construction_state_before_runs(self) -> None:
        root = self.base / "benchmark"
        _write_two_paper_task_records(root)
        task_path = root / "tasks" / "P01" / "T1" / "task.json"
        task = read_json(task_path)
        task["classification_frozen_before_runs"] = False
        write_json(task_path, task)
        manifest = read_json(root / "metadata" / "manifest.json")
        with self.assertRaisesRegex(Exception, "still under construction"):
            run_matrix.load_task_catalog(root, manifest)

    @mock.patch.object(
        run_matrix,
        "authenticate_runner_provider_gate_summary",
        return_value={},
    )
    def test_run_matrix_keeps_unique_startup_incident_in_rebuilt_jsonl(
        self, _provider_gate: mock.Mock
    ) -> None:
        root = self.base / "benchmark"
        project = self.base / "project"
        results = self.base / "results"
        for directory in (
            root / "metadata",
            project,
            self.base / "toolchain",
            self.base / "packages",
            self.base / "packages-runtime",
            self.base / "shared",
            self.base / "library-source",
            self.base / "library-olean",
        ):
            directory.mkdir(parents=True, exist_ok=True)
        for path in (self.base / "codex", self.base / "auth", self.base / "offline", self.base / "root.lean"):
            path.write_text("fixture\n", encoding="utf-8")

        task_ids = _write_two_paper_task_records(root)
        repetitions = ("rep-01", "rep-02", "rep-03")
        write_json(
            root / "metadata" / "config.json",
            {
                "repetitions": [{"id": repetition} for repetition in repetitions],
                "planned_counts_per_agent": {
                    "papers": 2,
                    "tasks": 6,
                    "repetitions_per_task": 3,
                    "conditions": 2,
                    "paired_assignments": 18,
                    "runs": 36,
                },
            },
        )
        pairs = []
        for task in task_ids:
            for repetition in repetitions:
                pair_id = f"{task}-{repetition}"
                pairs.append(
                    {
                        "pair_id": pair_id,
                        "task_id": task,
                        "repetition_id": repetition,
                        "condition_order": ["N", "L"],
                        "run_ids": [f"{pair_id}-N", f"{pair_id}-L"],
                    }
                )
        write_json(root / "metadata" / "run_order.json", {"pairs": pairs})
        manifest = read_json(root / "metadata" / "manifest.json")
        catalog = run_matrix.load_task_catalog(root, manifest)
        self.assertEqual(run_matrix.corpus_slug(manifest), "p01-p02")
        self.assertEqual(len(catalog), 6)
        expanded = run_matrix.assignments_from_order(
            {"pairs": pairs}, catalog, repetitions
        )
        self.assertEqual(len(expanded), 36)
        p02_assignment = next(
            assignment
            for assignment in expanded
            if assignment["task_id"] == "P02-T1"
        )
        self.assertEqual(p02_assignment["paper_sha256"], P02_PAPER_SHA256)
        self.assertEqual(p02_assignment["target_file"], "tasks/P02/T1/Target.lean")
        with self.assertRaisesRegex(Exception, "exact task/repetition matrix"):
            run_matrix.assignments_from_order(
                {"pairs": pairs[:-1]}, catalog, repetitions
            )
        post_use_system_run = pairs[0]["run_ids"][1]
        args = argparse.Namespace(
            benchmark_root=root,
            project_root=project,
            results_root=results,
            codex=self.base / "codex",
            auth_file=self.base / "auth",
            offline_shell=self.base / "offline",
            library_root_file=self.base / "root.lean",
            toolchain_root=self.base / "toolchain",
            packages_root=self.base / "packages",
            packages_runtime_root=self.base / "packages-runtime",
            shared_olean_root=self.base / "shared",
            library_source=self.base / "library-source",
            library_olean=self.base / "library-olean",
            time_limit_seconds=1800,
            allocation_end_epoch=4_102_444_800,
            allocation_guard_seconds=600,
            stop_after_paper="P01",
            force=False,
        )
        attempts: dict[str, int] = {}
        double_startup_runs: set[str] = set()
        freeze_check = _allocation_freeze_check()

        def fake_command(
            _args: argparse.Namespace,
            assignment: dict,
            attempt_jsonl: Path,
            attempt_output: Path,
            _base: Path,
        ) -> list[str]:
            return [
                "fake",
                json.dumps(assignment),
                str(attempt_output),
                str(attempt_jsonl),
            ]

        def fake_run(command: list[str], **_kwargs: object) -> subprocess.CompletedProcess:
            assignment = json.loads(command[1])
            output = Path(command[2])
            transcript = Path(command[3])
            run_id = assignment["run_id"]
            attempts[run_id] = attempts.get(run_id, 0) + 1
            agent_log = results / "logs" / f"{run_id}.agent.log"
            agent_log.write_text(
                f"{run_id} attempt {attempts[run_id]}\n", encoding="utf-8"
            )
            startup_incident = (
                len(attempts) == 1 and attempts[run_id] == 1
            ) or run_id in double_startup_runs
            post_use_system = run_id == post_use_system_run
            record = {
                "schema_version": 1,
                "kind": "highambench-run",
                **run_matrix._planned_assignment_record_identity(assignment),
                "agent": {
                    key: freeze_check["agent"][key]
                    for key in ("id", "version", "model", "reasoning_effort")
                },
                "environment_id": freeze_check["environment_id"],
                "frozen_run_verification": {
                    "freeze_check_sha256": run_matrix.canonical_document_digest(
                        freeze_check
                    ),
                    "freeze_check": json.loads(json.dumps(freeze_check)),
                },
                "limits": {
                    "time_seconds": freeze_check["limits"]["wall_clock_seconds"],
                    "model_tokens": freeze_check["limits"]["total_model_tokens"],
                    "prompt_startup_seconds": freeze_check["limits"][
                        "prompt_startup_timeout_seconds"
                    ],
                    "post_acceptance_usage_grace_seconds": 2.0,
                },
                "pass": not startup_incident and not post_use_system,
                "scored": not startup_incident,
                "agent_exit_code": 1 if startup_incident else 0,
                "failure_code": (
                    "SYSTEM_ERROR" if startup_incident or post_use_system else None
                ),
                "failure_note": (
                    "startup fault"
                    if startup_incident
                    else "post-start fault"
                    if post_use_system
                    else ""
                ),
                "useful_work_started": not startup_incident,
                "agent_log": str(agent_log),
                "validation_log": None,
            }
            if not startup_incident:
                record["protocol"] = {"complete": True}
                if post_use_system:
                    record["token_usage"] = {
                        "usage_scope": (
                            "rooted_attempt_thread_tree_completed_responses"
                        ),
                        "measurement_exact": True,
                        "submission_boundary_exact": False,
                        "submission_boundary": None,
                        "drain_complete": True,
                        "tree_quiescent": True,
                        "active_thread_ids": [],
                        "unresolved_thread_ids": [],
                        "invalid_reasons": [],
                    }
                    record["ultra_submission_boundary"] = {"verified": False}
                else:
                    record["token_usage"] = {
                        "usage_scope": (
                            "rooted_attempt_thread_tree_completed_responses"
                        ),
                        "measurement_exact": True,
                        "submission_boundary_exact": True,
                        "drain_complete": False,
                        "tree_quiescent": False,
                        "stop_reason": "first_valid_proof",
                        "root_thread_id": "root",
                        "active_thread_ids": ["root"],
                        "unresolved_thread_ids": [],
                        "invalid_reasons": [],
                        "submission_boundary": {
                            **_exact_nested_submission_boundary_fixture(),
                            "authenticated": True,
                            "status": "accepted",
                            "exact": True,
                            "root_only": True,
                            "descendants_quiescent": True,
                            "later_model_response_possible": False,
                        },
                    }
                    exact_boundary = record["token_usage"]["submission_boundary"]
                    record["ultra_submission_boundary"] = _seal_retained_request(
                        results / "logs",
                        exact_boundary,
                        label=run_id,
                    )
            write_json(output, record)
            transcript.write_text(
                json.dumps({"run_id": run_id, "attempt": attempts[run_id]}) + "\n",
                encoding="utf-8",
            )
            return subprocess.CompletedProcess(command, 1 if startup_incident else 0)

        with mock.patch.object(
            run_matrix,
            "verify_frozen_run_environment",
            return_value=freeze_check,
        ), mock.patch.object(
            run_matrix,
            "authenticate_runner_provider_gate_summary",
            return_value={},
        ), mock.patch.object(run_matrix, "runner_command", side_effect=fake_command), mock.patch.object(
            run_matrix.subprocess, "run", side_effect=fake_run
        ), mock.patch.dict(
            os.environ, {run_matrix.SLURM_JOB_ID_ENV: "1505507"}
        ), mock.patch.object(
            run_matrix.platform, "node", return_value="watgpu108"
        ), mock.patch.object(
            run_matrix, "_current_cpu_affinity", return_value=[8, 9, 56, 57]
        ), mock.patch.object(
            run_matrix,
            "_slurm_scheduler_sharing",
            return_value=_scheduler_sharing(),
        ), mock.patch.object(
            run_matrix,
            "_slurm_gpu_provenance",
            return_value=_slurm_gpu_provenance(),
        ):
            self.assertEqual(
                run_matrix.run(args), run_matrix.CHUNK_INCOMPLETE_EXIT_CODE
            )

        p01_attempts = dict(attempts)
        self.assertEqual(len(p01_attempts), 18)
        self.assertTrue(all(run_id.startswith("P01-") for run_id in p01_attempts))
        boundary_status = read_json(results / "last_chunk_status.json")
        self.assertEqual(
            boundary_status["status"], "stopped_after_requested_paper"
        )
        self.assertEqual(boundary_status["requested_paper_id"], "P01")
        self.assertEqual(boundary_status["next_paper_id"], "P02")
        self.assertTrue(boundary_status["next_run_id"].startswith("P02-"))

        # Retry incidents are canonical self-hashed derivations of one exact
        # attempt record and raw transcript. Rebuild authenticates every link.
        authenticated_assignments = [
            {**assignment, "backend_seed": None} for assignment in expanded
        ]
        first_run_id = pairs[0]["run_ids"][0]
        incident_path = results / "incidents" / f"{first_run_id}.attempt-1.json"
        incident = run_matrix._authenticate_matrix_incident(
            results,
            incident_path,
            authenticated_assignments[0],
            freeze_check,
            expected_attempt=1,
        )
        self.assertEqual(
            incident["matrix_incident"],
            {
                "status": "retryable_pre_prompt_system_error",
                "retry_allowed": True,
                "scored": False,
                "final_assignment_record_written": False,
            },
        )
        self.assertEqual(
            incident[run_matrix.MATRIX_INCIDENT_SHA256_FIELD],
            run_matrix.matrix_incident_digest(incident),
        )
        self.assertEqual(
            set(incident["incident_provenance"]),
            {
                "schema_version",
                "planned_assignment",
                "matrix_attempt",
                "source_attempt",
                "transcript",
            },
        )
        frozen_source = read_json(
            results / incident["incident_provenance"]["source_attempt"]["path"]
        )
        self.assertEqual(
            frozen_source["agent_log"],
            f"attempts/{first_run_id}.attempt-1.agent_log.artifact",
        )
        self.assertEqual(
            (results / frozen_source["agent_log"]).read_text(encoding="utf-8"),
            f"{first_run_id} attempt 1\n",
        )
        self.assertEqual(
            (results / "logs" / f"{first_run_id}.agent.log").read_text(
                encoding="utf-8"
            ),
            f"{first_run_id} attempt 2\n",
        )
        self.assertEqual(
            (results / incident["agent_log"]).read_bytes(),
            (results / frozen_source["agent_log"]).read_bytes(),
        )
        self.assertEqual(
            frozen_source["agent_log_sha256"],
            sha256_file(results / frozen_source["agent_log"]),
        )

        def rebuild() -> None:
            with mock.patch.object(
                run_matrix,
                "authenticate_runner_provider_gate_summary",
                return_value={},
            ):
                run_matrix._rebuild_jsonl(
                    results / "records",
                    results / "incidents",
                    authenticated_assignments,
                    results / "runs.jsonl",
                    results_root=results,
                    freeze_check=freeze_check,
                )

        source_log_path = results / frozen_source["agent_log"]
        incident_log_path = results / incident["agent_log"]
        source_log_bytes = source_log_path.read_bytes()
        incident_log_bytes = incident_log_path.read_bytes()
        source_log_path.write_bytes(b"same two-sided tamper\n")
        incident_log_path.write_bytes(b"same two-sided tamper\n")
        with self.assertRaisesRegex(Exception, "source agent_log digest"):
            rebuild()
        source_log_path.write_bytes(source_log_bytes)
        incident_log_path.write_bytes(incident_log_bytes)

        incident_bytes = incident_path.read_bytes()
        tampered_incident = json.loads(incident_bytes)
        tampered_incident["failure_note"] = "tampered without resealing"
        write_json(incident_path, tampered_incident)
        with self.assertRaisesRegex(Exception, "incident self-hash"):
            rebuild()
        incident_path.write_bytes(incident_bytes)

        source_path = results / incident["incident_provenance"]["source_attempt"]["path"]
        source_bytes = source_path.read_bytes()
        source_path.write_bytes(source_bytes + b" ")
        with self.assertRaisesRegex(Exception, "source or transcript digest"):
            rebuild()
        source_path.write_bytes(source_bytes)

        resealed_source_tampers = (
            (
                "assignment",
                lambda value: value.__setitem__("task_id", "P01-T2"),
                "wrong planned task_id",
            ),
            (
                "agent",
                lambda value: value["agent"].__setitem__("version", "stale"),
                "stale agent provenance",
            ),
            (
                "environment",
                lambda value: value.__setitem__("environment_id", "stale"),
                "stale environment identity",
            ),
            (
                "freeze",
                lambda value: value.__setitem__("frozen_run_verification", {}),
                "stale release/environment/freeze provenance",
            ),
            (
                "hardware",
                lambda value: value["allocation_hardware"].__setitem__(
                    "record_sha256", "0" * 64
                ),
                "descriptor self-hash",
            ),
        )
        for label, mutate, message in resealed_source_tampers:
            with self.subTest(resealed_incident_source=label):
                source_tamper = json.loads(source_bytes)
                mutate(source_tamper)
                write_json(source_path, source_tamper)
                resealed_incident = json.loads(incident_bytes)
                resealed_incident["incident_provenance"]["source_attempt"][
                    "sha256"
                ] = sha256_file(source_path)
                resealed_incident[run_matrix.MATRIX_INCIDENT_SHA256_FIELD] = (
                    run_matrix.matrix_incident_digest(resealed_incident)
                )
                write_json(incident_path, resealed_incident)
                with self.assertRaisesRegex(Exception, message):
                    rebuild()
                source_path.write_bytes(source_bytes)
                incident_path.write_bytes(incident_bytes)

        transcript_path = results / incident["incident_provenance"]["transcript"]["path"]
        transcript_bytes = transcript_path.read_bytes()
        transcript_path.write_bytes(transcript_bytes + b" ")
        with self.assertRaisesRegex(Exception, "source or transcript digest"):
            rebuild()
        transcript_path.write_bytes(transcript_bytes)

        identity_tamper = json.loads(incident_bytes)
        identity_tamper["incident_provenance"]["planned_assignment"]["task_id"] = (
            "P01-T2"
        )
        identity_tamper[run_matrix.MATRIX_INCIDENT_SHA256_FIELD] = (
            run_matrix.matrix_incident_digest(identity_tamper)
        )
        write_json(incident_path, identity_tamper)
        with self.assertRaisesRegex(Exception, "planned identity provenance"):
            rebuild()
        incident_path.write_bytes(incident_bytes)
        rebuild()

        # A fresh 12-hour resume authenticates all saved incidents before it
        # constructs a runner command or starts any hosted subprocess.
        resume_tamper = json.loads(incident_bytes)
        resume_tamper["failure_note"] = "resume tamper"
        write_json(incident_path, resume_tamper)
        attempts_before_incident_tamper = dict(attempts)
        with mock.patch.object(
            run_matrix,
            "verify_frozen_run_environment",
            return_value=freeze_check,
        ), mock.patch.object(
            run_matrix, "runner_command", side_effect=fake_command
        ) as command_mock, mock.patch.object(
            run_matrix.subprocess, "run", side_effect=fake_run
        ) as subprocess_mock:
            with self.assertRaisesRegex(Exception, "incident self-hash"):
                run_matrix.run(args)
        self.assertEqual(command_mock.call_count, 0)
        self.assertEqual(subprocess_mock.call_count, 0)
        self.assertEqual(attempts, attempts_before_incident_tamper)
        incident_path.write_bytes(incident_bytes)

        unmatched_incident = results / "incidents" / "foreign.attempt-1.json"
        write_json(unmatched_incident, {"kind": "highambench-run"})
        with mock.patch.object(
            run_matrix,
            "verify_frozen_run_environment",
            return_value=freeze_check,
        ), mock.patch.object(
            run_matrix, "runner_command", side_effect=fake_command
        ) as command_mock, mock.patch.object(
            run_matrix.subprocess, "run", side_effect=fake_run
        ) as subprocess_mock:
            with self.assertRaisesRegex(Exception, "unmatched matrix incident"):
                run_matrix.run(args)
        self.assertEqual(command_mock.call_count, 0)
        self.assertEqual(subprocess_mock.call_count, 0)
        unmatched_incident.unlink()

        # A corrupted final anywhere in the authenticated P01 boundary fails
        # before either a runner command or hosted subprocess can be started.
        tampered_path = results / "records" / f"{pairs[1]['run_ids'][0]}.json"
        untampered = read_json(tampered_path)
        tampered = json.loads(json.dumps(untampered))
        tampered["failure_note"] = "content changed without resealing"
        write_json(tampered_path, tampered)
        attempts_before_corrupt_resume = dict(attempts)
        with mock.patch.object(
            run_matrix,
            "verify_frozen_run_environment",
            return_value=freeze_check,
        ), mock.patch.object(
            run_matrix, "runner_command", side_effect=fake_command
        ) as command_mock, mock.patch.object(
            run_matrix.subprocess, "run", side_effect=fake_run
        ) as subprocess_mock, mock.patch.dict(
            os.environ, {run_matrix.SLURM_JOB_ID_ENV: "1505508"}
        ):
            with self.assertRaisesRegex(Exception, "self-hash"):
                run_matrix.run(args)
        self.assertEqual(command_mock.call_count, 0)
        self.assertEqual(subprocess_mock.call_count, 0)
        self.assertEqual(attempts, attempts_before_corrupt_resume)
        self.assertNotEqual(
            read_json(results / "last_chunk_status.json")["status"],
            "matrix_complete",
        )
        write_json(tampered_path, untampered)

        args.stop_after_paper = None
        with mock.patch.object(
            run_matrix,
            "verify_frozen_run_environment",
            return_value=freeze_check,
        ), mock.patch.object(
            run_matrix, "runner_command", side_effect=fake_command
        ), mock.patch.object(
            run_matrix.subprocess, "run", side_effect=fake_run
        ), mock.patch.dict(
            os.environ, {run_matrix.SLURM_JOB_ID_ENV: "1505508"}
        ), mock.patch.object(
            run_matrix.platform, "node", return_value="watgpu108"
        ), mock.patch.object(
            run_matrix, "_current_cpu_affinity", return_value=[8, 9, 56, 57]
        ), mock.patch.object(
            run_matrix,
            "_slurm_scheduler_sharing",
            return_value=_scheduler_sharing(),
        ), mock.patch.object(
            run_matrix,
            "_slurm_gpu_provenance",
            return_value=_slurm_gpu_provenance(),
        ):
            self.assertEqual(run_matrix.run(args), 0)
        self.assertEqual(
            {run_id: count for run_id, count in attempts.items() if run_id.startswith("P01-")},
            p01_attempts,
        )

        rows = [json.loads(line) for line in (results / "runs.jsonl").read_text().splitlines()]
        self.assertEqual(len(rows), 37)
        self.assertEqual(len({row["run_id"] for row in rows}), 37)
        self.assertEqual(rows[0]["failure_code"], "SYSTEM_ERROR")
        self.assertEqual(rows[0]["planned_run_id"], pairs[0]["run_ids"][0])
        self.assertEqual(rows[1]["run_id"], pairs[0]["run_ids"][0])
        self.assertIsNone(rows[1]["failure_code"])
        allocation_descriptor = rows[0]["allocation_hardware"]
        self.assertEqual(allocation_descriptor["job_id"], "1505507")
        self.assertTrue(
            all(
                row["allocation_hardware"]["job_id"]
                == ("1505507" if row.get("planned_run_id", row["run_id"]).startswith("P01-") else "1505508")
                for row in rows
            )
        )
        attempt_records = [
            read_json(path) for path in sorted((results / "attempts").glob("*.json"))
        ]
        self.assertEqual(len(attempt_records), 37)
        self.assertTrue(
            all(
                record["allocation_hardware"]["job_id"]
                == ("1505507" if record.get("planned_run_id", record["run_id"]).startswith("P01-") else "1505508")
                for record in attempt_records
            )
        )
        final_records = [
            read_json(path) for path in sorted((results / "records").glob("*.json"))
        ]
        self.assertTrue(
            all(
                record[run_matrix.MATRIX_RECORD_SHA256_FIELD]
                == run_matrix.matrix_record_digest(record)
                for record in final_records
            )
        )
        post_use_row = next(row for row in rows if row["run_id"] == post_use_system_run)
        self.assertEqual(post_use_row["failure_code"], "SYSTEM_ERROR")
        self.assertTrue(post_use_row["useful_work_started"])
        self.assertEqual(attempts[post_use_system_run], 1)

        last_run_id = pairs[-1]["run_ids"][-1]
        (results / "records" / f"{last_run_id}.json").unlink()
        hardware_path = results / allocation_descriptor["path"]
        attempts_before_chunk_stop = dict(attempts)
        args.allocation_end_epoch = 1001
        with mock.patch.object(
            run_matrix,
            "verify_frozen_run_environment",
            return_value=freeze_check,
        ), mock.patch.object(
            run_matrix, "runner_command", side_effect=fake_command
        ), mock.patch.object(
            run_matrix.subprocess, "run", side_effect=fake_run
        ), mock.patch.object(
            run_matrix.time, "time", return_value=1000.0
        ), mock.patch.dict(
            os.environ, {run_matrix.SLURM_JOB_ID_ENV: "1505508"}
        ), mock.patch.object(
            run_matrix.platform, "node", return_value="watgpu108"
        ), mock.patch.object(
            run_matrix, "_current_cpu_affinity", return_value=[8, 9, 56, 57]
        ), mock.patch.object(
            run_matrix,
            "_slurm_scheduler_sharing",
            return_value=_scheduler_sharing(),
        ), mock.patch.object(
            run_matrix,
            "_slurm_gpu_provenance",
            return_value=_slurm_gpu_provenance(),
        ):
            self.assertEqual(
                run_matrix.run(args), run_matrix.CHUNK_INCOMPLETE_EXIT_CODE
            )
        self.assertEqual(attempts, attempts_before_chunk_stop)
        self.assertTrue(hardware_path.is_file())
        self.assertFalse((results / "records" / f"{last_run_id}.json").exists())
        chunk_status = read_json(results / "last_chunk_status.json")
        self.assertEqual(chunk_status["status"], "stopped_before_allocation_deadline")
        self.assertEqual(chunk_status["next_run_id"], last_run_id)

        # Two consecutive failures before useful work are both incidents.  The
        # single allowed retry is exhausted without manufacturing a final.
        double_startup_runs.add(last_run_id)
        attempts_before_double_startup = attempts[last_run_id]
        args.allocation_end_epoch = 4_102_444_800
        with mock.patch.object(
            run_matrix,
            "verify_frozen_run_environment",
            return_value=freeze_check,
        ), mock.patch.object(
            run_matrix, "runner_command", side_effect=fake_command
        ), mock.patch.object(
            run_matrix.subprocess, "run", side_effect=fake_run
        ), mock.patch.dict(
            os.environ, {run_matrix.SLURM_JOB_ID_ENV: "1505508"}
        ), mock.patch.object(
            run_matrix.platform, "node", return_value="watgpu108"
        ), mock.patch.object(
            run_matrix, "_current_cpu_affinity", return_value=[8, 9, 56, 57]
        ), mock.patch.object(
            run_matrix,
            "_slurm_scheduler_sharing",
            return_value=_scheduler_sharing(),
        ), mock.patch.object(
            run_matrix,
            "_slurm_gpu_provenance",
            return_value=_slurm_gpu_provenance(),
        ):
            with self.assertRaisesRegex(Exception, "one permitted startup"):
                run_matrix.run(args)
        self.assertEqual(attempts[last_run_id], attempts_before_double_startup + 2)
        self.assertFalse((results / "records" / f"{last_run_id}.json").exists())
        self.assertTrue((results / run_matrix.ACTIVE_RUN_MARKER).is_file())
        self.assertTrue(
            (results / "incidents" / f"{last_run_id}.attempt-1.json").is_file()
        )
        self.assertTrue(
            (results / "incidents" / f"{last_run_id}.attempt-2.json").is_file()
        )

        # Even if an operator incorrectly removes the active marker, terminal
        # and interrupted-retry incident states fail before another provider call.
        (results / run_matrix.ACTIVE_RUN_MARKER).unlink()
        for expected_message, remove_terminal in (
            ("terminal or unscorable matrix incident", False),
            ("interrupted startup retry", True),
        ):
            if remove_terminal:
                (results / "incidents" / f"{last_run_id}.attempt-2.json").unlink()
            with mock.patch.object(
                run_matrix,
                "verify_frozen_run_environment",
                return_value=freeze_check,
            ), mock.patch.object(
                run_matrix, "runner_command", side_effect=fake_command
            ) as command_mock, mock.patch.object(
                run_matrix.subprocess, "run", side_effect=fake_run
            ) as subprocess_mock:
                with self.assertRaisesRegex(Exception, expected_message):
                    run_matrix.run(args)
            self.assertEqual(command_mock.call_count, 0)
            self.assertEqual(subprocess_mock.call_count, 0)

        # A correctly sealed unscorable-useful-work incident is likewise a
        # terminal resume state, independently of the active marker.
        retry_incident_path = (
            results / "incidents" / f"{last_run_id}.attempt-1.json"
        )
        retry_incident_path.unlink()
        unscorable_source_path = (
            results / "attempts" / f"{last_run_id}.attempt-1.json"
        )
        unscorable_transcript_path = unscorable_source_path.with_suffix(".jsonl")
        unscorable_source = read_json(unscorable_source_path)
        unscorable_source.pop("agent_log_sha256", None)
        unscorable_source.update(
            {
                "pass": False,
                "scored": False,
                "failure_code": "SYSTEM_ERROR",
                "failure_note": "useful work ended without exact accounting",
                "useful_work_started": True,
                "token_usage": {
                    "measurement_exact": False,
                    "submission_boundary_exact": False,
                },
                "agent_log": str(results / "logs" / f"{last_run_id}.agent.log"),
            }
        )
        (results / "logs" / f"{last_run_id}.agent.log").write_text(
            "unscorable useful work\n", encoding="utf-8"
        )
        write_json(unscorable_source_path, unscorable_source)
        unscorable_transcript_path.write_text(
            '{"unscorable":true}\n', encoding="utf-8"
        )
        unscorable_path = run_matrix._preserve_matrix_incident(
            unscorable_source,
            results / "incidents",
            results_root=results,
            assignment=authenticated_assignments[-1],
            attempt=1,
            attempt_output=unscorable_source_path,
            attempt_jsonl=unscorable_transcript_path,
            status="aborted_after_unscorable_useful_work",
            retry_allowed=False,
            freeze_check=freeze_check,
        )
        unscorable_incident = read_json(unscorable_path)
        self.assertEqual(
            unscorable_incident[run_matrix.MATRIX_INCIDENT_SHA256_FIELD],
            run_matrix.matrix_incident_digest(unscorable_incident),
        )
        with mock.patch.object(
            run_matrix,
            "verify_frozen_run_environment",
            return_value=freeze_check,
        ), mock.patch.object(
            run_matrix, "runner_command", side_effect=fake_command
        ) as command_mock, mock.patch.object(
            run_matrix.subprocess, "run", side_effect=fake_run
        ) as subprocess_mock:
            with self.assertRaisesRegex(
                Exception, "terminal or unscorable matrix incident"
            ):
                run_matrix.run(args)
        self.assertEqual(command_mock.call_count, 0)
        self.assertEqual(subprocess_mock.call_count, 0)


if __name__ == "__main__":
    unittest.main()
