from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
from types import SimpleNamespace
from unittest import mock


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import render_report as render_report_module  # noqa: E402
from common import BenchmarkToolError  # noqa: E402
from render_report import (  # noqa: E402
    CONSTRUCTION_TOOL_PATHS,
    PACKAGES_RUNTIME_ROOT,
    PRUNED_LIBRARY_OLEAN_ROOT,
    ReportError,
    _hook_trust_report_rows,
    load_report_inputs,
    main,
    render_report,
    _rederive_prompt_release_evidence,
    _rederive_ultra_accounting_evidence,
    _validate_matrix_record_summary,
    _validate_ultra_accounting_summary,
    _validate_ultra_boundary_summary,
    _validated_prompt_protocol,
)
from paper_bencmark.highambench.tools.tests.test_task_tags import (  # noqa: E402
    base_t4_task,
)
from paper_bencmark.highambench.tools.tests.test_render_p01_report import (  # noqa: E402
    install_accepted_provider_gate_fixture,
    nested_submission_wire_fixture,
    token_canary_projection_fixture,
    ultra_canary_projection_fixture,
    upgrade_token_gate_to_two_call_compaction_fixture,
)


PRODUCTION_PROMPT_PROTOCOL = {"version": "fixture-production-prompt-v1"}
PRODUCTION_EXECUTION_COMPONENTS = {
    field: str(index) * 64
    for index, field in enumerate(
        render_report_module.run_matrix.EXECUTION_COMPONENT_FIELDS, start=1
    )
}


def natural_projection_evidence() -> dict:
    zero = {
        "input_tokens": 0,
        "cached_input_tokens": 0,
        "cache_write_input_tokens": 0,
        "output_tokens": 0,
        "reasoning_output_tokens": 0,
        "total_tokens": 0,
    }
    raw = {
        "input_tokens": 10,
        "cached_input_tokens": 2,
        "cache_write_input_tokens": 0,
        "output_tokens": 3,
        "reasoning_output_tokens": 1,
        "total_tokens": 13,
    }
    policy = (
        render_report_module.ultra_canary.codex_isolated.ultra_fork_policy_static_record()
    )
    projection = {
        "accounting_projection_schema_version": (
            render_report_module.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "spawn_binding_source": "raw_function_call.call_id=subAgentActivity.id",
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
        "spawn_linkage_complete": True,
        "descendant_accounting_complete": True,
        "cumulative_projection_complete": True,
        "fork_policy_complete": True,
        "accounting_complete": True,
        "fork_policy": {**policy, "call_evidence": [], "complete": True},
        "root_thread_id": "root",
        "thread_count": 1,
        "response_count": 1,
        "call_count": 1,
        "response_ids": ["response-1"],
        "input_tokens": 10,
        "cached_input_tokens": 2,
        "cache_write_input_tokens": 0,
        "output_tokens": 3,
        "reasoning_output_tokens": 1,
        "model_tokens": 13,
        "submission_boundary_exact": False,
        "submission_boundary": None,
        "thread_accounting": [
            {
                "thread_id": "root",
                "parent_thread_id": None,
                "response_count": 1,
                **raw,
                "spawn_call_id": None,
                "spawn_parent_turn_id": None,
                "spawn_parent_response_id": None,
                "spawn_fork_turns": None,
                "spawn_fork_semantics": None,
                "spawn_binding_status": "root_zero",
                "expected_cumulative_baseline": zero,
                "expected_cumulative_projection": raw,
                "full_cumulative_projection": raw,
                "last_cumulative": raw,
                "cumulative_observation_count": 1,
                "observed_cumulative_baseline": zero,
                "cumulative_baseline_matches_expected": True,
                "cumulative_projection_status": "matched_full_projection",
                "cumulative_projection_match": True,
                "cumulative_projection_exempt_response_id": None,
                "cumulative_projection_exempt_response_usage": None,
                "accounting_complete": True,
            }
        ],
    }
    with tempfile.TemporaryDirectory() as temporary:
        usage_path = (Path(temporary) / "natural.usage.json").resolve()
        usage: dict = {
            **raw,
            "model_tokens": raw["total_tokens"],
            "response_count": 1,
            "notification_sequence": 1,
            "response_ids": ["response-1"],
            "root_thread_id": "root",
            "interrupt_requested": False,
            "pending_interrupt_response_count": 0,
            "invalid_reasons": [],
            "measurement_exact": True,
            "first_crossing": None,
        }
        boundary = {
            "response_id": "response-1",
            "raw_response_notification_sequence": 1,
            "request_published_at_monotonic_ns": 1_020_000_000,
            "request_published_at_unix_ns": 2_020_000_000,
        }
        install_accepted_provider_gate_fixture(
            usage_path=usage_path,
            usage=usage,
            boundary=boundary,
            run_id="natural-projection-fixture",
            token_limit=300_000,
            root_thread_id="root",
            turn_id="turn-1",
            response_id="response-1",
            prompt_release_record={
                "protocol_version": "highambench-prompt-release-v1",
                "kind": "highambench_prompt_released",
            },
            prompt_sha256="a" * 64,
            request_published_monotonic_ns=1_020_000_000,
            request_published_unix_ns=2_020_000_000,
            raw_response_monotonic_ns=1_019_000_000,
            raw_response_unix_ns=2_019_000_000,
        )
        terminal = dict(usage["provider_token_gate"]["terminal"])
        terminal.update(
            {
                "close_reason": "natural_end",
                "crossing": None,
                "crossing_closed": False,
            }
        )
        usage["provider_token_gate"]["live"] = terminal
        usage["provider_token_gate"]["terminal"] = terminal
        usage["adapter_teardown"]["immediate"] = False
        usage["adapter_teardown"]["signal"] = None
        usage["adapter_teardown"]["returncode"] = 0
        usage.update(
            {
                "submission_boundary_exact": False,
                "submission_boundary": None,
                "stop_reason": None,
                "drain_complete": True,
                "tree_quiescent": True,
            }
        )
        projection.update(usage)
    return projection


def digest_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def document_digest(value: dict) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()


def token_canary_projection() -> dict:
    zero = {
        field: 0
        for field in (
            "input_tokens",
            "cached_input_tokens",
            "cache_write_input_tokens",
            "output_tokens",
            "reasoning_output_tokens",
            "total_tokens",
        )
    }
    projection = {
        "accounting_projection_schema_version": (
            render_report_module.token_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "spawn_binding_source": "raw_function_call.call_id=subAgentActivity.id",
        "root_thread_id": "root",
        "root_expected_cumulative_baseline": zero,
        "root_cumulative_projection_status": "matched_full_projection",
        "spawn_linkage_complete": True,
        "descendant_accounting_complete": True,
        "cumulative_projection_complete": True,
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
            **render_report_module.ultra_canary.codex_isolated.ultra_fork_policy_static_record(),
            "call_evidence": [],
            "complete": True,
        },
        "accounting_complete": True,
        "root_only": True,
    }
    projection["projection_payload_sha256"] = document_digest(projection)
    return projection


def token_canary_prompt_release() -> dict:
    released = 1_000_000_000
    wall = 300
    hashes = {"ready": "a" * 64, "go": "b" * 64, "release": "c" * 64}
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
                "path": f"/trusted/logs/canary.prompt-{label}.json",
                "file_sha256": ("c" * 64, "a" * 64, "b" * 64)[index],
                "record_sha256": hashes[label],
            }
            for index, label in enumerate(("ready", "go", "release"))
        },
        "canonical_encoding": "compact_sorted_key_utf8_json_newline",
        "sealed_mode": "0444",
        "handshake_nonce": "a" * 64,
        "root_thread_id": "root",
        "effective_prompt_sha256": "b" * 64,
        "effective_prompt_bytes": 12001,
        "turn_start_request_sha256": "c" * 64,
        "turn_start_wire_verified": True,
        "command_binding_verified": True,
        "root_identity_verified": True,
        "ready_sha256": hashes["ready"],
        "go_sha256": hashes["go"],
        "release_sha256": hashes["release"],
        "measurement_time_origin": "RELEASED.released_at_monotonic_ns",
        "released_at_monotonic_ns": released,
        "deadline_monotonic_ns": released + wall * 1_000_000_000,
        "deadline_derivation": (
            "released_at_monotonic_ns + wall_time_seconds*1000000000"
        ),
        "wall_time_seconds": wall,
        "actual_stop_seconds": 5.75,
        "token_crossing_within_deadline": True,
        "first_valid_seconds": None,
        "submission_boundary": None,
        "sanitized_provider_gate_crossing": True,
        "top_level_artifact_count_unchanged": len(
            render_report_module.token_canary.ARTIFACT_LABELS
        ),
    }


def ultra_canary_projection() -> dict:
    codex = render_report_module.ultra_canary.codex_isolated
    static = codex.ultra_fork_policy_static_record()
    allowed_id = "call_allowed_root"
    blocked_ids = ["call_blocked_child", "call_blocked_root"]

    def call(
        call_id: str,
        *,
        parent: str,
        turn_id: str,
        response_id: str,
        allowed: bool,
    ) -> dict:
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
            "hook_run_id": f"pre-tool-use:0:{static['source_path']}:{call_id}",
            "hook_source_path": static["source_path"],
            "hook_thread_id": parent,
            "hook_turn_id": turn_id,
            "hook_started_observed": True,
            "hook_started_count": 1,
            "hook_completed_observed": True,
            "hook_completed_count": 1,
            "hook_status": "completed" if allowed else "blocked",
            "decision": "allow" if allowed else "block",
            "feedback": (
                None
                if allowed
                else codex.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
                    call_id=call_id
                )
            ),
            "resolution_status": (
                "resolved_child"
                if allowed
                else codex.ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS
            ),
            "child_activity_observed": allowed,
        }

    projection = {
        "accounting_projection_schema_version": (
            render_report_module.ultra_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "spawn_binding_source": "raw_function_call.call_id=subAgentActivity.id",
        "raw_spawn_call_ids": [allowed_id, *blocked_ids],
        "activity_spawn_call_ids": [allowed_id],
        "collab_spawn_call_ids": [allowed_id],
        "resolved_spawn_call_ids": [allowed_id],
        "failed_spawn_call_ids": blocked_ids,
        "policy_blocked_spawn_call_ids": blocked_ids,
        "unresolved_spawn_call_ids": [],
        "unsupported_spawn_call_ids": [],
        "inference_child_thread_ids": ["child"],
        "hook_observed_spawn_call_ids": [allowed_id, *blocked_ids],
        "hook_allowed_spawn_call_ids": [allowed_id],
        "hook_blocked_spawn_call_ids": blocked_ids,
        "hook_invalid_spawn_call_ids": [],
        "spawn_parent_response_ids": {allowed_id: "root-response"},
        "pre_spawn_completed_root_response_counts": {allowed_id: 2},
        "raw_call_activity_id_match": True,
        "completed_root_response_before_spawn": True,
        "fork_turns_all_child_thread_count": 1,
        "nonzero_inherited_baseline_child_thread_ids": ["child"],
        "spawn_linkage_complete": True,
        "descendant_accounting_complete": True,
        "cumulative_projection_complete": True,
        "fork_policy_complete": True,
        "accounting_complete": True,
        "fork_policy": {
            **static,
            "call_evidence": [
                call(
                    allowed_id,
                    parent="root",
                    turn_id="root-turn",
                    response_id="root-response",
                    allowed=True,
                ),
                call(
                    "call_blocked_child",
                    parent="child",
                    turn_id="child-turn",
                    response_id="child-blocked-response",
                    allowed=False,
                ),
                call(
                    "call_blocked_root",
                    parent="root",
                    turn_id="root-turn",
                    response_id="root-blocked-response",
                    allowed=False,
                ),
            ],
            "complete": True,
        },
        "thread_accounting": [{"thread_id": "child"}, {"thread_id": "root"}],
    }
    projection["projection_payload_sha256"] = document_digest(projection)
    return projection


def ultra_canary_summary(descriptor: dict, projection: dict | None = None) -> dict:
    codex = render_report_module.ultra_canary.codex_isolated
    return {
        **descriptor,
        "status": "passed",
        "thread_count": 2,
        "observed_descendant_thread_count": 1,
        "positive_usage_descendant_thread_count": 1,
        "response_count": 1,
        "total_model_tokens": 1_000,
        "drain_complete": False,
        "measurement_exact": True,
        "submission_boundary_exact": True,
        "accounting_projection": (
            ultra_canary_projection() if projection is None else projection
        ),
        "barrier": {
            **nested_submission_wire_fixture(
                outer_observed_ns=1_100_000_000,
                inner_started_ns=1_200_000_000,
            ),
            "retained_read_only": True,
            "captured_at_monotonic_ns": 1_300_000_000,
            "raw_response_observed_at_monotonic_ns": 1_400_000_000,
            "request_published_at_monotonic_ns": 1_600_000_000,
            "raw_response_completed_before_boundary_publication": True,
            "submission_event_order": (
                "inner_dynamic_call_before_raw_response_completed"
            ),
            "dynamic_call_observed_before_raw_response_completed": True,
            "raw_response_completed_before_dynamic_call_observed": False,
            "provider_gate_close": {
                "won": True,
                "requested_reason": "accepted_submission",
                "effective_reason": "accepted_submission",
                "phase": "CLOSED",
                "sequence": 4,
            },
        },
        "dependency_audit": {
            "complete": True,
            "helper_sha256": "a" * 64,
            "command_sha256": "b" * 64,
            "library_use": False,
            "library_declarations": [],
            "target_seen": True,
            "semantic_type_equal": True,
        },
        "prompt_release": {
            "schema_version": 1,
            "protocol_version": "highambench-prompt-release-v1",
            "authenticated": True,
            "timing_exact": True,
            "elapsed_clock": "CLOCK_MONOTONIC",
            "startup_timeout_seconds": 120,
            "artifact_count": 3,
            "artifacts_reauthenticated": True,
            "released_at_monotonic_ns": 1_000_000_000,
            "measurement_deadline_monotonic_ns": 301_000_000_000,
            "request_published_at_monotonic_ns": 1_600_000_000,
            "request_publication_timing_verified": True,
        },
    }


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def install_canary_gate_bundle(
    *,
    artifact_root: Path,
    artifacts: dict[str, dict],
    kind: str,
    benchmark_token_limit: int,
) -> tuple[dict, dict, dict]:
    """Install a sealed v2 provider-gate record behind a synthetic canary."""

    token = kind == "token"
    runner = render_report_module.runner
    token_module = render_report_module.token_canary
    ultra_module = render_report_module.ultra_canary
    runner_label = "record" if token else "runner_record"
    runner_path = artifact_root / artifacts[runner_label]["path"]
    usage_path = (artifact_root / artifacts["usage"]["path"]).resolve()
    gate_path = artifact_root / artifacts["provider_gate"]["path"]
    run_id = token_module.CANARY_ID if token else ultra_module.CANARY_ID
    token_limit = (
        token_module.DEFAULT_CANARY_TOKEN_LIMIT if token else benchmark_token_limit
    )
    root_thread_id = f"{kind}-canary-root"
    turn_id = f"{kind}-canary-turn"
    response_id = f"{kind}-canary-response"
    release_record = {
        "schema_version": 1,
        "protocol_version": "highambench-prompt-release-v1",
        "kind": "highambench_prompt_released",
        "run_id": run_id,
        "released_at_monotonic_ns": 1_000_000_000,
        "released_at_unix_ns": 2_000_000_000,
    }
    prompt_sha = digest_bytes(f"{kind}-canary-prompt".encode())
    if token:
        usage: dict = {
            "input_tokens": 240_000,
            "cached_input_tokens": 20_000,
            "cache_write_input_tokens": 2_000,
            "output_tokens": 20_000,
            "reasoning_output_tokens": 5_000,
            "total_tokens": 260_000,
        }
        boundary: dict = {}
    else:
        usage = {
            "input_tokens": 800,
            "cached_input_tokens": 100,
            "cache_write_input_tokens": 20,
            "output_tokens": 200,
            "reasoning_output_tokens": 50,
            "total_tokens": 1_000,
        }
        boundary = {
            "response_id": response_id,
            "raw_response_notification_sequence": 1,
            "request_published_at_monotonic_ns": 1_020_000_000,
            "request_published_at_unix_ns": 2_020_000_000,
        }
    usage.update(
        {
            "model_tokens": usage["total_tokens"],
            "response_count": 1,
            "notification_sequence": 1,
            "response_ids": [response_id],
            "root_thread_id": root_thread_id,
            "interrupt_requested": False,
            "pending_interrupt_response_count": 0,
            "invalid_reasons": [],
            "measurement_exact": True,
            "first_crossing": None,
        }
    )
    gate_record, catalog, transport, source_sha = install_accepted_provider_gate_fixture(
        usage_path=usage_path,
        usage=usage,
        boundary=boundary,
        run_id=run_id,
        token_limit=token_limit,
        root_thread_id=root_thread_id,
        turn_id=turn_id,
        response_id=response_id,
        prompt_release_record=release_record,
        prompt_sha256=prompt_sha,
        request_published_monotonic_ns=1_020_000_000,
        request_published_unix_ns=2_020_000_000,
        raw_response_monotonic_ns=1_019_000_000,
        raw_response_unix_ns=2_019_000_000,
        close_reason="token_limit" if token else "accepted_submission",
    )
    if token:
        gate_record = upgrade_token_gate_to_two_call_compaction_fixture(
            usage_path=usage_path,
            usage=usage,
            record=gate_record,
            token_limit=token_limit,
        )
        usage.update(
            {
                "submission_boundary": None,
                "submission_boundary_exact": False,
                "drain_complete": False,
                "tree_quiescent": False,
                "active_thread_ids": [root_thread_id],
                "unresolved_thread_ids": [],
                "stop_reason": "token_limit",
                "spawn_linkage_complete": True,
                "descendant_accounting_complete": True,
                "cumulative_projection_complete": False,
                "fork_policy_complete": True,
                "accounting_complete": False,
            }
        )
    else:
        usage.update(
            {
                "submission_boundary": boundary,
                "submission_boundary_exact": True,
                "drain_complete": False,
                "tree_quiescent": False,
                "active_thread_ids": [root_thread_id],
                "unresolved_thread_ids": [],
                "stop_reason": "first_valid_proof",
            }
        )
    write_json(usage_path, usage)
    gate_paths = runner.provider_gate_paths(usage_path)
    authentication = runner.authenticate_provider_gate_artifact(
        gate_paths["final"],
        token_limit=token_limit,
        run_id=run_id,
        model="gpt-5.6-sol",
        reasoning_effort="ultra",
        root_thread_id=root_thread_id,
        prompt_release_sha256=digest_bytes(
            json.dumps(
                release_record,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            ).encode("utf-8")
            + b"\n"
        ),
        prompt_release_protocol="highambench-prompt-release-v1",
        prompt_sha256=prompt_sha,
        model_catalog_sha256=str(catalog["catalog_sha256"]),
        model_entry_sha256=str(catalog["entry_sha256"]),
        expected_transport_provenance=transport,
        usage=usage,
        expected_source_sha256=source_sha,
    )
    gate_summary = runner.provider_gate_run_record(
        required=True,
        status="final_artifact_authenticated",
        paths=gate_paths,
        source_sha256=source_sha,
        catalog=catalog,
        transport_provenance=transport,
        live_crossing=(authentication["derived"]["first_crossing"] if token else None),
        final=authentication,
        error=None,
    )
    command = [
        "fixture-adapter",
        "--usage-output",
        str(usage_path),
        "--provider-gate-live-output",
        str(gate_paths["live"]),
        "--provider-gate-output",
        str(gate_paths["final"]),
        "--model-catalog-sha256",
        str(catalog["catalog_sha256"]),
        "--model-entry-sha256",
        str(catalog["entry_sha256"]),
        "--provider-response-bound",
        str(runner.PROVIDER_RESPONSE_TOKEN_BOUND),
    ]
    runner_record = {
        "run_id": run_id,
        "pass": not token,
        "failure_code": "TOKEN_LIMIT" if token else None,
        "agent_exit_code": 0,
        "agent": {"model": "gpt-5.6-sol", "reasoning_effort": "ultra"},
        "limits": {"model_tokens": token_limit},
        "agent_command": command,
        "prompt_release": {
            "effective_prompt_sha256": prompt_sha,
            "released": {"record": release_record},
        },
        "token_usage": usage,
        "token_measurement": {
            "limit_enforcement": {
                "mode": runner.ULTRA_TOKEN_LIMIT_ENFORCEMENT_MODE,
                "notification": runner.ULTRA_USAGE_NOTIFICATION,
                "configured_limit_tokens": token_limit,
                "triggered": token,
                "observed_tokens": (
                    usage["first_crossing"]["tokens"] if token else None
                ),
                "overshoot_tokens": (
                    usage["first_crossing"]["tokens"] - token_limit
                    if token
                    else None
                ),
                "first_crossing_tokens": (
                    usage["first_crossing"]["tokens"] if token else None
                ),
                "first_crossing_overshoot_tokens": (
                    usage["first_crossing"]["tokens"] - token_limit
                    if token
                    else None
                ),
                "final_endpoint_tokens": usage["model_tokens"] if token else None,
                "final_overshoot_tokens": (
                    max(0, usage["model_tokens"] - token_limit) if token else None
                ),
                "checked_before_submission_validation": True,
                "one_response_overshoot_possible": True,
                "concurrent_inflight_overshoot_possible": False,
            }
        },
        "provider_token_gate": gate_summary,
    }
    write_json(runner_path, runner_record)
    for label, path in (
        (runner_label, runner_path),
        ("usage", usage_path),
        ("provider_gate", gate_paths["final"]),
    ):
        artifacts[label] = {
            "path": path.relative_to(artifact_root).as_posix(),
            "sha256": digest_bytes(path.read_bytes()),
        }
    projection = (
        token_canary_projection_fixture(
            record_sha256=str(gate_record["record_sha256"]),
            response_ids=list(usage["response_ids"]),
            provider_usage_reconciliation=dict(
                usage["provider_usage_reconciliation"]
            ),
        )
        if token
        else ultra_canary_projection_fixture(
            record_sha256=str(gate_record["record_sha256"]),
            response_ids=list(usage["response_ids"]),
            provider_usage_reconciliation=dict(
                usage["provider_usage_reconciliation"]
            ),
        )
    )
    return usage, projection, runner_record


class ReportFixture:
    def __init__(self, raw: str) -> None:
        self.repo = Path(raw) / "repo"
        self.root = self.repo / "paper_bencmark" / "highambench"
        self.analysis_path = self.repo / "results" / "analysis" / "summary.json"
        self.freeze_path = self.repo / "results" / "freeze_check.json"
        self.output_tex = self.repo / "report.tex"
        self.construction_path = (
            self.root / "metadata" / "evidence" / "construction_validation.json"
        )
        self.library_pointer_path = (
            self.root / "metadata" / "evidence" / "library_dependency_probe.json"
        )
        self.canary_path = (
            self.root / "metadata" / "evidence" / "token_control_live_canary.json"
        )
        self.ultra_canary_path = (
            self.root
            / "metadata"
            / "evidence"
            / "ultra_orchestration_live_canary.json"
        )
        self._build()

    def _build(self) -> None:
        prompt = b"Use Lean to complete the fixed theorem.\n"
        prompt_path = self.root / "agent_prompt.md"
        prompt_path.parent.mkdir(parents=True, exist_ok=True)
        prompt_path.write_bytes(prompt)
        shared_core = b"""namespace HighamBench
structure StandardAddModel where
  u : Real
def gamma := 0
def GammaValid := True
def recursiveSum := 0
end HighamBench
"""
        shared_p01 = b"""import HighamBench.Core
namespace HighamBench
structure NoGuardAddModel where
  u : Real
def pairwiseSum := 0
def noGuardRecursiveRunningBudget := 0
end HighamBench
"""
        shared_path = self.root / "shared" / "HighamBench"
        shared_path.mkdir(parents=True, exist_ok=True)
        (shared_path / "Core.lean").write_bytes(shared_core)
        (shared_path / "P01Definitions.lean").write_bytes(shared_p01)

        targets: list[dict] = []
        task_ids = ["P01-T1", "P01-T2", "P01-T3"]
        for tier, task_id in zip(("T1", "T2", "T3"), task_ids):
            target_bytes = (
                "import HighamBench.P01Definitions\n"
                f"theorem p01_{tier.lower()}_test : True := by trivial\n"
            ).encode()
            target_path = self.root / "tasks" / "P01" / tier / "Target.lean"
            target_path.parent.mkdir(parents=True, exist_ok=True)
            target_path.write_bytes(target_bytes)
            targets.append(
                {
                    "task_id": task_id,
                    "tier": tier,
                    "tier_name": {"T1": "direct use", "T2": "combine", "T3": "extend"}[tier],
                    "availability": "available",
                    "title": f"Fixture result {tier}",
                    "tier_reason": f"Fixture reason for {tier}.",
                    "source_locations": [
                        {
                            "section": f"Section {tier}",
                            "anchor": f"equation ({tier[-1]}.1)",
                            "journal_page": 780 + int(tier[-1]),
                            "pdf_page": int(tier[-1]),
                            "role": "fixture source anchor",
                        }
                    ],
                    "lean_target": {
                        "declaration": f"p01_{tier.lower()}_test",
                        "file": f"paper_bencmark/highambench/tasks/P01/{tier}/Target.lean",
                        "controlled_file_sha256": digest_bytes(target_bytes),
                        "shared_files": [
                            "paper_bencmark/highambench/shared/HighamBench/Core.lean",
                            (
                                "paper_bencmark/highambench/shared/HighamBench/"
                                "P01Definitions.lean"
                            ),
                        ],
                    },
                }
            )
            write_json(
                self.root / "tasks" / "P01" / tier / "task.json",
                {
                    "task_id": task_id,
                    "paper_id": "P01",
                    "tier": tier,
                    "classification_frozen_before_runs": True,
                    "tier_label": targets[-1]["tier_name"],
                    "tier_rationale": targets[-1]["tier_reason"],
                    "informal_statement": f"The chosen {tier} fixture claim.",
                    "source_locations": targets[-1]["source_locations"],
                    "formal_statement": {
                        "theorem_name": f"p01_{tier.lower()}_test",
                        "lean_header": f"theorem p01_{tier.lower()}_test : True",
                        "plain_language": f"The {tier} fixture statement is true.",
                    },
                },
            )

        paper_hash = "a" * 64
        spec_hash = "b" * 64
        paper = {
            "paper_id": "P01",
            "classification_frozen_before_runs": True,
            "title": "The Accuracy of Floating Point Summation",
            "authors": ["Nicholas J. Higham"],
            "source": {
                "local_path": "paper_bencmark/reference_papers/paper.pdf",
                "sha256": paper_hash,
            },
            "benchmark_specification": {
                "local_path": "paper_bencmark/scratch_pad/spec.pdf",
                "sha256": spec_hash,
            },
        }
        write_json(self.root / "tasks" / "P01" / "paper.json", paper)

        benchmark_id = "fixture-p01"
        manifest = {
            "benchmark_id": benchmark_id,
            "specification": {
                "local_path": "paper_bencmark/scratch_pad/spec.pdf",
                "sha256": spec_hash,
            },
            "controlled_shared_files": [
                {
                    "path": "paper_bencmark/highambench/shared/HighamBench/Core.lean",
                    "paper_ids": ["P01"],
                    "sha256": digest_bytes(shared_core),
                },
                {
                    "path": (
                        "paper_bencmark/highambench/shared/HighamBench/"
                        "P01Definitions.lean"
                    ),
                    "paper_ids": ["P01"],
                    "sha256": digest_bytes(shared_p01),
                },
            ],
            "papers": [
                {
                    "paper_id": "P01",
                    "citation": {
                        "author": "Nicholas J. Higham",
                        "title": "The Accuracy of Floating Point Summation",
                    },
                    "source": {
                        "local_path": "paper_bencmark/reference_papers/paper.pdf",
                        "sha256": paper_hash,
                        "rights_note": "Fixture source; do not redistribute.",
                    },
                    "targets": targets,
                }
            ],
        }
        tool_hashes: dict[str, str] = {}
        for index, relative in enumerate(CONSTRUCTION_TOOL_PATHS, start=1):
            tool_path = self.root / relative
            tool_path.parent.mkdir(parents=True, exist_ok=True)
            tool_path.write_bytes(f"fixture checker {index}: {relative}\n".encode())
            tool_hashes[relative] = digest_bytes(tool_path.read_bytes())

        source_manifest = {
            "schema_version": 1,
            "kind": "highambench-controlled-files",
            "label": "NumStability source",
            "files": [
                {"path": "NumStability.lean", "sha256": "1" * 64, "bytes": 101},
                {
                    "path": "NumStability/Fixture.lean",
                    "sha256": "2" * 64,
                    "bytes": 202,
                },
            ],
        }
        compiled_manifest = {
            "schema_version": 1,
            "kind": "highambench-controlled-files",
            "label": "compiled NumStability",
            "files": [
                {
                    "path": "NumStability/Fixture.olean",
                    "sha256": "3" * 64,
                    "bytes": 303,
                }
            ],
        }
        packages_runtime_manifest = {
            "schema_version": 1,
            "kind": "highambench-controlled-files",
            "label": "pruned package runtime",
            "files": [
                {"path": "mathlib/Mathlib.lean", "sha256": "a" * 64, "bytes": 10},
                {
                    "path": "mathlib/Mathlib/Fixture.lean",
                    "sha256": "b" * 64,
                    "bytes": 20,
                },
                {
                    "path": "mathlib/.lake/build/lib/lean/Mathlib/Fixture.olean",
                    "sha256": "c" * 64,
                    "bytes": 30,
                },
                {
                    "path": "mathlib/.lake/build/lib/lean/Mathlib/Fixture.olean.server",
                    "sha256": "d" * 64,
                    "bytes": 40,
                },
                {
                    "path": "mathlib/.lake/build/lib/lean/Mathlib/Fixture.olean.private",
                    "sha256": "e" * 64,
                    "bytes": 50,
                },
                {
                    "path": "mathlib/.lake/build/lib/lean/Mathlib/Fixture.ir",
                    "sha256": "f" * 64,
                    "bytes": 60,
                },
            ],
        }
        compiled_summary = {
            "schema_version": 1,
            "kind": "highambench-compiled-environment-summary",
            "toolchain": {
                "relative_root": ".",
                "file_count": 7,
                "total_bytes": 700,
                "tree_sha256": "4" * 64,
            },
            "packages": [
                {
                    "package": "mathlib",
                    "relative_root": "mathlib/.lake/build/lib/lean",
                    "git_commit": "5" * 40,
                    "file_count": 11,
                    "total_bytes": 1100,
                    "tree_sha256": "6" * 64,
                }
            ],
        }
        source_manifest_path = self.root / "metadata" / "library_source.json"
        compiled_manifest_path = self.root / "metadata" / "library_olean.json"
        compiled_summary_path = self.root / "metadata" / "packages_olean.json"
        packages_runtime_path = self.root / "metadata" / "packages_runtime.json"
        write_json(source_manifest_path, source_manifest)
        write_json(compiled_manifest_path, compiled_manifest)
        write_json(compiled_summary_path, compiled_summary)
        write_json(packages_runtime_path, packages_runtime_manifest)
        source_manifest_sha = digest_bytes(source_manifest_path.read_bytes())
        compiled_manifest_sha = digest_bytes(compiled_manifest_path.read_bytes())
        compiled_summary_sha = digest_bytes(compiled_summary_path.read_bytes())
        packages_runtime_sha = digest_bytes(packages_runtime_path.read_bytes())

        benchmark_token_limit = 300_000
        canary_artifact_root = self.repo / "canary-artifacts"
        canary_artifact_paths = {
            label: f"artifacts/{label}"
            for label in render_report_module.token_canary.ARTIFACT_LABELS
        }
        canary_artifacts: dict[str, dict] = {}
        for index, (label, relative) in enumerate(
            canary_artifact_paths.items(), start=1
        ):
            path = canary_artifact_root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            if label == "freeze_check":
                write_json(
                    path,
                    {
                        "prompt_protocol": PRODUCTION_PROMPT_PROTOCOL,
                        "execution_components": PRODUCTION_EXECUTION_COMPONENTS,
                    },
                )
                self.token_production_freeze_path = path
            else:
                path.write_bytes(f"fixture canary {index}: {label}\n".encode())
            canary_artifacts[label] = {
                "path": relative,
                "sha256": digest_bytes(path.read_bytes()),
            }
        token_usage, token_projection, _ = install_canary_gate_bundle(
            artifact_root=canary_artifact_root,
            artifacts=canary_artifacts,
            kind="token",
            benchmark_token_limit=benchmark_token_limit,
        )
        canary_evidence = {
            "schema_version": render_report_module.token_canary.EVIDENCE_SCHEMA_VERSION,
            "kind": render_report_module.token_canary.EVIDENCE_KIND,
            "status": "passed",
            "public_release": False,
            "scored": False,
            "matrix_assignment": False,
            "synthetic_input": True,
            "benchmark_task_bytes_used": False,
            "benchmark_id": benchmark_id,
            "canary_id": render_report_module.token_canary.CANARY_ID,
            "pre_canary_environment_id": "fixture-pre-canary-environment",
            "freeze_check_sha256": "1" * 64,
            "agent": {
                "id": "fixture-agent",
                "version": "1.2.3",
                "binary_sha256": "a" * 64,
                "model": "fixture-model",
                "reasoning_effort": "medium",
            },
            "artifact_root": "canary-artifacts",
            "artifacts": canary_artifacts,
            "assignment": {
                "task_id": render_report_module.token_canary.CANARY_ID,
                "paper_id": "SYNTHETIC",
                "condition": "N",
                "repetition_id": "canary",
                "matrix_assignment": False,
            },
            "prompt": render_report_module.token_canary.prompt_record(),
            "source_separation": {"audit_sha256": "c" * 64},
            "controls": {
                "frozen_benchmark_token_limit": benchmark_token_limit,
                "outer_canary_token_limit": (
                    render_report_module.token_canary.DEFAULT_CANARY_TOKEN_LIMIT
                ),
                "nested_advisory_rollout_budget_limit": benchmark_token_limit,
                "canary_wall_time_seconds": 300,
                "notification": "rawResponse/completed",
                "cached_input_counted_once": True,
                "trusted_adapter_freezes_first_threshold": False,
                "trusted_adapter_latches_first_threshold": True,
                "all_descendant_threads_included": True,
                "response_ids_deduplicated": True,
                "drain_complete_required": False,
                "provider_token_quiescence_required": True,
                "tree_quiescence_distinct_from_provider_quiescence": True,
                "measurement_exact_required": True,
                "root_completion_is_tree_barrier": False,
                "trusted_usage_path_outside_workspace": True,
                "authenticated_prompt_release_required": True,
                "prompt_release_protocol_version": "highambench-prompt-release-v1",
                "prompt_startup_timeout_seconds": 120.0,
                "prompt_ready_go_released_files_required": 3,
                "prompt_artifact_canonical_json_required": True,
                "prompt_artifact_sealed_mode": "0444",
                "measurement_time_origin": "RELEASED.released_at_monotonic_ns",
                "release_based_deadline_required": True,
                "submission_boundary_expected": False,
            },
            "outcome": {
                "actual_stop_seconds": 5.758539,
                "input_tokens_including_cached": token_usage["input_tokens"],
                "cached_input_tokens": token_usage["cached_input_tokens"],
                "output_tokens": token_usage["output_tokens"],
                "total_model_tokens": token_usage["model_tokens"],
                "first_crossing_tokens": token_usage["first_crossing"]["tokens"],
                "overshoot_tokens": (
                    token_usage["first_crossing"]["tokens"]
                    - render_report_module.token_canary.DEFAULT_CANARY_TOKEN_LIMIT
                ),
                "final_overshoot_tokens": (
                    token_usage["model_tokens"]
                    - render_report_module.token_canary.DEFAULT_CANARY_TOKEN_LIMIT
                ),
                "thread_count": 1,
                "observed_child_thread_count": 0,
                "response_count": 2,
                "notification_sequence": 2,
                "notification_count_in_audit_log": 2,
                "drain_complete": False,
                "measurement_exact": True,
                "accounting_projection": token_projection,
                "prompt_release": token_canary_prompt_release(),
            },
            "startup_preflight_history": [],
        }
        write_json(self.canary_path, canary_evidence)
        canary_sha = digest_bytes(self.canary_path.read_bytes())
        canary_descriptor = {
            "path": (
                "paper_bencmark/highambench/metadata/evidence/"
                "token_control_live_canary.json"
            ),
            "sha256": canary_sha,
            "status": "passed",
        }
        ultra_artifact_root = self.repo / "ultra-canary-artifacts"
        ultra_artifacts: dict[str, dict] = {}
        for index, label in enumerate(
            render_report_module.ultra_canary.ARTIFACT_LABELS, start=1
        ):
            relative = f"artifacts/{label}"
            path = ultra_artifact_root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            if label == "freeze_check":
                write_json(
                    path,
                    {
                        "prompt_protocol": PRODUCTION_PROMPT_PROTOCOL,
                        "execution_components": PRODUCTION_EXECUTION_COMPONENTS,
                    },
                )
            else:
                path.write_bytes(f"fixture Ultra canary {index}: {label}\n".encode())
            ultra_artifacts[label] = {
                "path": relative,
                "sha256": digest_bytes(path.read_bytes()),
            }
        ultra_usage, ultra_projection, _ = install_canary_gate_bundle(
            artifact_root=ultra_artifact_root,
            artifacts=ultra_artifacts,
            kind="ultra",
            benchmark_token_limit=benchmark_token_limit,
        )
        write_json(
            self.ultra_canary_path,
            {
                "schema_version": 1,
                "kind": render_report_module.ultra_canary.EVIDENCE_KIND,
                "status": "passed",
                "public_release": False,
                "scored": False,
                "matrix_assignment": False,
                "synthetic_input": True,
                "canary_id": render_report_module.ultra_canary.CANARY_ID,
                "benchmark_id": benchmark_id,
                "agent": {
                    "id": "fixture-agent",
                    "version": "1.2.3",
                    "binary_sha256": "a" * 64,
                    "model": "fixture-model",
                    "reasoning_effort": "medium",
                },
                "prompt": render_report_module.ultra_canary.prompt_record(),
                "controls": {"outer_token_limit": benchmark_token_limit},
                "outcome": {
                    "measurement_exact": True,
                    "submission_boundary_exact": True,
                    "drain_complete": False,
                    "accounting_projection": ultra_projection,
                    "model_tokens": ultra_usage["model_tokens"],
                },
                "artifact_root": "ultra-canary-artifacts",
                "artifacts": ultra_artifacts,
            },
        )
        ultra_canary_descriptor = {
            "path": render_report_module.ultra_canary.FROZEN_EVIDENCE_PATH,
            "sha256": digest_bytes(self.ultra_canary_path.read_bytes()),
            "status": "passed",
        }

        def release_entry(relative: str) -> dict:
            path = self.root / relative
            value = path.read_bytes()
            return {"path": relative, "sha256": digest_bytes(value), "bytes": len(value)}

        release_paths = list(CONSTRUCTION_TOOL_PATHS) + [
            "metadata/library_source.json",
            "metadata/library_olean.json",
            "metadata/packages_olean.json",
            "metadata/packages_runtime.json",
            "metadata/evidence/token_control_live_canary.json",
            "metadata/evidence/ultra_orchestration_live_canary.json",
        ]
        release_manifest = {
            "schema_version": 1,
            "kind": "highambench-controlled-files",
            "label": "evaluation release",
            "files": [release_entry(relative) for relative in release_paths],
        }
        release_path = self.root / "metadata" / "release_files.json"
        write_json(release_path, release_manifest)
        release_sha = digest_bytes(release_path.read_bytes())

        bundle_sha = "e" * 64
        environment_id = "highambench-p01-" + bundle_sha[:16]
        shared_core_olean_sha = "7" * 64
        shared_p01_olean_sha = "6" * 64
        lean_binary_sha = "8" * 64
        bubblewrap_sha = "9" * 64
        python_binary_sha = "f" * 64
        python_version = "3.fixture"
        token_control = {
            "advisory_rollout_budget": {
                "enabled": True,
                "feature": "rollout_budget",
                "feature_row": "rollout_budget under development false",
                "limit_tokens": benchmark_token_limit,
                "prefill_token_weight": 1,
                "role": "advisory_only",
                "sampling_token_weight": 1,
                "strict_config": True,
            },
            "cached_input_counted_once": True,
            "checked_before_submission_validation": True,
            "comparison": ">=",
            "control": "loopback_provider_response_admission_gate",
            "input_includes_cached": True,
            "limit_tokens": benchmark_token_limit,
            "live_update_sequence": True,
            "live_cumulative": True,
            "measurement_source": "codex_app_server_rawResponse/completed",
            "notification": "rawResponse/completed",
            "usage_scope": "rooted_attempt_thread_tree_completed_responses",
            "one_response_overshoot_possible": True,
            "concurrent_inflight_overshoot_possible": False,
            "all_descendant_threads_included": True,
            "response_ids_deduplicated": True,
            "outcome_exactness": render_report_module.ULTRA_OUTCOME_EXACTNESS,
            "measurement_exact_required": True,
            "root_completion_is_tree_barrier": False,
            "outer_runner_polling": True,
            "over_limit_pass_allowed": False,
            "trusted_adapter_freezes_first_threshold": True,
            "trusted_adapter_latches_first_threshold": True,
            "trusted_usage_path_outside_workspace": True,
            "provider_gate_protocol": render_report_module.runner.PROVIDER_GATE_PROTOCOL,
            "provider_response_bound_tokens": (
                render_report_module.runner.PROVIDER_RESPONSE_TOKEN_BOUND
            ),
            "strict_admission_inequality": (
                "completed_tokens + (open_request_count + 1) * "
                "response_bound < token_limit"
            ),
            "crossing_response_release": (
                render_report_module.runner.PROVIDER_GATE_CROSSING_RELEASE_POLICY
            ),
            "crossing_response_actions_released": False,
            "provider_requests_quiescent_at_scored_endpoint": True,
            "tree_quiescence_distinct_from_provider_quiescence": True,
        }
        config = {
            "benchmark_id": benchmark_id,
            "frozen_environment": {
                "environment_id": environment_id,
                "environment_bundle_sha256": bundle_sha,
                "prompt_sha256": digest_bytes(prompt),
                "agent_id": "fixture-agent",
                "agent_version": "1.2.3",
                "agent_binary_sha256": "a" * 64,
                "model_version": "fixture-model",
                "model_reasoning_effort": "medium",
                "python_version": python_version,
                "python_binary_sha256": python_binary_sha,
                "numstability_source_manifest": (
                    "paper_bencmark/highambench/metadata/library_source.json"
                ),
                "numstability_source_manifest_sha256": source_manifest_sha,
                "numstability_compiled_manifest": (
                    "paper_bencmark/highambench/metadata/library_olean.json"
                ),
                "numstability_compiled_manifest_sha256": compiled_manifest_sha,
                "compiled_environment_summary": (
                    "paper_bencmark/highambench/metadata/packages_olean.json"
                ),
                "compiled_environment_summary_sha256": compiled_summary_sha,
                "packages_runtime_manifest": (
                    "paper_bencmark/highambench/metadata/packages_runtime.json"
                ),
                "packages_runtime_manifest_sha256": packages_runtime_sha,
                "release_manifest": (
                    "paper_bencmark/highambench/metadata/release_files.json"
                ),
                "release_manifest_sha256": release_sha,
                "bubblewrap_binary_sha256": bubblewrap_sha,
                "token_control_canary": canary_descriptor,
                "ultra_orchestration_canary": ultra_canary_descriptor,
            },
            "planned_counts_per_agent": {
                "papers": 1,
                "tasks": 3,
                "repetitions_per_task": 3,
                "conditions": 2,
                "paired_assignments": 9,
                "runs": 18,
            },
            "repetitions": [
                {"id": "rep-01", "backend_seed": None},
                {"id": "rep-02", "backend_seed": None},
                {"id": "rep-03", "backend_seed": None},
            ],
            "limits": {
                "wall_clock_seconds": 900,
                "total_model_tokens": benchmark_token_limit,
            },
            "token_control": token_control,
        }
        run_order = {"benchmark_id": benchmark_id, "pairs": []}
        environment = {
            "environment_id": environment_id,
            "environment_bundle_sha256": bundle_sha,
            "release_manifest": "paper_bencmark/highambench/metadata/release_files.json",
            "release_manifest_sha256": release_sha,
            "runtime": {
                "python": {
                    "version": python_version,
                    "binary_sha256": python_binary_sha,
                },
                "packages_runtime_manifest": (
                    "paper_bencmark/highambench/metadata/packages_runtime.json"
                ),
                "packages_runtime_manifest_sha256": packages_runtime_sha,
            },
            "host_class": {
                "kernel": "Fixture Linux",
                "virtualization": "FIXTURE",
                "cpu_vendor": "Fixture Vendor",
                "processor": "Fixture CPU",
                "cpu_family": 1,
                "cpu_model": 2,
                "cpu_stepping": 3,
                "online_logical_cpus": 4,
                "allocated_physical_cores": 2,
                "allocated_sockets": 1,
                "allocated_threads_per_core": [2, 2],
                "visible_memory_bytes": 16000000000,
                "allocation_memory_limit_bytes": 8000000000,
                "slurm_num_nodes": 1,
                "slurm_num_cpus": 4,
                "slurm_num_tasks": 1,
                "slurm_cpus_per_task": 4,
                "slurm_allocated_memory_bytes": 8000000000,
            },
            "lean": {
                "version": "4.fixture",
                "commit": "b" * 40,
                "binary_sha256": lean_binary_sha,
                "mathlib_commit": "c" * 40,
                "numstability_commit": "d" * 40,
                "shared_sources": {
                    "HighamBench/Core.lean": digest_bytes(shared_core),
                    "HighamBench/P01Definitions.lean": digest_bytes(shared_p01),
                },
                "shared_olean_bundles": {
                    "P01": {
                        "HighamBench/Core.olean": shared_core_olean_sha,
                        "HighamBench/P01Definitions.olean": shared_p01_olean_sha,
                    }
                },
                "numstability_source_manifest": (
                    "paper_bencmark/highambench/metadata/library_source.json"
                ),
                "numstability_source_manifest_sha256": source_manifest_sha,
                "numstability_compiled_manifest": (
                    "paper_bencmark/highambench/metadata/library_olean.json"
                ),
                "numstability_compiled_manifest_sha256": compiled_manifest_sha,
                "compiled_environment_summary": (
                    "paper_bencmark/highambench/metadata/packages_olean.json"
                ),
                "compiled_environment_summary_sha256": compiled_summary_sha,
            },
            "isolation": {
                "kind": "bubblewrap namespace; not an OCI container",
                "network_boundary": "model shell offline; provider control connection retained",
                "lean_adapter_sha256": tool_hashes["tools/lean_isolated.py"],
                "validator_sha256": tool_hashes["tools/validator.py"],
                "dependency_audit_sha256": tool_hashes["tools/dependency_audit.lean"],
                "bubblewrap_binary_sha256": bubblewrap_sha,
                "bubblewrap_version": "bubblewrap 0.fixture",
            },
            "known_reference_protocol_deviations": [
                "No backend seed is available; repetition IDs are not seeds.",
                "There is no frozen OCI image.",
                "The provider connection remains available to the control process.",
                "Provider-token closure can precede app-server-tree terminality.",
            ],
            "token_control": token_control,
            "token_control_canary": canary_descriptor,
            "ultra_orchestration_canary": ultra_canary_descriptor,
        }
        write_json(self.root / "metadata" / "manifest.json", manifest)
        write_json(self.root / "metadata" / "config.json", config)
        write_json(self.root / "metadata" / "run_order.json", run_order)
        write_json(self.root / "metadata" / "environment.json", environment)

        write_json(
            self.root / "metadata" / "evidence" / "exact_target_search.json",
            {
                "fixed_surface_hashes": {
                    "shared_files": [
                        {
                            "path": "paper_bencmark/highambench/shared/HighamBench/Core.lean",
                            "sha256": digest_bytes(shared_core),
                        },
                        {
                            "path": (
                                "paper_bencmark/highambench/shared/HighamBench/"
                                "P01Definitions.lean"
                            ),
                            "sha256": digest_bytes(shared_p01),
                        },
                    ],
                    **{
                        target["task_id"]: {
                            "sha256": target["lean_target"]["controlled_file_sha256"]
                        }
                        for target in targets
                    },
                },
                "overall_conclusion": {
                    "all_three_exact_targets_absent": True,
                    "all_three_semantic_duplicates_absent": True,
                    "tier_labels_supported_by_library_surface": True,
                },
                "task_findings": [
                    {
                        "task_id": task_id,
                        "exact_duplicate_found": False,
                        "semantic_duplicate_found": False,
                        "tier_assessment": f"{tier} is supported by the fixture search.",
                    }
                    for task_id, tier in zip(task_ids, ("T1", "T2", "T3"))
                ],
            },
        )
        construction = {
            "kind": "highambench-private-construction-check",
            "pass": True,
            "summary": {
                "expected": 6,
                "checked": 6,
                "passed": 6,
                "condition_n_passed": 3,
                "condition_l_passed": 3,
            },
            "isolation": {
                "condition_n_preflight_after_complete_controlled_staging": True,
                "condition_n_numstability_mounts_configured": False,
                "condition_l_numstability_mounts_configured": True,
            },
            "verification_basis": {
                "tools": tool_hashes,
                "executables": {
                    "python": {
                        "path": "/usr/bin/python3",
                        "sha256": python_binary_sha,
                        "version": python_version,
                    },
                    "bubblewrap": {"path": "/bin/bwrap", "sha256": bubblewrap_sha},
                },
                "shared_olean": {
                    "bundles": {
                        "P01": {
                            "HighamBench/Core.olean": shared_core_olean_sha,
                            "HighamBench/P01Definitions.olean": shared_p01_olean_sha,
                        }
                    },
                    "exact_file_count": 2,
                },
                "numstability_source": {
                    "path": "metadata/library_source.json",
                    "sha256": source_manifest_sha,
                    "label": "NumStability source",
                    "file_count": len(source_manifest["files"]),
                    "total_bytes": sum(item["bytes"] for item in source_manifest["files"]),
                    "verified": len(source_manifest["files"]),
                    "exact_tree": True,
                },
                "numstability_compiled": {
                    "path": "metadata/library_olean.json",
                    "sha256": compiled_manifest_sha,
                    "label": "compiled NumStability",
                    "file_count": len(compiled_manifest["files"]),
                    "total_bytes": sum(item["bytes"] for item in compiled_manifest["files"]),
                    "verified": len(compiled_manifest["files"]),
                    "exact_tree": True,
                    "mount_root": str((self.repo / PRUNED_LIBRARY_OLEAN_ROOT).resolve()),
                    "only_numstability_namespace": True,
                },
                "packages_runtime": {
                    "path": "metadata/packages_runtime.json",
                    "sha256": packages_runtime_sha,
                    "label": "pruned package runtime",
                    "file_count": len(packages_runtime_manifest["files"]),
                    "total_bytes": sum(
                        item["bytes"] for item in packages_runtime_manifest["files"]
                    ),
                    "verified": len(packages_runtime_manifest["files"]),
                    "exact_tree": True,
                    "mount_root": str((self.repo / PACKAGES_RUNTIME_ROOT).resolve()),
                    "only_mathlib_source_and_lean_compiled_artifacts": True,
                    "mathlib_source_file_count": 2,
                    "base_olean_file_count": 1,
                    "compiled_support_file_count": 3,
                },
            },
            "results": [
                {
                    "task_id": task_id,
                    "tier": tier,
                    "condition": condition,
                    "manifest_sha256": ("0" if tier == "T1" else "1" if tier == "T2" else "2") * 64,
                    "condition_n_library_arguments_omitted": condition == "N",
                    "pass": True,
                    "n_preflight": (
                        {
                            "ok": True,
                            "complete": True,
                            "filesystem_leaks": [],
                            "controlled_manifest_sha256": (
                                ("0" if tier == "T1" else "1" if tier == "T2" else "2")
                                * 64
                            ),
                            "controlled_files_verified_after_staging": {
                                "ok": True,
                                "verified": 5,
                                "expected": 5,
                                "missing": [],
                                "changed": [],
                            },
                            "filesystem_scan": {
                                "root": ".",
                                "markers": ["NumStability", "numStability"],
                                "regular_file_count": 5,
                                "directory_count": 3,
                                "symlink_count": 0,
                            },
                            "import_probe": {
                                "attempted": True,
                                "reliable": True,
                                "importable": False,
                            },
                        }
                        if condition == "N"
                        else None
                    ),
                    "validation": {
                        "pass": True,
                        "compile_exit_code": 0,
                        "compile_timed_out": False,
                        "controlled_before_ok": True,
                        "controlled_hidden_ok": True,
                        "failure_code": None,
                        "statement_unchanged": True,
                        "static_finding_count": 0,
                        "dependency_audit": {
                            "complete": True,
                            "exit_code": 0,
                            "format_version": 2,
                            "forbidden_dependency_count": 0,
                            "library_declarations": (
                                [
                                    {
                                        "distance": 1,
                                        "module": "NumStability.Fixture",
                                        "name": f"NumStability.fixture{tier}",
                                    }
                                ]
                                if condition == "L"
                                else []
                            ),
                            "library_use": condition == "L",
                            "local_modules": ["Submission"],
                            "missing_helper_modules": [],
                        },
                    },
                }
                for task_id, tier in zip(task_ids, ("T1", "T2", "T3"))
                for condition in ("N", "L")
            ],
        }
        write_json(self.construction_path, construction)
        write_json(
            self.library_pointer_path,
            {
                "schema_version": "0.1.0",
                "kind": "highambench-library-dependency-evidence-pointer",
                "status": "superseded by the complete six-proof construction check",
                "current_evidence": (
                    "paper_bencmark/highambench/metadata/evidence/"
                    "construction_validation.json"
                ),
                "current_evidence_sha256": digest_bytes(
                    self.construction_path.read_bytes()
                ),
                "current_result": {
                    "proofs_checked": 6,
                    "proofs_passed": 6,
                    "condition_l_passed_proofs_using_numstability": 3,
                },
            },
        )
        for number, focus in ((1, "paper meaning and source"), (2, "formal interface and protocol")):
            write_json(
                self.root / "metadata" / "reviews" / f"reviewer_{number}.json",
                {
                    "review_id": f"fixture-review-{number}",
                    "reviewer": {"focus": focus, "kind": "Codex review, not human"},
                    "overall_status": "final pass",
                    "task_reviews": [
                        {"task_id": task_id, "review_outcome": "pass"} for task_id in task_ids
                    ],
                },
            )

        release_count = len(release_manifest["files"])
        freeze_check = {
            "schema_version": 1,
            "kind": "highambench-frozen-run-verification",
            "ok": True,
            "benchmark_id": benchmark_id,
            "environment_id": environment_id,
            "environment_bundle_sha256": bundle_sha,
            "agent": {
                "id": "fixture-agent",
                "version": "1.2.3",
                "binary_sha256": "a" * 64,
                "model": "fixture-model",
                "reasoning_effort": "medium",
            },
            "python": {
                "version": python_version,
                "binary_sha256": python_binary_sha,
            },
            "token_control": {
                **token_control,
                "advisory_rollout_budget": {
                    **token_control["advisory_rollout_budget"],
                    "feature_row": "rollout_budget under development false",
                },
            },
            "token_control_canary": {
                **canary_descriptor,
                "canary_limit_tokens": (
                    render_report_module.token_canary.DEFAULT_CANARY_TOKEN_LIMIT
                ),
                "first_crossing_tokens": token_usage["first_crossing"]["tokens"],
                "final_endpoint_tokens": token_usage["model_tokens"],
                "thread_count": 1,
                "observed_child_thread_count": 0,
                "response_count": 2,
                "drain_complete": False,
                "provider_gate_quiescent": True,
                "measurement_exact": True,
                "synthetic_input": True,
                "matrix_assignment": False,
                "benchmark_task_bytes_used": False,
                "prompt_protocol": render_report_module.token_canary.PROMPT_PROTOCOL,
                "source_separation_audit_sha256": "c" * 64,
                "prompt_release": token_canary_prompt_release(),
                "accounting_projection": token_projection,
                "artifacts": {
                    label: {
                        **descriptor,
                        "bytes": (canary_artifact_root / descriptor["path"]).stat().st_size,
                    }
                    for label, descriptor in canary_artifacts.items()
                },
            },
            "ultra_orchestration_canary": ultra_canary_summary(
                ultra_canary_descriptor, ultra_projection
            ),
            "lean": {
                "version": "4.fixture",
                "commit": "b" * 40,
                "binary_sha256": lean_binary_sha,
                "mathlib_commit": "c" * 40,
                "numstability_commit": "d" * 40,
                "source_files_verified": len(source_manifest["files"]),
                "compiled_files_verified": len(compiled_manifest["files"]),
            },
            "host_class": {
                field: environment["host_class"][field]
                for field in (
                    "kernel",
                    "virtualization",
                    "cpu_vendor",
                    "processor",
                    "cpu_family",
                    "cpu_model",
                    "cpu_stepping",
                    "online_logical_cpus",
                    "allocated_physical_cores",
                    "allocated_sockets",
                    "allocated_threads_per_core",
                    "visible_memory_bytes",
                    "allocation_memory_limit_bytes",
                    "slurm_num_nodes",
                    "slurm_num_cpus",
                    "slurm_num_tasks",
                    "slurm_cpus_per_task",
                    "slurm_allocated_memory_bytes",
                )
            },
            "limits": {
                "wall_clock_seconds": 900,
                "total_model_tokens": benchmark_token_limit,
            },
            "release_manifest": {
                "path": "metadata/release_files.json",
                "sha256": release_sha,
                "file_count": release_count,
                "verification": {
                    "ok": True,
                    "verified": release_count,
                    "expected": release_count,
                    "missing": [],
                    "changed": [],
                },
            },
            "packages_runtime": {
                "path": "paper_bencmark/highambench/metadata/packages_runtime.json",
                "sha256": packages_runtime_sha,
                "file_count": len(packages_runtime_manifest["files"]),
                "source_file_count": 2,
                "olean_file_count": 1,
                "compiled_support_file_count": 3,
                "verification": {
                    "ok": True,
                    "verified": len(packages_runtime_manifest["files"]),
                    "expected": len(packages_runtime_manifest["files"]),
                    "missing": [],
                    "changed": [],
                },
            },
            "compiled_environment_summary": {
                "path": "paper_bencmark/highambench/metadata/packages_olean.json",
                "sha256": compiled_summary_sha,
                "toolchain_file_count": 7,
                "package_count": 1,
                "package_file_count": 11,
            },
            "bubblewrap": {
                "version": "bubblewrap 0.fixture",
                "binary_sha256": bubblewrap_sha,
            },
            "metadata_document_sha256": {
                "config": document_digest(config),
                "environment": document_digest(environment),
                "manifest": document_digest(manifest),
                "run_order": document_digest(run_order),
            },
        }
        write_json(self.freeze_path, freeze_check)
        freeze_sha = document_digest(freeze_check)

        failure_counts = {code: 0 for code in (
            "TIME_LIMIT",
            "TOKEN_LIMIT",
            "NO_SUBMISSION",
            "RULE_VIOLATION",
            "SYNTAX_OR_ELAB",
            "PROOF_ERROR",
            "SYSTEM_ERROR",
        )}
        failure_counts["PROOF_ERROR"] = 3

        def condition_row(scope: str, condition: str, task_id: str | None = None, tier: str | None = None) -> dict:
            row = {
                "result_status": "observational_not_reference_score",
                "agent_id": "fixture-agent",
                "agent_version": "1.2.3",
                "model": "fixture-model",
                "scope": scope,
                "condition": condition,
                "official_scored_runs": 0,
                "observational_runs": 9 if scope == "overall" else 3,
                "observed_passes": (9 if scope == "overall" else 3) if condition == "L" else 0,
                "observed_pass_rate": 1.0 if condition == "L" else 0.0,
                "median_observed_seconds": 12.5 if condition == "L" else 900.0,
                "median_observed_model_tokens": 1000.0 if condition == "L" else 2000.0,
                "runs_with_token_measurement": 9 if scope == "overall" else 3,
                "observed_passed_library_use": 9 if scope == "overall" and condition == "L" else 3 if condition == "L" else 0,
                "failure_counts": {code: (failure_counts[code] if condition == "N" else 0) for code in failure_counts},
            }
            if task_id is not None:
                row.update({"paper_id": "P01", "task_id": task_id, "tier": tier})
            return row

        condition_rows = [
            condition_row(scope, condition)
            for scope in ("overall", "T1", "T2", "T3")
            for condition in ("N", "L")
        ]
        task_rows = [
            condition_row(task_id, condition, task_id, tier)
            for task_id, tier in zip(task_ids, ("T1", "T2", "T3"))
            for condition in ("N", "L")
        ]

        def pair_row(scope: str, task_id: str | None = None, tier: str | None = None) -> dict:
            row = {
                "result_status": "observational_not_reference_score",
                "agent_id": "fixture-agent",
                "agent_version": "1.2.3",
                "model": "fixture-model",
                "scope": scope,
                "condition": "L-N",
                "pairs": 9 if scope == "overall" else 3,
                "observed_pass_rate_change": 1.0,
                "median_observed_paired_time_change": -887.5,
                "median_observed_paired_token_change": -1000.0,
                "pairs_with_token_measurement": 9 if scope == "overall" else 3,
                "bootstrap": {
                    "method": "percentile bootstrap resampling whole papers",
                    "confidence": 0.95,
                    "paper_count": 1,
                    "informative": False,
                    "note": "one-paper resampling is degenerate and does not estimate corpus uncertainty",
                    "ranges": {
                        "pass_rate_change": {"low": 1.0, "high": 1.0},
                        "median_paired_time_change": {"low": -887.5, "high": -887.5},
                        "median_paired_token_change": {"low": -1000.0, "high": -1000.0},
                    },
                },
            }
            if task_id is not None:
                row.update({"paper_id": "P01", "task_id": task_id, "tier": tier})
            return row

        pair_rows = [pair_row(scope) for scope in ("overall", "T1", "T2", "T3")]
        task_pair_rows = [
            pair_row(task_id, task_id, tier)
            for task_id, tier in zip(task_ids, ("T1", "T2", "T3"))
        ]

        runs: list[dict] = []
        selected_ids: list[str] = []
        for task_id, tier in zip(task_ids, ("T1", "T2", "T3")):
            for repetition in ("rep-01", "rep-02", "rep-03"):
                for condition in ("N", "L"):
                    run_id = f"{task_id}-{repetition}-{condition}"
                    selected_ids.append(run_id)
                    passed = condition == "L"
                    runs.append(
                        {
                            "agent_id": "fixture-agent",
                            "agent_version": "1.2.3",
                            "model": "fixture-model",
                            "run_id": run_id,
                            "pair_id": f"{task_id}-{repetition}",
                            "paper_id": "P01",
                            "task_id": task_id,
                            "tier": tier,
                            "repetition_id": repetition,
                            "backend_seed": None,
                            "condition": condition,
                            "pair_order": "N-first",
                            "order_index": 1 if condition == "N" else 2,
                            "scored": False,
                            "pass": passed,
                            "actual_stop_seconds": 12.5 if passed else 100.0,
                            "scored_elapsed_seconds": 12.5 if passed else 900.0,
                            "model_tokens": 1000 if passed else 2000,
                            "library_use": passed,
                            "library_declarations": ["NumStability.fixture"] if passed else [],
                            "failure_code": None if passed else "PROOF_ERROR",
                            "failure_note": "" if passed else "fixture proof failure",
                            "protocol_complete": False,
                            "submission_sha256": "d" * 64 if passed else None,
                        }
                    )

        reasons = [
            "backend seeds are unavailable",
            "no frozen OCI image",
            "protocol claim not met: seed_enforced_by_agent",
        ]
        matrix_evidence = []
        for run in runs:
            record = {**run, "matrix_attempt": 1}
            record["matrix_record_sha256"] = document_digest(record)
            matrix_evidence.append(
                {
                    "run_id": record["run_id"],
                    "matrix_attempt": 1,
                    "matrix_record_sha256": record["matrix_record_sha256"],
                    "recomputed_matrix_record_sha256": record[
                        "matrix_record_sha256"
                    ],
                    "valid": True,
                    "record": record,
                }
            )
        result_check = {
            "kind": "highambench-result-set-check",
            "ok": True,
            "benchmark_id": benchmark_id,
            "metadata_document_sha256": {
                "config": document_digest(config),
                "manifest": document_digest(manifest),
                "run_order": document_digest(run_order),
            },
            "freeze_check_sha256": freeze_sha,
            "network_violation_run_count": 0,
            "network_integrity_failure_count": 0,
            "expected_agents": 1,
            "expected_pairs_per_agent": 9,
            "expected_final_runs_per_agent": 18,
            "input_record_count": 18,
            "selected_final_record_count": 18,
            "official_final_record_count": 0,
            "selected_final_run_ids": selected_ids,
            "analysis_profile": "observational_pilot",
            "reference_compliant": False,
            "official_scores_valid": False,
            "observational_results_allowed": True,
            "nonreference_reasons": reasons,
            "system_error_incident_count": 0,
            "system_error_incidents": [],
            "system_error_issue_count": 0,
            "system_error_issues": [],
            "system_error_handling_complete": True,
            "matrix_record_authentication": {
                "schema_version": 1,
                "hash_field": "matrix_record_sha256",
                "canonicalization": (
                    "compact_sorted_key_utf8_json_remove_only_hash_field"
                ),
                "selected_final_record_count": len(runs),
                "authenticated_final_record_count": len(runs),
                "all_selected_final_records_authenticated": True,
                "run_evidence": matrix_evidence,
            },
            "errors": [],
            "warnings": [],
        }
        analysis = {
            "schema_version": 1,
            "kind": "highambench-analysis",
            "included_unscored": False,
            "input_run_count": 18,
            "analyzed_run_count": 0,
            "excluded_run_count": 18,
            "official_scores_valid": False,
            "result_set_check": result_check,
            "observational_pilot_results": {
                "label": "observational pilot; not a reference-compliant HighamBench score",
                "official_scores_valid": False,
                "nonreference_reasons": reasons,
                "run_count": 18,
                "condition_summaries": condition_rows,
                "per_task_summaries": task_rows,
                "paired_comparisons": pair_rows,
                "per_task_paired_comparisons": task_pair_rows,
            },
            "per_run_results": runs,
            "condition_summaries": [],
            "per_task_summaries": [],
            "paired_comparisons": [],
            "per_task_paired_comparisons": [],
            "pair_problems": [],
            "malformed_input_lines": [],
        }
        write_json(self.analysis_path, analysis)

    def refresh_construction_pointer_digest(self) -> None:
        pointer = json.loads(self.library_pointer_path.read_text(encoding="utf-8"))
        pointer["current_evidence_sha256"] = digest_bytes(
            self.construction_path.read_bytes()
        )
        write_json(self.library_pointer_path, pointer)

    def refresh_freeze_digest(self) -> None:
        freeze = json.loads(self.freeze_path.read_text(encoding="utf-8"))
        analysis = json.loads(self.analysis_path.read_text(encoding="utf-8"))
        analysis["result_set_check"]["freeze_check_sha256"] = document_digest(
            freeze
        )
        write_json(self.analysis_path, analysis)

    def refresh_metadata_and_freeze_digests(self) -> None:
        config = json.loads(
            (self.root / "metadata" / "config.json").read_text(encoding="utf-8")
        )
        environment = json.loads(
            (self.root / "metadata" / "environment.json").read_text(
                encoding="utf-8"
            )
        )
        freeze = json.loads(self.freeze_path.read_text(encoding="utf-8"))
        freeze["metadata_document_sha256"]["config"] = document_digest(config)
        freeze["metadata_document_sha256"]["environment"] = document_digest(
            environment
        )
        write_json(self.freeze_path, freeze)
        analysis = json.loads(self.analysis_path.read_text(encoding="utf-8"))
        analysis["result_set_check"]["metadata_document_sha256"]["config"] = (
            document_digest(config)
        )
        analysis["result_set_check"]["freeze_check_sha256"] = document_digest(
            freeze
        )
        write_json(self.analysis_path, analysis)

    def refreeze_canary_evidence(self) -> None:
        canary_sha = digest_bytes(self.canary_path.read_bytes())
        config_path = self.root / "metadata" / "config.json"
        environment_path = self.root / "metadata" / "environment.json"
        release_path = self.root / "metadata" / "release_files.json"
        config = json.loads(config_path.read_text(encoding="utf-8"))
        environment = json.loads(environment_path.read_text(encoding="utf-8"))
        config["frozen_environment"]["token_control_canary"]["sha256"] = canary_sha
        environment["token_control_canary"]["sha256"] = canary_sha
        release = json.loads(release_path.read_text(encoding="utf-8"))
        entry = next(
            item
            for item in release["files"]
            if item["path"] == "metadata/evidence/token_control_live_canary.json"
        )
        entry["sha256"] = canary_sha
        entry["bytes"] = self.canary_path.stat().st_size
        write_json(release_path, release)
        release_sha = digest_bytes(release_path.read_bytes())
        config["frozen_environment"]["release_manifest_sha256"] = release_sha
        environment["release_manifest_sha256"] = release_sha
        write_json(config_path, config)
        write_json(environment_path, environment)
        freeze = json.loads(self.freeze_path.read_text(encoding="utf-8"))
        freeze["release_manifest"]["sha256"] = release_sha
        freeze["token_control_canary"]["sha256"] = canary_sha
        write_json(self.freeze_path, freeze)
        self.refresh_metadata_and_freeze_digests()

    def activate_fresh_novelty_override(self) -> None:
        task_ids = ["P01-T1", "P01-T2", "P01-T3"]

        def task_decisions() -> list[dict]:
            return [
                {
                    "task_id": task_id,
                    "source_faithful": True,
                    "exact_target_absent_from_mathlib": True,
                    "exact_target_absent_from_numstability": task_id != "P01-T1",
                    "decision": (
                        "fail_exact_target_collision"
                        if task_id == "P01-T1"
                        else "pass"
                    ),
                }
                for task_id in task_ids
            ]

        formal_path = self.root / "metadata" / "reviews" / "fresh_formal.json"
        source_path = self.root / "metadata" / "reviews" / "fresh_source.json"
        write_json(
            formal_path,
            {
                "kind": "fixture-fresh-formal-review",
                "record_status": "final",
                "reviewer": {
                    "id": "fixture-fresh-formal",
                    "identity": "Codex formal reviewer",
                    "fresh_context": True,
                },
                "overall_decision": "fail",
                "task_reviews": task_decisions(),
            },
        )
        write_json(
            source_path,
            {
                "kind": "fixture-fresh-source-review",
                "record_status": "current_with_blocking_defects",
                "reviewer": {
                    "identity": "Codex source reviewer",
                    "fresh_context": True,
                },
                "overall_decision": "fail_exact_target_novelty",
                "tasks": task_decisions(),
            },
        )

        config_path = self.root / "metadata" / "config.json"
        config = json.loads(config_path.read_text(encoding="utf-8"))
        config["private_measurement_review_override"] = {
            "enabled": True,
            "fresh_context_reviews_required": True,
            "source_fidelity_required": True,
            "scope": "exact-target novelty rejections only",
            "ignored_rejection_task_ids": ["P01-T1"],
            "note": "fixture private measurement only",
            "review_records": [
                {
                    "path": "metadata/reviews/fresh_formal.json",
                    "sha256": digest_bytes(formal_path.read_bytes()),
                    "record_status": "final",
                    "task_count": 3,
                },
                {
                    "path": "metadata/reviews/fresh_source.json",
                    "sha256": digest_bytes(source_path.read_bytes()),
                    "record_status": "current_with_blocking_defects",
                    "task_count": 3,
                },
            ],
        }
        write_json(config_path, config)

        freeze = json.loads(self.freeze_path.read_text(encoding="utf-8"))
        freeze["metadata_document_sha256"]["config"] = document_digest(config)
        write_json(self.freeze_path, freeze)
        analysis = json.loads(self.analysis_path.read_text(encoding="utf-8"))
        analysis["result_set_check"]["metadata_document_sha256"]["config"] = (
            document_digest(config)
        )
        analysis["result_set_check"]["freeze_check_sha256"] = document_digest(freeze)
        write_json(self.analysis_path, analysis)


class TierFourReportBranchTests(unittest.TestCase):
    def test_t4_private_proof_wording_is_not_obsolete(self) -> None:
        combined = (
            render_report_module.T4_SKELETON_PRIVATE_PROOF_NOTE
            + render_report_module.T4_PRIVATE_CONSTRUCTION_PROSE
        )
        self.assertIn("proof-complete private N/L solvability builds", combined)
        self.assertIn("private N/L builds are mandatory", combined)
        self.assertNotIn("T4 instead uses", combined)
        self.assertNotIn("no private gold proof", combined)

    def test_t4_coverage_uses_strict_claim_scoped_metadata(self) -> None:
        task = base_t4_task()
        task["classification_frozen_before_runs"] = True
        rows = render_report_module._t4_coverage_rows([task])
        self.assertEqual(
            rows,
            [
                {
                    "paper_id": "P01",
                    "task_id": "P01-T4",
                    "tier": "T4",
                    "stratum": "whole-paper",
                    "source_inventory_count": 3,
                    "included_source_count": 2,
                    "excluded_source_count": 1,
                    "reviewed_included_source_count": 2,
                    "declaration_count": 3,
                    "reviewed_declaration_count": 3,
                    "review_unit_count": 2,
                    "accepted_review_count": 2,
                    "accepted_review_unit_coverage_rate": 1.0,
                    "controlled_sorry_count": 1,
                    "measurement_ready": True,
                }
            ],
        )
        task["faithfulness_reviews"][0]["status"] = "pending"
        with self.assertRaisesRegex(ReportError, "invalid T4 whole-paper metadata"):
            render_report_module._t4_coverage_rows([task])

    def test_matrix_is_explicitly_t1_t3_only_when_t4_is_present(self) -> None:
        inputs = SimpleNamespace(
            tasks=(
                {"task_id": "P01-T1", "paper_id": "P01", "tier": "T1"},
                {"task_id": "P01-T4", "paper_id": "P01", "tier": "T4"},
            ),
            config={"repetitions": [{"id": "rep-01"}]},
        )
        selected_runs = [
            {
                "task_id": "P01-T1",
                "repetition_id": "rep-01",
                "condition": condition,
            }
            for condition in ("N", "L")
        ]
        condition_rows = [
            {"scope": scope, "condition": condition}
            for scope in ("overall", "T1")
            for condition in ("N", "L")
        ]
        task_rows = [
            {"task_id": "P01-T1", "condition": condition}
            for condition in ("N", "L")
        ]
        pair_rows = [{"scope": scope} for scope in ("overall", "T1")]
        task_pair_rows = [{"task_id": "P01-T1"}]
        render_report_module._check_matrix_coverage(
            inputs,
            selected_runs,
            condition_rows,
            task_rows,
            pair_rows,
            task_pair_rows,
        )
        with self.assertRaisesRegex(ReportError, "fixed task matrix exactly"):
            render_report_module._check_matrix_coverage(
                inputs,
                [
                    *selected_runs,
                    {
                        "task_id": "P01-T4",
                        "repetition_id": "rep-01",
                        "condition": "N",
                    },
                ],
                condition_rows,
                task_rows,
                pair_rows,
                task_pair_rows,
            )


class RenderReportTests(unittest.TestCase):
    def setUp(self) -> None:
        self.production_bindings = mock.patch.object(
            render_report_module.run_matrix,
            "production_freeze_bindings",
            return_value=(
                PRODUCTION_PROMPT_PROTOCOL,
                PRODUCTION_EXECUTION_COMPONENTS,
            ),
        )
        self.production_bindings_mock = self.production_bindings.start()
        self.token_canary_verifier = mock.patch.object(
            render_report_module.token_canary,
            "validate_attestation_document",
            side_effect=self._verify_fixture_token_canary,
        )
        self.token_canary_verifier_mock = self.token_canary_verifier.start()
        self.ultra_canary_verifier = mock.patch.object(
            render_report_module.ultra_canary,
            "verify_frozen_attestation",
            side_effect=self._verify_fixture_ultra_canary,
        )
        self.ultra_canary_verifier_mock = self.ultra_canary_verifier.start()

    def tearDown(self) -> None:
        self.ultra_canary_verifier.stop()
        self.token_canary_verifier.stop()
        self.production_bindings.stop()

    def test_collaboration_event_window_uses_emission_not_delayed_receipt_time(self) -> None:
        window_matches = (
            render_report_module._collaboration_event_observation_is_between_calls
        )
        self.assertTrue(
            window_matches(
                event_unix_ns=2_000_000,
                receipt_monotonic_ns=9_000_000,
                provider_commit_unix_ns=1_000_000,
                successor_admitted_unix_ns=3_000_000,
            )
        )
        self.assertFalse(
            window_matches(
                event_unix_ns=2_000_001,
                receipt_monotonic_ns=1_750_000,
                provider_commit_unix_ns=1_000_000,
                successor_admitted_unix_ns=3_000_000,
            )
        )
        self.assertFalse(
            window_matches(
                event_unix_ns=2_000_000,
                receipt_monotonic_ns=0,
                provider_commit_unix_ns=1_000_000,
                successor_admitted_unix_ns=3_000_000,
            )
        )

    def test_superseded_delivery_accepts_message_and_send_message_manifests(self) -> None:
        def item(
            index: int,
            item_type: str,
            *,
            name: str | None = None,
            namespace: str | None = None,
            call_id: str | None = None,
            arguments: bytes | None = None,
            wait_timeout_ms: int | None = None,
        ) -> dict:
            return {
                "index": index,
                "id": f"item-{index}",
                "type": item_type,
                "name": name,
                "namespace": namespace,
                "call_id": call_id,
                "payload_sha256": hashlib.sha256(
                    f"{index}:{item_type}".encode()
                ).hexdigest(),
                "payload_bytes": 10 + index,
                "arguments_sha256": (
                    hashlib.sha256(arguments).hexdigest()
                    if arguments is not None
                    else None
                ),
                "arguments_bytes": (
                    len(arguments) if arguments is not None else None
                ),
                "wait_timeout_ms": wait_timeout_ms,
            }

        send_arguments = b'{"target":"/root/child","message":"continue"}'
        wait_arguments = b'{"timeout_ms":30000}'
        shapes = {
            "message-only": [
                item(0, "reasoning"),
                item(1, "message"),
            ],
            "message-and-send": [
                item(0, "reasoning"),
                item(1, "message"),
                item(
                    2,
                    "function_call",
                    name="send_message",
                    namespace="collaboration",
                    call_id="send-call",
                    arguments=send_arguments,
                ),
            ],
            "job-1510008-message-superseded-wait": [
                item(0, "reasoning"),
                item(
                    1,
                    "function_call",
                    name="wait_agent",
                    namespace="collaboration",
                    call_id="wait-call",
                    arguments=wait_arguments,
                    wait_timeout_ms=30_000,
                ),
            ],
        }
        exact_wait_labels = {"job-1510008-message-superseded-wait"}
        metadata = {"request_kind": "turn"}
        delivery = {
            "successor_call_id": "provider-call-00000002",
            "successor_response_id": "successor-response",
        }
        for label, items in shapes.items():
            with self.subTest(label=label):
                response_id = f"{label}-response"
                manifest = {
                    "schema_version": 1,
                    "response_id": response_id,
                    "output_item_count": len(items),
                    "action_capable_item_count": sum(
                        entry["type"] == "function_call"
                        or entry["type"].endswith("_call")
                        for entry in items
                    ),
                    "items": items,
                }
                self.assertEqual(
                    render_report_module._gate_validate_response_output_manifest(
                        manifest, response_id, label
                    ),
                    label in exact_wait_labels,
                )
                call = {
                    "appserver_crossbind": None,
                    "crossed_cap": False,
                    "release_kind": "byte_identity",
                    "response_output_manifest": manifest,
                }
                self.assertTrue(
                    render_report_module._gate_superseded_delivery_is_exact(
                        call, metadata, delivery
                    )
                )

        for mutation in ("timeout", "name"):
            label = f"job-1510008-malformed-{mutation}"
            response_id = f"{label}-response"
            malformed_items = [
                dict(entry)
                for entry in shapes[
                    "job-1510008-message-superseded-wait"
                ]
            ]
            if mutation == "timeout":
                malformed_items[1]["wait_timeout_ms"] = 9_999
            else:
                malformed_items[1]["name"] = "send_message"
            malformed_manifest = {
                "schema_version": 1,
                "response_id": response_id,
                "output_item_count": len(malformed_items),
                "action_capable_item_count": 1,
                "items": malformed_items,
            }
            with self.subTest(malformed_wait=mutation), self.assertRaises(
                ReportError
            ):
                render_report_module._gate_validate_response_output_manifest(
                    malformed_manifest, response_id, label
                )

        bad_delivery = {**delivery, "successor_response_id": None}
        self.assertFalse(
            render_report_module._gate_superseded_delivery_is_exact(
                {
                    "appserver_crossbind": None,
                    "crossed_cap": False,
                    "release_kind": "byte_identity",
                },
                metadata,
                bad_delivery,
            )
        )

    def test_collaboration_routes_accept_only_adjacent_parent_child_messages(self) -> None:
        threads = [
            {
                "thread_id": "root-thread",
                "parent_thread_id": None,
                "agent_path": "root",
                "provisional": False,
                "spawn_binding_status": "root_zero",
            },
            {
                "thread_id": "library-thread",
                "parent_thread_id": "root-thread",
                "agent_path": "/root/library_search",
                "provisional": False,
                "spawn_binding_status": "resolved",
            },
            {
                "thread_id": "grandchild-thread",
                "parent_thread_id": "library-thread",
                "agent_path": "/root/library_search/reader",
                "provisional": False,
                "spawn_binding_status": "resolved",
            },
        ]
        route = render_report_module._rooted_collaboration_route_matches
        common = {
            "thread_accounting": threads,
            "root_thread_id": "root-thread",
        }
        self.assertTrue(
            route(
                thread_id="library-thread",
                author="/root",
                recipient="/root/library_search",
                **common,
            )
        )
        self.assertTrue(
            route(
                thread_id="root-thread",
                author="/root/library_search",
                recipient="/root",
                **common,
            )
        )
        self.assertFalse(
            route(
                thread_id="grandchild-thread",
                author="/root",
                recipient="/root/library_search/reader",
                **common,
            )
        )
        self.assertFalse(
            route(
                thread_id="library-thread",
                author="/root",
                recipient="/root",
                **common,
            )
        )

    def test_submission_barrier_v5_accepts_two_orders_and_rejects_ambiguity(self) -> None:
        dynamic_first = {
            "schema_version": (
                render_report_module.ultra_canary.codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION
            ),
            "inner_dynamic_item_started_at_monotonic_ns": 10,
            "captured_at_monotonic_ns": 11,
            "raw_response_observed_at_monotonic_ns": 12,
            "request_published_at_monotonic_ns": 13,
            "raw_response_completed_before_boundary_publication": True,
            "submission_event_order": (
                "inner_dynamic_call_before_raw_response_completed"
            ),
            "dynamic_call_observed_before_raw_response_completed": True,
            "raw_response_completed_before_dynamic_call_observed": False,
        }
        response_first = {
            **dynamic_first,
            "inner_dynamic_item_started_at_monotonic_ns": 11,
            "captured_at_monotonic_ns": 12,
            "raw_response_observed_at_monotonic_ns": 10,
            "submission_event_order": (
                "raw_response_completed_before_inner_dynamic_call"
            ),
            "dynamic_call_observed_before_raw_response_completed": False,
            "raw_response_completed_before_dynamic_call_observed": True,
        }
        self.assertEqual(
            render_report_module._validate_submission_event_order_v5(
                dynamic_first, "dynamic-first", require_event_timestamps=True
            ),
            "inner_dynamic_call_before_raw_response_completed",
        )
        self.assertEqual(
            render_report_module._validate_submission_event_order_v5(
                response_first, "response-first", require_event_timestamps=True
            ),
            "raw_response_completed_before_inner_dynamic_call",
        )
        invalid = (
            {**dynamic_first, "schema_version": 1},
            {**dynamic_first, "schema_version": 2},
            {**dynamic_first, "schema_version": 3},
            {**dynamic_first, "schema_version": 4},
            {
                **dynamic_first,
                "raw_response_completed_before_dynamic_call_observed": True,
            },
            {
                **dynamic_first,
                "dynamic_call_observed_before_raw_response_completed": False,
            },
            {
                **dynamic_first,
                "submission_event_order": (
                    "raw_response_completed_before_inner_dynamic_call"
                ),
            },
            {**dynamic_first, "raw_response_observed_at_monotonic_ns": 9},
            {**dynamic_first, "request_published_at_monotonic_ns": 11},
        )
        for value in invalid:
            with self.subTest(value=value), self.assertRaises(ReportError):
                render_report_module._validate_submission_event_order_v5(
                    value, "invalid-order", require_event_timestamps=True
                )

    @staticmethod
    def _verify_fixture_ultra_canary(
        project_root: Path,
        descriptor: dict,
        *,
        expected_benchmark_id: str,
        expected_agent: dict,
        expected_token_limit: int,
        expected_prompt_protocol: dict,
        expected_execution_components: dict,
    ) -> dict:
        if (
            expected_benchmark_id != "fixture-p01"
            or expected_token_limit != 300_000
            or expected_prompt_protocol != PRODUCTION_PROMPT_PROTOCOL
            or expected_execution_components != PRODUCTION_EXECUTION_COMPONENTS
            or expected_agent.get("id") != "fixture-agent"
        ):
            raise BenchmarkToolError("fixture Ultra canary production binding is stale")
        evidence = json.loads(
            (project_root / descriptor["path"]).read_text(encoding="utf-8")
        )
        return ultra_canary_summary(
            descriptor, evidence["outcome"]["accounting_projection"]
        )

    @staticmethod
    def _verify_fixture_token_canary(
        evidence: dict,
        *,
        project_root: Path,
        expected_benchmark_id: str,
        expected_agent: dict,
        expected_frozen_token_limit: int,
    ) -> dict:
        outcome = evidence.get("outcome")
        if (
            evidence.get("canary_id") != render_report_module.token_canary.CANARY_ID
            or evidence.get("benchmark_id") != expected_benchmark_id
            or evidence.get("agent") != expected_agent
            or evidence.get("scored") is not False
            or evidence.get("matrix_assignment") is not False
            or evidence.get("synthetic_input") is not True
            or evidence.get("benchmark_task_bytes_used") is not False
            or expected_frozen_token_limit != 300_000
            or not isinstance(outcome, dict)
            or outcome.get("thread_count") != 1
            or outcome.get("response_count") != 2
            or outcome.get("drain_complete") is not False
            or outcome.get("measurement_exact") is not True
        ):
            raise BenchmarkToolError(
                "synthetic token-canary lacks an exact root-only gate crossing"
            )
        artifact_root = project_root / str(evidence["artifact_root"])
        artifacts = {
            label: {
                "path": descriptor["path"],
                "sha256": descriptor["sha256"],
                "bytes": (artifact_root / descriptor["path"]).stat().st_size,
            }
            for label, descriptor in evidence["artifacts"].items()
        }
        return {
            "status": "passed",
            "canary_limit_tokens": evidence["controls"][
                "outer_canary_token_limit"
            ],
            "first_crossing_tokens": outcome["first_crossing_tokens"],
            "final_endpoint_tokens": outcome["total_model_tokens"],
            "thread_count": 1,
            "observed_child_thread_count": 0,
            "response_count": 2,
            "drain_complete": False,
            "provider_gate_quiescent": True,
            "measurement_exact": True,
            "synthetic_input": True,
            "matrix_assignment": False,
            "benchmark_task_bytes_used": False,
            "prompt_protocol": render_report_module.token_canary.PROMPT_PROTOCOL,
            "source_separation_audit_sha256": evidence["source_separation"][
                "audit_sha256"
            ],
            "prompt_release": outcome["prompt_release"],
            "accounting_projection": outcome["accounting_projection"],
            "artifacts": artifacts,
        }

    def test_report_independently_rederives_current_projection_summary(self) -> None:
        evidence = natural_projection_evidence()
        derived = _rederive_ultra_accounting_evidence(evidence)
        audit = {
            "run_id": "run-1",
            "valid": True,
            **derived,
            "evidence": evidence,
        }
        summary = {
            "schema_version": render_report_module.ACCOUNTING_PROJECTION_SCHEMA_VERSION,
            "spawn_binding_source": "raw_function_call.call_id=subAgentActivity.id",
            "selected_ultra_run_count": 1,
            "complete_projection_count": 1,
            "accepted_boundary_projection_count": 0,
            "natural_drain_projection_count": 1,
            "token_gate_crossing_projection_count": 0,
            "all_selected_ultra_projections_complete": True,
            "run_evidence": [audit],
        }
        checked = _validate_ultra_accounting_summary(
            {"ultra_accounting_projections": summary},
            [{"run_id": "run-1", "pass": False}],
        )
        self.assertIs(checked, summary)

        gate_evidence = natural_projection_evidence()
        top_totals = {
            field: gate_evidence["model_tokens" if field == "total_tokens" else field]
            for field in render_report_module.ACCOUNTING_TOKEN_FIELDS
        }
        self.assertEqual(
            render_report_module._rederive_projection_v4_gate(
                gate_evidence,
                accepted=False,
                response_ids=list(gate_evidence["response_ids"]),
                response_count=1,
                top_totals=top_totals,
            )["outcome"],
            "natural_drain",
        )

        missing_metadata = json.loads(json.dumps(gate_evidence))
        missing_metadata["appserver_response_ledger"][0]["provider_gate_call"][
            "request_metadata"
        ].pop("session_id")
        with self.assertRaisesRegex(ReportError, "delivery"):
            render_report_module._rederive_projection_v4_gate(
                missing_metadata,
                accepted=False,
                response_ids=list(missing_metadata["response_ids"]),
                response_count=1,
                top_totals=top_totals,
            )

        wrong_sanitizer = json.loads(json.dumps(gate_evidence))
        crossing_call = wrong_sanitizer["appserver_response_ledger"][0]["provider_gate_call"]
        crossing_call["crossed_cap"] = True
        crossing_call["release_kind"] = (
            render_report_module.runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE
        )
        crossing = {
            "call_id": crossing_call["call_id"],
            "response_id": crossing_call["response_id"],
            "sequence": 3,
            "previous_total": 0,
            "response_tokens": top_totals["total_tokens"],
            "completed_tokens": top_totals["total_tokens"],
            "overshoot_tokens": 0,
            "commit_unix_ns": crossing_call["commit_unix_ns"],
            "commit_monotonic_ns": crossing_call["commit_monotonic_ns"],
            "sole_inflight": True,
            "release_kind": crossing_call["release_kind"],
            "request_kind": "turn",
        }
        wrong_sanitizer["provider_token_gate"]["terminal"].update(
            {
                "close_reason": "token_limit",
                "crossing": crossing,
                "crossing_closed": True,
            }
        )
        wrong_sanitizer["first_crossing"] = {
            "response_id": crossing["response_id"],
            "tokens": crossing["completed_tokens"],
        }
        wrong_sanitizer["stop_reason"] = "token_limit"
        wrong_sanitizer["drain_complete"] = False
        wrong_sanitizer["adapter_teardown"]["immediate"] = True
        with self.assertRaisesRegex(ReportError, "token projection"):
            render_report_module._rederive_projection_v4_gate(
                wrong_sanitizer,
                accepted=False,
                response_ids=list(wrong_sanitizer["response_ids"]),
                response_count=1,
                top_totals=top_totals,
            )

        old_projection = {**summary, "schema_version": 3}
        with self.assertRaisesRegex(ReportError, "accounting summary"):
            _validate_ultra_accounting_summary(
                {"ultra_accounting_projections": old_projection},
                [{"run_id": "run-1", "pass": False}],
            )

        tampered = json.loads(json.dumps(summary))
        tampered["run_evidence"][0]["evidence"]["thread_accounting"][0][
            "cumulative_observation_count"
        ] = 0
        with self.assertRaisesRegex(ReportError, "observation"):
            _validate_ultra_accounting_summary(
                {"ultra_accounting_projections": tampered},
                [{"run_id": "run-1", "pass": False}],
            )

    def test_projection_supersession_uses_route_local_order(self) -> None:
        response_ids = [
            "root-superseded-1",
            "child-direct-1",
            "child-direct-2",
            "root-superseded-2",
            "child-direct-3",
            "root-suppressed",
            "root-direct",
        ]
        appserver_ids = [
            "child-direct-1",
            "child-direct-2",
            "child-direct-3",
            "root-direct",
        ]

        def direct(
            response_id: str,
            call_id: str,
            thread_id: str,
            turn_id: str,
        ) -> dict:
            return {
                "response_id": response_id,
                "call_id": call_id,
                "request_metadata": {
                    "thread_id": thread_id,
                    "turn_id": turn_id,
                    "request_kind": "turn",
                },
            }

        calls = [
            direct("child-direct-1", "child-call-1", "child", "child-turn"),
            direct("child-direct-2", "child-call-2", "child", "child-turn"),
            direct("child-direct-3", "child-call-3", "child", "child-turn"),
            direct("root-direct", "root-call-3", "root", "root-turn"),
        ]
        superseded = [
            {
                "response_id": "root-superseded-1",
                "provider_call_id": "root-call-1",
                "thread_id": "root",
                "turn_id": "root-turn",
                "successor_response_id": "root-superseded-2",
                "successor_call_id": "root-call-2",
            },
            {
                "response_id": "root-superseded-2",
                "provider_call_id": "root-call-2",
                "thread_id": "root",
                "turn_id": "root-turn",
                "successor_response_id": "root-suppressed",
                "successor_call_id": "root-wait-call",
            },
        ]
        suppressed = [
            {
                "response_id": "root-suppressed",
                "provider_call_id": "root-wait-call",
                "thread_id": "root",
                "turn_id": "root-turn",
                "successor_response_id": "root-direct",
                "successor_call_id": "root-call-3",
            }
        ]
        render_report_module._validate_projection_superseded_route_order(
            response_ids=response_ids,
            appserver_response_ids=appserver_ids,
            direct_calls=calls,
            suppressed_evidence=suppressed,
            superseded_evidence=superseded,
            discarded_evidence=[],
        )

        mutations = {
            "same_route_intervening": (
                json.loads(json.dumps(calls)),
                superseded,
                suppressed,
            ),
            "wrong_successor_call": (
                calls,
                json.loads(json.dumps(superseded)),
                suppressed,
            ),
            "wrong_successor_response": (
                calls,
                json.loads(json.dumps(superseded)),
                suppressed,
            ),
            "wrong_successor_thread": (
                json.loads(json.dumps(calls)),
                superseded,
                suppressed,
            ),
            "wrong_successor_turn": (
                json.loads(json.dumps(calls)),
                superseded,
                suppressed,
            ),
            "wrong_suppressed_successor_call": (
                calls,
                superseded,
                json.loads(json.dumps(suppressed)),
            ),
        }
        mutations["same_route_intervening"][0][0]["request_metadata"].update(
            {"thread_id": "root", "turn_id": "root-turn"}
        )
        mutations["wrong_successor_call"][1][0]["successor_call_id"] = (
            "wrong-call"
        )
        wrong_response = mutations["wrong_successor_response"][1][0]
        wrong_response["successor_response_id"] = "child-direct-2"
        wrong_response["successor_call_id"] = "child-call-2"
        mutations["wrong_successor_thread"][0][-1]["request_metadata"][
            "thread_id"
        ] = "child"
        mutations["wrong_successor_turn"][0][-1]["request_metadata"][
            "turn_id"
        ] = "other-root-turn"
        mutations["wrong_suppressed_successor_call"][2][0][
            "successor_call_id"
        ] = "wrong-direct-call"
        for name, (
            mutated_calls,
            mutated_superseded,
            mutated_suppressed,
        ) in mutations.items():
            with self.subTest(name=name), self.assertRaisesRegex(
                ReportError, "(?:superseded chain|suppressed bridge) changed"
            ):
                render_report_module._validate_projection_superseded_route_order(
                    response_ids=response_ids,
                    appserver_response_ids=appserver_ids,
                    direct_calls=mutated_calls,
                    suppressed_evidence=mutated_suppressed,
                    superseded_evidence=mutated_superseded,
                    discarded_evidence=[],
                )

    def test_report_reauthenticates_full_matrix_record_hash(self) -> None:
        record = {
            "run_id": "run-1",
            "pair_id": "pair-1",
            "paper_id": "P01",
            "task_id": "P01-T1",
            "tier": "T1",
            "repetition_id": "rep-01",
            "condition": "N",
            "pair_order": "N-first",
            "order_index": 1,
            "pass": False,
            "failure_code": "PROOF_ERROR",
            "agent_exit_code": 0,
            "matrix_attempt": 1,
        }
        record["matrix_record_sha256"] = document_digest(record)
        audit = {
            "run_id": "run-1",
            "matrix_attempt": 1,
            "matrix_record_sha256": record["matrix_record_sha256"],
            "recomputed_matrix_record_sha256": record["matrix_record_sha256"],
            "valid": True,
            "record": record,
        }
        summary = {
            "schema_version": 1,
            "hash_field": "matrix_record_sha256",
            "canonicalization": "compact_sorted_key_utf8_json_remove_only_hash_field",
            "selected_final_record_count": 1,
            "authenticated_final_record_count": 1,
            "all_selected_final_records_authenticated": True,
            "run_evidence": [audit],
        }
        selected = [{key: value for key, value in record.items() if key not in {"matrix_attempt", "matrix_record_sha256"}}]
        self.assertIs(
            _validate_matrix_record_summary(
                {"matrix_record_authentication": summary}, selected, ultra=False
            ),
            summary,
        )
        invalid_record = dict(record)
        invalid_record["matrix_attempt"] = False
        invalid_record.pop("matrix_record_sha256", None)
        invalid_record["matrix_record_sha256"] = document_digest(invalid_record)
        invalid_audit = {
            **audit,
            "matrix_attempt": False,
            "matrix_record_sha256": invalid_record["matrix_record_sha256"],
            "recomputed_matrix_record_sha256": invalid_record[
                "matrix_record_sha256"
            ],
            "record": invalid_record,
        }
        invalid_summary = {**summary, "run_evidence": [invalid_audit]}
        with self.assertRaisesRegex(ReportError, "self-authentication"):
            _validate_matrix_record_summary(
                {"matrix_record_authentication": invalid_summary},
                selected,
                ultra=False,
            )
        audit["record"]["failure_code"] = "NO_SUBMISSION"
        with self.assertRaisesRegex(ReportError, "self-authentication"):
            _validate_matrix_record_summary(
                {"matrix_record_authentication": summary}, selected
            )

    def test_provider_sse_auth_accepts_absent_header_and_rejects_ambiguity(self) -> None:
        body_sha = "a" * 64
        call = {
            "upstream_content_type_occurrences": 0,
            "upstream_content_type": None,
            "upstream_content_encoding_occurrences": 0,
            "upstream_content_encoding": None,
            "upstream_body_sha256": body_sha,
            "upstream_body_bytes": 123,
            "response_id": "response-1",
            "upstream_sse_authentication": {
                "schema_version": 1,
                "protocol": "highambench-responses-sse-envelope-v1",
                "parser": "highambench-strict-responses-sse-v2",
                "complete": True,
                "content_type_basis": (
                    "authenticated_stream_request_header_absent"
                ),
                "content_encoding_basis": "implicit_identity_header_absent",
                "json_event_count": 2,
                "completed_event_index": 1,
                "done_count": 0,
                "body_sha256": body_sha,
                "body_bytes": 123,
                "response_id": "response-1",
                "downstream_content_type_synthesized": True,
            },
        }
        self.assertTrue(
            render_report_module._gate_validate_upstream_sse_authentication(
                call, "missing-header fixture"
            )["complete"]
        )

        explicit_empty = json.loads(json.dumps(call))
        explicit_empty["upstream_content_type_occurrences"] = 1
        explicit_empty["upstream_content_type"] = ""
        with self.assertRaisesRegex(ReportError, "declared Content-Type"):
            render_report_module._gate_validate_upstream_sse_authentication(
                explicit_empty, "empty-header fixture"
            )

        duplicate = json.loads(json.dumps(call))
        duplicate["upstream_content_type_occurrences"] = 2
        with self.assertRaisesRegex(ReportError, "ambiguous"):
            render_report_module._gate_validate_upstream_sse_authentication(
                duplicate, "duplicate-header fixture"
            )

        empty_authentication = json.loads(json.dumps(call))
        empty_authentication["upstream_sse_authentication"] = {}
        with self.assertRaisesRegex(ReportError, "missing or extra field"):
            render_report_module._gate_validate_upstream_sse_authentication(
                empty_authentication, "empty-authentication fixture"
            )

        stale_parser = json.loads(json.dumps(call))
        stale_parser["upstream_sse_authentication"]["parser"] = (
            "highambench-strict-responses-sse-v1"
        )
        with self.assertRaisesRegex(ReportError, "inconsistent"):
            render_report_module._gate_validate_upstream_sse_authentication(
                stale_parser, "stale-parser fixture"
            )

        stale = json.loads(json.dumps(call))
        stale["upstream_sse_authentication"]["body_bytes"] = 122
        with self.assertRaisesRegex(ReportError, "inconsistent"):
            render_report_module._gate_validate_upstream_sse_authentication(
                stale, "stale-body fixture"
            )

    def test_provider_gate_authenticates_exact_runner_catalog_projection(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            for kind in ("token", "ultra"):
                with self.subTest(kind=kind):
                    evidence_path = (
                        fixture.canary_path
                        if kind == "token"
                        else fixture.ultra_canary_path
                    )
                    evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
                    root = fixture.repo / evidence["artifact_root"]
                    record_label = "record" if kind == "token" else "runner_record"
                    record_path = root / evidence["artifacts"][record_label]["path"]
                    gate_path = root / evidence["artifacts"]["provider_gate"]["path"]
                    record = json.loads(record_path.read_text(encoding="utf-8"))
                    gate = json.loads(gate_path.read_text(encoding="utf-8"))
                    catalog = record["provider_token_gate"]["model_catalog"]
                    self.assertEqual(
                        catalog,
                        {
                            "catalog_sha256": gate["configuration"][
                                "model_catalog_sha256"
                            ],
                            "entry_sha256": gate["configuration"][
                                "model_entry_sha256"
                            ],
                            "response_bound": (
                                render_report_module.runner.PROVIDER_RESPONSE_TOKEN_BOUND
                            ),
                        },
                    )
                    authentication = (
                        render_report_module._authenticate_provider_gate_record(
                            record,
                            artifact_path=gate_path,
                            label=f"production-shaped {kind} fixture",
                        )
                    )
                    self.assertEqual(
                        authentication["record_sha256"], gate["record_sha256"]
                    )
                    self.assertEqual(
                        (
                            record["token_usage"]["adapter_teardown"]["returncode"],
                            record["token_usage"]["adapter_teardown"]["signal"],
                        ),
                        (-15, "SIGTERM"),
                    )

                    clean_exit = json.loads(json.dumps(record))
                    clean_exit["token_usage"]["adapter_teardown"].update(
                        {"returncode": 0, "signal": None}
                    )
                    render_report_module._authenticate_provider_gate_record(
                        clean_exit,
                        artifact_path=gate_path,
                        label=f"clean-exit {kind} fixture",
                    )
                    killed_exit = json.loads(json.dumps(record))
                    killed_exit["token_usage"]["adapter_teardown"].update(
                        {"returncode": -9, "signal": "SIGKILL"}
                    )
                    render_report_module._authenticate_provider_gate_record(
                        killed_exit,
                        artifact_path=gate_path,
                        label=f"killed-exit {kind} fixture",
                    )

                    for returncode, signal in (
                        (0, "SIGTERM"),
                        (-15, None),
                        (-15, "SIGKILL"),
                        (-9, "SIGTERM"),
                        (1, None),
                        (15, "SIGTERM"),
                        (-1, "SIGTERM"),
                    ):
                        with self.subTest(
                            kind=kind,
                            teardown_returncode=returncode,
                            teardown_signal=signal,
                        ):
                            mismatched = json.loads(json.dumps(record))
                            mismatched["token_usage"]["adapter_teardown"].update(
                                {"returncode": returncode, "signal": signal}
                            )
                            with self.assertRaisesRegex(
                                ReportError,
                                "adapter did not exit cleanly at its gate endpoint",
                            ):
                                render_report_module._authenticate_provider_gate_record(
                                    mismatched,
                                    artifact_path=gate_path,
                                    label=f"mismatched teardown {kind} fixture",
                                )

                    expanded = json.loads(json.dumps(record))
                    expanded["provider_token_gate"]["model_catalog"]["slug"] = (
                        "gpt-5.6-sol"
                    )
                    with self.assertRaisesRegex(
                        ReportError, "model-catalog projection has a missing or extra field"
                    ):
                        render_report_module._authenticate_provider_gate_record(
                            expanded,
                            artifact_path=gate_path,
                            label=f"expanded {kind} fixture",
                        )

                    for field, replacement in (
                        ("catalog_sha256", "0" * 64),
                        ("entry_sha256", "0" * 64),
                        (
                            "response_bound",
                            render_report_module.runner.PROVIDER_RESPONSE_TOKEN_BOUND
                            - 1,
                        ),
                    ):
                        with self.subTest(kind=kind, tampered_field=field):
                            tampered = json.loads(json.dumps(record))
                            tampered["provider_token_gate"]["model_catalog"][
                                field
                            ] = replacement
                            with self.assertRaisesRegex(
                                ReportError, "model-catalog projection changed"
                            ):
                                render_report_module._authenticate_provider_gate_record(
                                    tampered,
                                    artifact_path=gate_path,
                                    label=f"tampered {kind} {field} fixture",
                                )

    def test_provider_gate_rejects_missing_tampered_poison_override_and_post_boundary(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)

            def canary_record(kind: str) -> tuple[dict, Path]:
                evidence_path = (
                    fixture.canary_path if kind == "token" else fixture.ultra_canary_path
                )
                evidence = json.loads(evidence_path.read_text(encoding="utf-8"))
                root = fixture.repo / evidence["artifact_root"]
                record_label = "record" if kind == "token" else "runner_record"
                record_path = root / evidence["artifacts"][record_label]["path"]
                gate_path = root / evidence["artifacts"]["provider_gate"]["path"]
                return json.loads(record_path.read_text(encoding="utf-8")), gate_path

            token_record, token_gate = canary_record("token")
            token_auth = render_report_module._authenticate_provider_gate_record(
                token_record, artifact_path=token_gate, label="positive token fixture"
            )
            self.assertEqual(token_auth["endpoint"], "sanitized_provider_gate_crossing")
            self.assertEqual(token_auth["response_count"], 2)
            self.assertEqual(token_auth["first_crossing"]["request_kind"], "compaction")
            self.assertEqual(token_auth["request_kinds"], ["turn", "compaction"])
            self.assertEqual(
                token_auth["release_kinds"],
                [
                    "byte_identity",
                    render_report_module.runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE,
                ],
            )
            wrong_first_kind = {
                **token_auth,
                "request_kinds": ["compaction", "compaction"],
            }
            with self.assertRaisesRegex(ReportError, "Token V8 gate shape"):
                render_report_module._validate_token_canary_provider_gate_shape(
                    wrong_first_kind, "wrong first call"
                )

            typed_bool = json.loads(json.dumps(token_record))
            typed_bool["provider_token_gate"]["final"]["authentication"]["derived"][
                "poisoned"
            ] = 0
            with self.assertRaises(ReportError):
                render_report_module._authenticate_provider_gate_record(
                    typed_bool,
                    artifact_path=token_gate,
                    label="integer poisoned flag",
                )

            old_enforcement = json.loads(json.dumps(token_record))
            enforcement = old_enforcement["token_measurement"]["limit_enforcement"]
            enforcement["final_drained_tokens"] = enforcement.pop(
                "final_endpoint_tokens"
            )
            with self.assertRaises(ReportError):
                render_report_module._authenticate_provider_gate_record(
                    old_enforcement,
                    artifact_path=token_gate,
                    label="old final-drained token field",
                )

            accepted_record, accepted_gate = canary_record("ultra")
            accepted_auth = render_report_module._authenticate_provider_gate_record(
                accepted_record,
                artifact_path=accepted_gate,
                label="positive accepted fixture",
            )
            self.assertEqual(accepted_auth["endpoint"], "accepted_provider_gate_close")

            missing = json.loads(json.dumps(accepted_record))
            missing.pop("provider_token_gate")
            with self.assertRaises(ReportError):
                render_report_module._authenticate_provider_gate_record(
                    missing, artifact_path=accepted_gate, label="missing gate"
                )

            tampered = json.loads(json.dumps(accepted_record))
            tampered["provider_token_gate"]["implementation_source_sha256"] = "0" * 64
            with self.assertRaises(ReportError):
                render_report_module._authenticate_provider_gate_record(
                    tampered, artifact_path=accepted_gate, label="tampered source"
                )

            for old_version in ("v1", "v2"):
                with self.subTest(old_version=old_version):
                    old_protocol = json.loads(json.dumps(accepted_record))
                    old_protocol["provider_token_gate"]["protocol"] = (
                        f"highambench-provider-token-gate-{old_version}"
                    )
                    with self.assertRaises(ReportError):
                        render_report_module._authenticate_provider_gate_record(
                            old_protocol,
                            artifact_path=accepted_gate,
                            label=f"old {old_version} gate protocol",
                        )

            poisoned = json.loads(json.dumps(accepted_record))
            poisoned["token_usage"]["provider_token_gate"]["terminal"].update(
                {"poisoned": True, "poison_reasons": ["fixture poison"]}
            )
            with self.assertRaises(ReportError):
                render_report_module._authenticate_provider_gate_record(
                    poisoned, artifact_path=accepted_gate, label="poisoned gate"
                )

            override = json.loads(json.dumps(accepted_record))
            override["provider_token_gate"]["status"] = "test_override"
            with self.assertRaises(ReportError):
                render_report_module._authenticate_provider_gate_record(
                    override, artifact_path=accepted_gate, label="test override"
                )

            with self.assertRaises(ReportError):
                render_report_module._authenticate_provider_gate_record(
                    accepted_record,
                    artifact_path=accepted_gate.with_name("missing-provider-gate.json"),
                    label="missing artifact",
                )

            post_boundary = json.loads(json.dumps(accepted_record))
            commit = post_boundary["token_usage"]["appserver_response_ledger"][0][
                "provider_gate_call"
            ]["commit_monotonic_ns"]
            post_boundary["token_usage"]["submission_boundary"][
                "request_published_at_monotonic_ns"
            ] = commit - 1
            with self.assertRaisesRegex(ReportError, "ordered after publication"):
                render_report_module._authenticate_provider_gate_record(
                    post_boundary,
                    artifact_path=accepted_gate,
                    label="post-boundary provider call",
                )

            reconciled = json.loads(json.dumps(accepted_record))
            record = json.loads(accepted_gate.read_text(encoding="utf-8"))
            direct = json.loads(json.dumps(record["calls"][0]))
            direct_admit_mono = direct["admitted_monotonic_ns"]
            direct_admit_unix = direct["admitted_unix_ns"]
            wait_usage = {
                "input_tokens": 10,
                "cached_input_tokens": 2,
                "cache_write_input_tokens": 0,
                "output_tokens": 2,
                "reasoning_output_tokens": 1,
                "total_tokens": 12,
            }
            raw_wait_usage = {
                "input_tokens": 10,
                "input_tokens_details": {
                    "cached_tokens": 2,
                    "cache_write_tokens": 0,
                },
                "output_tokens": 2,
                "output_tokens_details": {"reasoning_tokens": 1},
                "total_tokens": 12,
            }
            wait_response_id = "suppressed-wait-response"
            arguments = b'{"timeout_ms":30000}'
            suppressed = json.loads(json.dumps(direct))
            suppressed.update(
                {
                    "response_id": wait_response_id,
                    "usage": raw_wait_usage,
                    "normalized_usage": wait_usage,
                    "previous_total": 0,
                    "committed_total": 12,
                    "admitted_monotonic_ns": direct_admit_mono - 150_000,
                    "upstream_start_monotonic_ns": direct_admit_mono - 100_000,
                    "commit_monotonic_ns": direct_admit_mono - 50_000,
                    "admitted_unix_ns": direct_admit_unix - 3_000_000,
                    "upstream_start_unix_ns": direct_admit_unix - 2_500_000,
                    "commit_unix_ns": direct_admit_unix - 2_000_000,
                    "crossed_cap": False,
                    "release_kind": "byte_identity",
                    "released_body_sha256": direct["upstream_body_sha256"],
                    "released_body_bytes": direct["upstream_body_bytes"],
                    "released_sanitized_event": None,
                    "released_sanitized_events": None,
                    "released_sanitized_body_utf8": None,
                    "response_output_manifest": {
                        "schema_version": 1,
                        "response_id": wait_response_id,
                        "output_item_count": 2,
                        "action_capable_item_count": 1,
                        "items": [
                            {
                                "index": 0,
                                "id": "reasoning-item",
                                "type": "reasoning",
                                "name": None,
                                "namespace": None,
                                "call_id": None,
                                "payload_sha256": "a" * 64,
                                "payload_bytes": 10,
                                "arguments_sha256": None,
                                "arguments_bytes": None,
                                "wait_timeout_ms": None,
                            },
                            {
                                "index": 1,
                                "id": "wait-item",
                                "type": "function_call",
                                "name": "wait_agent",
                                "namespace": "collaboration",
                                "call_id": "wait-call",
                                "payload_sha256": "b" * 64,
                                "payload_bytes": 20,
                                "arguments_sha256": hashlib.sha256(arguments).hexdigest(),
                                "arguments_bytes": len(arguments),
                                "wait_timeout_ms": 30_000,
                            },
                        ],
                    },
                    "appserver_crossbind": None,
                    "error": None,
                }
            )
            suppressed["upstream_sse_authentication"]["response_id"] = wait_response_id
            direct.update(
                {
                    "sequence": 4,
                    "call_id": "provider-call-00000004",
                    "completed_before": 12,
                    "reserved_before": 12,
                    "reservation_after": 12
                    + render_report_module.runner.PROVIDER_RESPONSE_TOKEN_BOUND,
                    "previous_total": 12,
                    "committed_total": 12 + direct["normalized_usage"]["total_tokens"],
                }
            )
            suppressed["appserver_delivery"] = {
                "kind": "suppressed_collaboration_wait",
                "successor_call_id": direct["call_id"],
                "successor_response_id": direct["response_id"],
                "bind_unix_ns": direct["appserver_crossbind"]["bind_unix_ns"] + 10,
                "bind_monotonic_ns": direct["appserver_crossbind"][
                    "bind_monotonic_ns"
                ]
                + 10,
            }
            record["calls"] = [suppressed, direct]
            record["state"]["completed_tokens"] = direct["committed_total"]
            record["state"]["sequence"] = 5
            record["transitions"][-1]["sequence"] = 5
            record.pop("record_sha256")
            record["record_sha256"] = hashlib.sha256(
                render_report_module._gate_canonical_newline(record)
            ).hexdigest()
            accepted_gate.chmod(0o600)
            accepted_gate.write_bytes(
                render_report_module._gate_canonical_newline(record)
            )
            accepted_gate.chmod(0o444)

            usage = reconciled["token_usage"]
            usage["submission_boundary"]["provider_gate_close"]["sequence"] = 5
            appserver_usage = dict(usage["appserver_usage"])
            provider_usage = {
                field: appserver_usage[field] + wait_usage[field]
                for field in render_report_module.ACCOUNTING_TOKEN_FIELDS
            }
            provider_ids = [wait_response_id, direct["response_id"]]
            evidence = {
                "response_id": wait_response_id,
                "provider_call_id": suppressed["call_id"],
                "thread_id": suppressed["request_metadata"]["thread_id"],
                "turn_id": suppressed["request_metadata"]["turn_id"],
                "successor_response_id": direct["response_id"],
                "successor_call_id": direct["call_id"],
                "agent_message_item_id": "child-final-item",
                "agent_message_sha256": "c" * 64,
                "agent_message_author": "/root/fixture_child",
                "agent_message_recipient": "/root",
                # Collaboration event timestamps have millisecond resolution;
                # leave a full millisecond before successor admission.
                "agent_message_observed_at_unix_ns": direct_admit_unix - 1_500_000,
                "agent_message_observed_at_monotonic_ns": direct_admit_mono - 25_000,
            }
            usage.update(
                {
                    "input_tokens": provider_usage["input_tokens"],
                    "cached_input_tokens": provider_usage["cached_input_tokens"],
                    "cache_write_input_tokens": provider_usage[
                        "cache_write_input_tokens"
                    ],
                    "output_tokens": provider_usage["output_tokens"],
                    "reasoning_output_tokens": provider_usage[
                        "reasoning_output_tokens"
                    ],
                    "model_tokens": provider_usage["total_tokens"],
                    "total_tokens": provider_usage["total_tokens"],
                    "call_count": 2,
                    "response_count": 2,
                    "response_ids": provider_ids,
                    "provider_response_count": 2,
                    "provider_response_ids": provider_ids,
                    "provider_usage": provider_usage,
                    "suppressed_collaboration_wait_response_count": 1,
                    "suppressed_collaboration_wait_response_ids": [wait_response_id],
                    "suppressed_collaboration_wait_usage": wait_usage,
                    "suppressed_collaboration_wait_evidence": [evidence],
                }
            )
            usage["provider_usage_reconciliation"] = {
                "schema_version": render_report_module.codex_isolated.PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION,
                "provider_response_count": 2,
                "appserver_response_count": 1,
                "suppressed_collaboration_wait_response_count": 1,
                "provider_usage": provider_usage,
                "appserver_usage": appserver_usage,
                "suppressed_collaboration_wait_usage": wait_usage,
                "provider_response_ids": provider_ids,
                "appserver_response_ids": [direct["response_id"]],
                "suppressed_collaboration_wait_response_ids": [wait_response_id],
                "suppressed_collaboration_wait_evidence": [evidence],
                "superseded_by_collaboration_message_response_count": 0,
                "superseded_by_collaboration_message_usage": {
                    field: 0 for field in provider_usage
                },
                "superseded_by_collaboration_message_response_ids": [],
                "superseded_by_collaboration_message_evidence": [],
                "discarded_after_explicit_child_interrupt_response_count": 0,
                "discarded_after_explicit_child_interrupt_usage": {
                    field: 0 for field in provider_usage
                },
                "discarded_after_explicit_child_interrupt_response_ids": [],
                "discarded_after_explicit_child_interrupt_evidence": [],
            }
            usage["appserver_response_ledger"][0]["provider_gate_call"] = direct
            usage["provider_token_gate"]["record_sha256"] = record["record_sha256"]
            usage["provider_token_gate"]["live"] = record["state"]
            usage["provider_token_gate"]["terminal"] = record["state"]

            payload = render_report_module._gate_canonical_newline(record)
            file_sha = hashlib.sha256(payload).hexdigest()
            final = reconciled["provider_token_gate"]["final"]
            final["file"].update(
                {"size_bytes": len(payload), "file_sha256": file_sha}
            )
            final["authentication"] = {
                "path": str(accepted_gate),
                "file_sha256": file_sha,
                "record_sha256": record["record_sha256"],
                "size_bytes": len(payload),
                "mode": "0444",
                "authenticated": True,
                "record": record,
                "derived": {
                    "completed_tokens": provider_usage["total_tokens"],
                    "response_count": 2,
                    "response_ids": provider_ids,
                    "provider_response_count": 2,
                    "provider_response_ids": provider_ids,
                    "appserver_response_count": 1,
                    "appserver_response_ids": [direct["response_id"]],
                    "suppressed_collaboration_wait_response_count": 1,
                    "suppressed_collaboration_wait_response_ids": [wait_response_id],
                    "superseded_by_collaboration_message_response_count": 0,
                    "superseded_by_collaboration_message_response_ids": [],
                    "discarded_after_explicit_child_interrupt_response_count": 0,
                    "discarded_after_explicit_child_interrupt_response_ids": [],
                    "first_crossing": None,
                    "poisoned": False,
                    "appserver_deliveries_reconciled": True,
                },
            }
            reconciled_auth = render_report_module._authenticate_provider_gate_record(
                reconciled,
                artifact_path=accepted_gate,
                label="suppressed-wait positive fixture",
            )
            self.assertEqual(reconciled_auth["provider_response_count"], 2)
            self.assertEqual(reconciled_auth["appserver_response_count"], 1)
            self.assertEqual(
                reconciled_auth["suppressed_collaboration_wait_response_count"], 1
            )

            bad_evidence = json.loads(json.dumps(reconciled))
            bad_evidence["token_usage"][
                "suppressed_collaboration_wait_evidence"
            ][0]["agent_message_recipient"] = "/root/other"
            bad_evidence["token_usage"]["provider_usage_reconciliation"][
                "suppressed_collaboration_wait_evidence"
            ][0]["agent_message_recipient"] = "/root/other"
            with self.assertRaisesRegex(ReportError, "unique child result"):
                render_report_module._authenticate_provider_gate_record(
                    bad_evidence,
                    artifact_path=accepted_gate,
                    label="suppressed-wait bad evidence",
                )

            # Extend the authenticated two-call wait fixture with the exact
            # job-1510529 shape: a general supersession immediately names the
            # suppressed wait, which in turn names the earliest direct call.
            mixed = json.loads(json.dumps(reconciled))
            mixed_record = json.loads(json.dumps(record))
            mixed_suppressed = mixed_record["calls"][0]
            mixed_direct = mixed_record["calls"][1]
            generic_response_id = "superseded-before-wait-response"
            generic = json.loads(json.dumps(mixed_suppressed))
            generic.update(
                {
                    "sequence": 3,
                    "call_id": "provider-call-00000003",
                    "response_id": generic_response_id,
                    "completed_before": 0,
                    "reserved_before": 0,
                    "reservation_after": render_report_module.runner.PROVIDER_RESPONSE_TOKEN_BOUND,
                    "previous_total": 0,
                    "committed_total": wait_usage["total_tokens"],
                    "admitted_monotonic_ns": direct_admit_mono - 190_000,
                    "upstream_start_monotonic_ns": direct_admit_mono - 180_000,
                    "commit_monotonic_ns": direct_admit_mono - 160_000,
                    "admitted_unix_ns": direct_admit_unix - 6_000_000,
                    "upstream_start_unix_ns": direct_admit_unix - 5_500_000,
                    "commit_unix_ns": direct_admit_unix - 5_000_000,
                    "response_output_manifest": {
                        "schema_version": 1,
                        "response_id": generic_response_id,
                        "output_item_count": 2,
                        "action_capable_item_count": 0,
                        "items": [
                            {
                                "index": 0,
                                "id": "generic-reasoning-item",
                                "type": "reasoning",
                                "name": None,
                                "namespace": None,
                                "call_id": None,
                                "payload_sha256": "d" * 64,
                                "payload_bytes": 10,
                                "arguments_sha256": None,
                                "arguments_bytes": None,
                                "wait_timeout_ms": None,
                            },
                            {
                                "index": 1,
                                "id": "generic-message-item",
                                "type": "message",
                                "name": None,
                                "namespace": None,
                                "call_id": None,
                                "payload_sha256": "e" * 64,
                                "payload_bytes": 20,
                                "arguments_sha256": None,
                                "arguments_bytes": None,
                                "wait_timeout_ms": None,
                            },
                        ],
                    },
                    "appserver_crossbind": None,
                }
            )
            generic["upstream_sse_authentication"][
                "response_id"
            ] = generic_response_id
            mixed_suppressed.update(
                {
                    "sequence": 4,
                    "call_id": "provider-call-00000004",
                    "completed_before": wait_usage["total_tokens"],
                    "reserved_before": wait_usage["total_tokens"],
                    "reservation_after": wait_usage["total_tokens"]
                    + render_report_module.runner.PROVIDER_RESPONSE_TOKEN_BOUND,
                    "previous_total": wait_usage["total_tokens"],
                    "committed_total": 2 * wait_usage["total_tokens"],
                }
            )
            mixed_direct.update(
                {
                    "sequence": 5,
                    "call_id": "provider-call-00000005",
                    "completed_before": 2 * wait_usage["total_tokens"],
                    "reserved_before": 2 * wait_usage["total_tokens"],
                    "reservation_after": 2 * wait_usage["total_tokens"]
                    + render_report_module.runner.PROVIDER_RESPONSE_TOKEN_BOUND,
                    "previous_total": 2 * wait_usage["total_tokens"],
                    "committed_total": 2 * wait_usage["total_tokens"]
                    + mixed_direct["normalized_usage"]["total_tokens"],
                }
            )
            mixed_suppressed["appserver_delivery"].update(
                {
                    "successor_call_id": mixed_direct["call_id"],
                    "successor_response_id": mixed_direct["response_id"],
                }
            )
            generic["appserver_delivery"] = {
                "kind": "superseded_by_collaboration_message",
                "successor_call_id": mixed_suppressed["call_id"],
                "successor_response_id": mixed_suppressed["response_id"],
                "bind_unix_ns": mixed_suppressed["appserver_delivery"][
                    "bind_unix_ns"
                ]
                + 10,
                "bind_monotonic_ns": mixed_suppressed["appserver_delivery"][
                    "bind_monotonic_ns"
                ]
                + 10,
            }
            mixed_record["calls"] = [generic, mixed_suppressed, mixed_direct]
            mixed_record["state"].update(
                {
                    "completed_tokens": mixed_direct["committed_total"],
                    "sequence": 6,
                }
            )
            mixed_record["transitions"][-1]["sequence"] = 6
            mixed_record.pop("record_sha256")
            mixed_record["record_sha256"] = hashlib.sha256(
                render_report_module._gate_canonical_newline(mixed_record)
            ).hexdigest()
            accepted_gate.chmod(0o600)
            accepted_gate.write_bytes(
                render_report_module._gate_canonical_newline(mixed_record)
            )
            accepted_gate.chmod(0o444)

            mixed_usage = mixed["token_usage"]
            mixed_usage["submission_boundary"]["provider_gate_close"][
                "sequence"
            ] = 6
            mixed_provider_usage = {
                field: appserver_usage[field] + 2 * wait_usage[field]
                for field in render_report_module.ACCOUNTING_TOKEN_FIELDS
            }
            mixed_provider_ids = [
                generic_response_id,
                wait_response_id,
                mixed_direct["response_id"],
            ]
            mixed_wait_evidence = json.loads(json.dumps(evidence))
            mixed_wait_evidence["provider_call_id"] = mixed_suppressed[
                "call_id"
            ]
            mixed_wait_evidence["successor_call_id"] = mixed_direct["call_id"]
            generic_evidence = {
                "response_id": generic_response_id,
                "provider_call_id": generic["call_id"],
                "thread_id": generic["request_metadata"]["thread_id"],
                "turn_id": generic["request_metadata"]["turn_id"],
                "successor_response_id": mixed_suppressed["response_id"],
                "successor_call_id": mixed_suppressed["call_id"],
                "collaboration_messages": [
                    {
                        "item_id": "child-message-before-wait",
                        "item_sha256": "f" * 64,
                        "author": "/root/fixture_child",
                        "recipient": "/root",
                        "observed_at_unix_ns": direct_admit_unix - 4_500_000,
                        "observed_at_monotonic_ns": direct_admit_mono
                        - 155_000,
                    }
                ],
            }
            mixed_usage.update(
                {
                    "input_tokens": mixed_provider_usage["input_tokens"],
                    "cached_input_tokens": mixed_provider_usage[
                        "cached_input_tokens"
                    ],
                    "cache_write_input_tokens": mixed_provider_usage[
                        "cache_write_input_tokens"
                    ],
                    "output_tokens": mixed_provider_usage["output_tokens"],
                    "reasoning_output_tokens": mixed_provider_usage[
                        "reasoning_output_tokens"
                    ],
                    "model_tokens": mixed_provider_usage["total_tokens"],
                    "total_tokens": mixed_provider_usage["total_tokens"],
                    "call_count": 3,
                    "response_count": 3,
                    "response_ids": mixed_provider_ids,
                    "provider_response_count": 3,
                    "provider_response_ids": mixed_provider_ids,
                    "provider_usage": mixed_provider_usage,
                    "suppressed_collaboration_wait_evidence": [
                        mixed_wait_evidence
                    ],
                    "superseded_by_collaboration_message_response_count": 1,
                    "superseded_by_collaboration_message_response_ids": [
                        generic_response_id
                    ],
                    "superseded_by_collaboration_message_usage": wait_usage,
                    "superseded_by_collaboration_message_evidence": [
                        generic_evidence
                    ],
                }
            )
            mixed_usage["provider_usage_reconciliation"].update(
                {
                    "provider_response_count": 3,
                    "provider_usage": mixed_provider_usage,
                    "provider_response_ids": mixed_provider_ids,
                    "suppressed_collaboration_wait_evidence": [
                        mixed_wait_evidence
                    ],
                    "superseded_by_collaboration_message_response_count": 1,
                    "superseded_by_collaboration_message_usage": wait_usage,
                    "superseded_by_collaboration_message_response_ids": [
                        generic_response_id
                    ],
                    "superseded_by_collaboration_message_evidence": [
                        generic_evidence
                    ],
                }
            )
            mixed_usage["appserver_response_ledger"][0][
                "provider_gate_call"
            ] = mixed_direct
            mixed_usage["thread_accounting"] = [
                {
                    "thread_id": mixed_usage["root_thread_id"],
                    "parent_thread_id": None,
                    "agent_path": "root",
                    "provisional": False,
                    "spawn_binding_status": "root_zero",
                },
                {
                    "thread_id": "fixture-child-thread",
                    "parent_thread_id": mixed_usage["root_thread_id"],
                    "agent_path": "/root/fixture_child",
                    "provisional": False,
                    "spawn_binding_status": "resolved",
                },
            ]
            mixed_usage["provider_token_gate"][
                "record_sha256"
            ] = mixed_record["record_sha256"]
            mixed_usage["provider_token_gate"]["live"] = mixed_record["state"]
            mixed_usage["provider_token_gate"]["terminal"] = mixed_record[
                "state"
            ]

            mixed_payload = render_report_module._gate_canonical_newline(
                mixed_record
            )
            mixed_file_sha = hashlib.sha256(mixed_payload).hexdigest()
            mixed_final = mixed["provider_token_gate"]["final"]
            mixed_final["file"].update(
                {
                    "size_bytes": len(mixed_payload),
                    "file_sha256": mixed_file_sha,
                }
            )
            mixed_authentication = mixed_final["authentication"]
            mixed_authentication.update(
                {
                    "file_sha256": mixed_file_sha,
                    "record_sha256": mixed_record["record_sha256"],
                    "size_bytes": len(mixed_payload),
                    "record": mixed_record,
                }
            )
            mixed_authentication["derived"].update(
                {
                    "completed_tokens": mixed_provider_usage["total_tokens"],
                    "response_count": 3,
                    "response_ids": mixed_provider_ids,
                    "provider_response_count": 3,
                    "provider_response_ids": mixed_provider_ids,
                    "superseded_by_collaboration_message_response_count": 1,
                    "superseded_by_collaboration_message_response_ids": [
                        generic_response_id
                    ],
                }
            )
            mixed_auth = render_report_module._authenticate_provider_gate_record(
                mixed,
                artifact_path=accepted_gate,
                label="job-1510529 mixed-chain fixture",
            )
            self.assertEqual(mixed_auth["provider_response_count"], 3)
            self.assertEqual(
                mixed_auth["superseded_by_collaboration_message_response_count"],
                1,
            )

            wrong_bridge_call = json.loads(json.dumps(mixed))
            for target in (
                wrong_bridge_call["token_usage"],
                wrong_bridge_call["token_usage"]["provider_usage_reconciliation"],
            ):
                target["suppressed_collaboration_wait_evidence"][0][
                    "successor_call_id"
                ] = "wrong-direct-call"
            with self.assertRaises(ReportError):
                render_report_module._authenticate_provider_gate_record(
                    wrong_bridge_call,
                    artifact_path=accepted_gate,
                    label="job-1510529 mismatched wait bridge",
                )

    def test_report_rederives_prompt_release_and_request_publication(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            logs = root / "results" / "logs"
            logs.mkdir(parents=True)
            prompt = "Solve the fixed theorem.\n"
            prompt_bytes = prompt.encode()
            nonce = "e" * 64
            release_ns = 10_000_000_000
            usage_path = logs / "run-1.usage.json"
            paths = {
                "ready": logs / "run-1.prompt-ready.json",
                "go": logs / "run-1.prompt-go.json",
                "release": logs / "run-1.prompt-release.json",
            }
            common = {
                "schema_version": 1,
                "protocol_version": "highambench-prompt-release-v1",
                "handshake_nonce": nonce,
                "run_id": "run-1",
                "condition": "N",
                "model": "model-v1",
                "reasoning_effort": "ultra",
                "root_thread_id": "root-thread",
                "turn_start_request_id": 3,
                "effective_prompt_sha256": hashlib.sha256(prompt_bytes).hexdigest(),
                "effective_prompt_bytes": len(prompt_bytes),
                "adapter_name": "codex_isolated.py",
                "adapter_version": "1",
                "app_server_client_name": "highambench-isolated",
                "app_server_client_version": "1",
                "elapsed_clock": "CLOCK_MONOTONIC",
            }

            def signed(value: dict, field: str, path: Path) -> tuple[dict, dict]:
                result = dict(value)
                result[field] = document_digest(result)
                payload = (json.dumps(result, sort_keys=True, separators=(",", ":")) + "\n").encode()
                path.write_bytes(payload)
                path.chmod(0o444)
                return result, {
                    "path": str(path),
                    "file_sha256": hashlib.sha256(payload).hexdigest(),
                    "record_sha256": result[field],
                    "record": result,
                }

            ready, ready_descriptor = signed(
                {
                    **common,
                    "kind": "highambench_prompt_ready",
                    "turn_start_write_state": "not_started",
                    "ready_at_monotonic_ns": release_ns - 2,
                    "ready_at_unix_ns": 20_000_000_000,
                },
                "ready_sha256",
                paths["ready"],
            )
            go, go_descriptor = signed(
                {
                    **common,
                    "kind": "highambench_prompt_go",
                    "ready_sha256": ready["ready_sha256"],
                    "turn_start_write_authorized": True,
                    "authorized_at_monotonic_ns": release_ns - 1,
                    "authorized_at_unix_ns": 20_000_000_001,
                },
                "go_sha256",
                paths["go"],
            )
            wire = render_report_module._prompt_turn_start_wire(
                prompt=prompt,
                root_thread_id="root-thread",
                model="model-v1",
                reasoning_effort="ultra",
            )
            _, release_descriptor = signed(
                {
                    **common,
                    "kind": "highambench_prompt_released",
                    "ready_sha256": ready["ready_sha256"],
                    "go_sha256": go["go_sha256"],
                    "turn_start_write_state": "flushed",
                    "timestamp_capture_point": "immediately_before_turn_start_write",
                    "turn_start_request_sha256": hashlib.sha256(wire).hexdigest(),
                    "turn_start_request_bytes": len(wire),
                    "released_at_monotonic_ns": release_ns,
                    "released_at_unix_ns": 20_000_000_002,
                    "turn_start_flushed_at_monotonic_ns": release_ns + 1,
                    "turn_start_flushed_at_unix_ns": 20_000_000_003,
                },
                "release_sha256",
                paths["release"],
            )
            codex = render_report_module.ultra_canary.codex_isolated
            nested_wire = {
                **nested_submission_wire_fixture(
                    outer_observed_ns=release_ns + 50_000_000,
                    inner_started_ns=release_ns + 100_000_000,
                ),
            }
            request_path = logs / "run-1.submission-request.json"
            request, request_descriptor = signed(
                {
                    **nested_wire,
                    "kind": "highambench_submission_request",
                    "inner_dynamic_item_started_at_monotonic_ns": (
                        release_ns + 100_000_000
                    ),
                    "captured_at_monotonic_ns": release_ns + 200_000_000,
                    "raw_response_observed_at_monotonic_ns": (
                        release_ns + 300_000_000
                    ),
                    "request_published_at_monotonic_ns": release_ns + 600_000_000,
                    "request_published_at_unix_ns": 20_600_000_002,
                    "raw_response_completed_before_boundary_publication": True,
                    "submission_event_order": (
                        "inner_dynamic_call_before_raw_response_completed"
                    ),
                    "dynamic_call_observed_before_raw_response_completed": True,
                    "raw_response_completed_before_dynamic_call_observed": False,
                },
                "request_sha256",
                request_path,
            )
            command = ["adapter", "--usage-output", str(usage_path)]
            for option, value in (
                ("--prompt-ready-output", paths["ready"]),
                ("--prompt-go-input", paths["go"]),
                ("--prompt-release-output", paths["release"]),
                ("--prompt-handshake-nonce", nonce),
                ("--prompt-run-id", "run-1"),
            ):
                command.extend((option, str(value)))
            record = {
                "run_id": "run-1",
                "task_id": "P01-T1",
                "condition": "N",
                "pass": True,
                "first_valid_seconds": 0.6,
                "actual_stop_seconds": 0.7,
                "scored_elapsed_seconds": 0.6,
                "time_measurement": (
                    "authenticated CLOCK_MONOTONIC turn/start write to authenticated "
                    "nested submission-boundary publication after outer exec raw-response "
                    "completion with inner submit_proof blocked; hidden validation certifies "
                    "the immutable requested bytes"
                ),
                "agent": {"model": "model-v1", "reasoning_effort": "ultra"},
                "agent_command": command,
                "prompt_provenance": {
                    "effective_prompt": {
                        "sha256": hashlib.sha256(prompt_bytes).hexdigest(),
                        "bytes": len(prompt_bytes),
                    }
                },
                "token_usage": {
                    "root_thread_id": "root-thread",
                    "submission_boundary": {
                        **nested_wire,
                        "request_sha256": request["request_sha256"],
                        "request_published_at_monotonic_ns": release_ns + 600_000_000,
                        "request_published_at_unix_ns": 20_600_000_002,
                        "raw_response_completed_before_boundary_publication": True,
                        "submission_event_order": (
                            "inner_dynamic_call_before_raw_response_completed"
                        ),
                        "dynamic_call_observed_before_raw_response_completed": True,
                        "raw_response_completed_before_dynamic_call_observed": False,
                        "provider_gate_close": {
                            "won": True,
                            "requested_reason": "accepted_submission",
                            "effective_reason": "accepted_submission",
                            "phase": "CLOSED",
                            "sequence": 4,
                        },
                    },
                },
                "ultra_submission_boundary": {"artifacts": {"request": request_descriptor}},
                "protocol": {"verified": {"authenticated_prompt_release": True}},
                "prompt_release": {
                    "schema_version": 1,
                    "protocol_version": "highambench-prompt-release-v1",
                    "required": True,
                    "status": "released_authenticated",
                    "authenticated": True,
                    "timing_exact": True,
                    "useful_work_basis": "authenticated_release",
                    "startup_timeout_seconds": 120.0,
                    "startup_timeout_triggered": False,
                    "go_minimum_release_window_seconds": 5.0,
                    "handshake_nonce": nonce,
                    "elapsed_clock": "CLOCK_MONOTONIC",
                    "artifact_paths": {name: str(path) for name, path in paths.items()},
                    "effective_prompt_sha256": hashlib.sha256(prompt_bytes).hexdigest(),
                    "effective_prompt_bytes": len(prompt_bytes),
                    "ready": ready_descriptor,
                    "go": go_descriptor,
                    "released": release_descriptor,
                    "stale_artifacts_removed": [],
                    "error": None,
                },
            }
            config = {
                "limits": {
                    "prompt_startup_timeout_seconds": 120,
                    "wall_clock_seconds": 100,
                },
                "frozen_environment": {"model_reasoning_effort": "ultra"},
            }
            audit = _rederive_prompt_release_evidence(
                record, config, prompt, repository_root=root
            )
            self.assertTrue(audit["ultra_request_publication_timing_verified"])
            record["token_usage"]["submission_boundary"][
                "request_published_at_monotonic_ns"
            ] += 1
            with self.assertRaisesRegex(ReportError, "publication is unbound"):
                _rederive_prompt_release_evidence(
                    record, config, prompt, repository_root=root
                )

    def test_ultra_boundary_summary_requires_exact_pass_and_failure_outcomes(self) -> None:
        selected = [{"pass": True}, {"pass": False}, {"pass": True}]
        summary = {
            "protocol": "authenticated-submit-proof-v1",
            "selected_ultra_run_count": 3,
            "passing_ultra_run_count": 2,
            "verified_accepted_boundary_count": 2,
            "naturally_drained_failure_count": 1,
            "provider_gate_crossing_failure_count": 0,
            "invalid_or_inexact_outcome_count": 0,
            "retained_artifact_set_count": 2,
            "retained_artifact_file_count": 10,
            "retained_artifacts_reauthenticated": True,
            "pass_drain_complete": False,
            "failure_natural_drain_complete": True,
            "root_active_at_pass_boundary": True,
            "descendants_quiescent_at_pass_boundary": True,
            "later_model_response_possible_after_pass_boundary": False,
            "all_selected_ultra_outcomes_exact": True,
        }
        self.assertEqual(
            _validate_ultra_boundary_summary(
                {"ultra_submission_boundaries": summary}, selected
            ),
            summary,
        )
        resealed_timeout = [
            {"pass": True},
            {"pass": False, "failure_code": "TIME_LIMIT"},
            {"pass": True},
        ]
        with self.assertRaisesRegex(ReportError, "TIME_LIMIT.*exact natural-drain"):
            _validate_ultra_boundary_summary(
                {"ultra_submission_boundaries": summary}, resealed_timeout
            )
        for field, value in (
            ("retained_artifacts_reauthenticated", False),
            ("invalid_or_inexact_outcome_count", 1),
            ("pass_drain_complete", True),
        ):
            with self.subTest(field=field):
                changed = {**summary, field: value}
                with self.assertRaisesRegex(ReportError, "submission-boundary summary"):
                    _validate_ultra_boundary_summary(
                        {"ultra_submission_boundaries": changed}, selected
                    )

    def test_authenticates_signposted_prompt_protocol_and_per_run_summary(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            root = Path(raw)
            common = root / "agent_prompt.md"
            supplement = root / "condition_prompts" / "L.md"
            supplement.parent.mkdir()
            common.write_text("Common instructions.\n", encoding="utf-8")
            supplement.write_text("Neutral library instructions.\n", encoding="utf-8")
            common_descriptor = {
                "path": "agent_prompt.md",
                "sha256": digest_bytes(common.read_bytes()),
                "bytes": common.stat().st_size,
            }
            supplement_descriptor = {
                "path": "condition_prompts/L.md",
                "sha256": digest_bytes(supplement.read_bytes()),
                "bytes": supplement.stat().st_size,
            }
            protocol = {
                "version": "signposted-library-v1",
                "composition_order": [
                    "common_prompt",
                    "condition_L_supplement_if_condition_L",
                    "task_context",
                    "fixed_target",
                ],
                "common_prompt": common_descriptor,
                "condition_supplements": {"L": supplement_descriptor},
                "N_receives_condition_supplement": False,
                "relevant_theorem_or_module_hints_supplied": False,
            }
            inputs = type(
                "PromptInputs",
                (),
                {
                    "benchmark_root": root,
                    "config": {
                        "frozen_environment": {
                            "prompt_sha256": common_descriptor["sha256"],
                            "prompt_protocol": protocol,
                        }
                    },
                    "environment": {"agent": {"prompt_protocol": protocol}},
                    "freeze_check": {"prompt_protocol": protocol},
                    "release_manifest": {
                        "files": [common_descriptor, supplement_descriptor]
                    },
                },
            )()
            summary = {
                "selected_final_record_count": 2,
                "prompt_provenance": {
                    "protocol_version": "signposted-library-v1",
                    "signposted": True,
                    "verified_final_runs": 2,
                    "expected_final_runs": 2,
                    "condition_n_supplement_count": 0,
                    "condition_l_supplement_count": 1,
                    "complete": True,
                },
            }
            self.assertEqual(
                _validated_prompt_protocol(inputs, summary), protocol
            )
            summary["prompt_provenance"]["condition_n_supplement_count"] = 1
            with self.assertRaisesRegex(ReportError, "provenance is incomplete"):
                _validated_prompt_protocol(inputs, summary)

    def test_resolves_authenticated_construction_pointer_and_uses_all_rows(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            inputs = load_report_inputs(fixture.root, fixture.analysis_path)
            self.assertEqual(
                inputs.construction_check.get("kind"),
                "highambench-private-construction-check",
            )
            self.assertEqual(len(inputs.construction_check.get("results", [])), 6)
            latex = render_report(inputs)
            self.assertIn("3 of 3 private library-side proofs compiled", latex)
            self.assertIn("3 of 3 proof dependency records were complete", latex)
            self.assertIn("3 of 3 proofs used NumStability", latex)
            self.assertIn("All 6 private construction proofs", latex)
            self.assertIn(
                "proof-complete private N/L builds are mandatory", latex
            )
            self.assertIn(
                "skeleton-specific check is separate from the mandatory", latex
            )
            self.assertNotIn("T4 instead uses", latex)
            self.assertNotIn("no private gold proof", latex)

    def test_accepts_authenticated_fresh_novelty_override_without_hiding_rejection(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            fixture.activate_fresh_novelty_override()
            latex = render_report(load_report_inputs(fixture.root, fixture.analysis_path))
            self.assertIn("Private measurement exception", latex)
            self.assertIn(r"fail\_exact\_target\_collision", latex)
            self.assertIn("does not approve a public release", latex)
            self.assertIn("P01-T1", latex)

    def test_refuses_tampered_fresh_review_selected_by_override(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            fixture.activate_fresh_novelty_override()
            review_path = (
                fixture.root / "metadata" / "reviews" / "fresh_source.json"
            )
            review_path.write_text(
                review_path.read_text(encoding="utf-8") + "\n", encoding="utf-8"
            )
            with self.assertRaisesRegex(
                ReportError, "private measurement review record 2 changed"
            ):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_reports_partial_duplicate_search_as_partial(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            search_path = (
                fixture.root / "metadata" / "evidence" / "exact_target_search.json"
            )
            search = json.loads(search_path.read_text(encoding="utf-8"))
            search["task_findings"] = search["task_findings"][:2]
            search["fixed_surface_hashes"].pop("P01-T3")
            write_json(search_path, search)
            latex = render_report(load_report_inputs(fixture.root, fixture.analysis_path))
            self.assertIn("cover 2 of 3 tasks", latex)
            self.assertIn("Authenticated duplicate-search evidence for 2 task(s)", latex)

    def test_refuses_tampered_pointer_target_bytes(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            fixture.construction_path.write_text(
                fixture.construction_path.read_text(encoding="utf-8") + "\n",
                encoding="utf-8",
            )
            with self.assertRaisesRegex(
                ReportError, "current library construction evidence changed after it was frozen"
            ):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_authenticated_but_incomplete_l_construction_record(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(
                fixture.construction_path.read_text(encoding="utf-8")
            )
            t3_l = next(
                result
                for result in construction["results"]
                if result["task_id"] == "P01-T3" and result["condition"] == "L"
            )
            t3_l["validation"]["dependency_audit"]["library_use"] = False
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(
                ReportError, "P01-T3/L.*does not record real NumStability library use"
            ):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_failed_l_compile_record(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(
                fixture.construction_path.read_text(encoding="utf-8")
            )
            t1_l = next(
                result
                for result in construction["results"]
                if result["task_id"] == "P01-T1" and result["condition"] == "L"
            )
            t1_l["validation"]["compile_exit_code"] = 1
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(
                ReportError, "P01-T1/L.*incomplete compile or dependency record"
            ):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_incomplete_l_dependency_record(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(
                fixture.construction_path.read_text(encoding="utf-8")
            )
            t2_l = next(
                result
                for result in construction["results"]
                if result["task_id"] == "P01-T2" and result["condition"] == "L"
            )
            t2_l["validation"]["dependency_audit"]["complete"] = False
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(
                ReportError, "P01-T2/L.*incomplete compile or dependency record"
            ):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_unsafe_construction_pointer_path(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            pointer = json.loads(
                fixture.library_pointer_path.read_text(encoding="utf-8")
            )
            pointer["current_evidence"] = "../construction_validation.json"
            write_json(fixture.library_pointer_path, pointer)
            with self.assertRaisesRegex(ReportError, "unsafe file path"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_pointer_target_with_wrong_evidence_kind(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(
                fixture.construction_path.read_text(encoding="utf-8")
            )
            construction["kind"] = "unrelated-evidence"
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(
                ReportError, "not a highambench-private-construction-check"
            ):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_renders_required_sections_and_private_measurement_scope(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            inputs = load_report_inputs(fixture.root, fixture.analysis_path)
            latex = render_report(inputs)
            self.assertIn("Private benchmark measurement", latex)
            self.assertIn("not approved for public release", latex)
            self.assertNotIn("OBSERVATIONAL ONLY", latex)
            self.assertIn("\\section{Why T1, T2, and T3 are present}", latex)
            self.assertIn("\\section{The exact shared Lean setting}", latex)
            self.assertIn("\\section{The two conditions and their isolation}", latex)
            self.assertIn("Every run record", latex)
            self.assertIn("Per-condition results", latex)
            self.assertIn("Per-task results", latex)
            self.assertIn("Failure counts by scope and condition", latex)
            self.assertIn(r"T1 & N & PROOF\_ERROR & 3", latex)
            self.assertIn("Paired changes by tier", latex)
            self.assertIn("Actual library use in condition L", latex)
            self.assertIn("All 6 private construction proofs", latex)
            self.assertIn("Authenticated duplicate-search evidence for 3 task(s)", latex)
            self.assertIn("Hardware and allocation fields enforced across chunks", latex)
            self.assertIn("Fixture CPU", latex)
            self.assertIn("8000000000 bytes (7.5 GiB)", latex)
            self.assertIn("Slurm allocation", latex)
            self.assertIn("one paper", latex.lower())
            self.assertIn("bootstrap", latex.lower())
            self.assertIn("provider connection", latex.lower())
            self.assertIn("loopback provider gate", latex)
            self.assertIn("app-server tree", latex)
            self.assertIn("opaque compaction item", latex)
            self.assertIn("Authenticated live token-control canary", latex)
            self.assertIn("260,000 total model tokens", latex)
            canary_limit = render_report_module.token_canary.DEFAULT_CANARY_TOKEN_LIMIT
            self.assertIn(f"{canary_limit:,}-token outer cap", latex)
            self.assertIn(
                f"{260_000 - canary_limit:,}-token first-crossing overshoot",
                latex,
            )
            self.assertIn("Provider-gate terminal total", latex)
            self.assertIn("Rooted threads", latex)
            self.assertIn("Unique completed responses", latex)
            self.assertIn("Closed provider gate; active tree", latex)
            self.assertIn("Observed token-control canary result", latex)
            self.assertIn("12.500", latex)
            self.assertIn("P01-T3", latex)
            self.assertIn("\\end{document}", latex)

    def test_ultra_report_distinguishes_hook_trust_sources(self) -> None:
        projection = ultra_canary_projection()
        rows = _hook_trust_report_rows(projection)
        self.assertEqual(
            [row[0] for row in rows],
            [
                "Hook-trust CLI flag present",
                "Hook-trust thread config",
                "Effective hook-trust source",
            ],
        )
        self.assertEqual(rows[0][1], True)
        self.assertEqual(rows[1][1], '{"bypass_hook_trust":true}')
        self.assertEqual(rows[2][1], "thread_start_config")
        mutations = {
            "hook_trust_bypass_cli_flag_present": False,
            "hook_trust_bypass_thread_config": {"bypass_hook_trust": False},
            "hook_trust_bypass_effective_source": "cli_flag",
        }
        for field, replacement in mutations.items():
            with self.subTest(field=field):
                tampered = json.loads(json.dumps(projection))
                tampered["fork_policy"][field] = replacement
                with self.assertRaisesRegex(ReportError, "hook-trust split"):
                    _hook_trust_report_rows(tampered)

    def test_refuses_incomplete_analysis(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            analysis = json.loads(fixture.analysis_path.read_text(encoding="utf-8"))
            analysis["result_set_check"]["ok"] = False
            analysis["result_set_check"]["errors"] = ["missing run"]
            write_json(fixture.analysis_path, analysis)
            with self.assertRaisesRegex(ReportError, "incomplete analysis"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_analysis_after_metadata_changes(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            config_path = fixture.root / "metadata" / "config.json"
            config = json.loads(config_path.read_text(encoding="utf-8"))
            config["limits"]["wall_clock_seconds"] = 901
            write_json(config_path, config)
            with self.assertRaisesRegex(ReportError, "stale (analysis|metadata)"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_reproduction_uses_pruned_library_and_no_free_environment_id(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            latex = render_report(load_report_inputs(fixture.root, fixture.analysis_path))
            self.assertNotIn("--environment-id", latex)
            self.assertNotIn("--library-olean .lake/build/lib/lean", latex)
            self.assertIn("--library-olean " + PRUNED_LIBRARY_OLEAN_ROOT, latex)
            self.assertIn("--packages-runtime-root " + PACKAGES_RUNTIME_ROOT, latex)
            self.assertIn("--release-manifest paper_bencmark/highambench/metadata/release_files.json", latex)
            self.assertIn("--agent-network-verified --token-control-verified", latex)
            self.assertIn("rawResponse/completed", latex)
            self.assertIn("crossbindings", latex)
            self.assertIn("sealed provider gate", latex)
            self.assertIn("One sole-inflight response may cross the cap", latex)
            self.assertIn("concurrent in-flight overshoot is false", latex)
            self.assertIn(r"rollout\_budget", latex)
            self.assertIn("remains advisory", latex)

    def test_refuses_rollout_budget_as_enforcing_token_control(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            freeze = json.loads(fixture.freeze_path.read_text(encoding="utf-8"))
            freeze["token_control"]["outer_runner_polling"] = False
            freeze["token_control"]["advisory_rollout_budget"]["role"] = (
                "enforcing"
            )
            write_json(fixture.freeze_path, freeze)
            fixture.refresh_freeze_digest()
            with self.assertRaisesRegex(ReportError, "live token-control evidence"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_canary_descriptor_disagreement(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            environment_path = fixture.root / "metadata" / "environment.json"
            environment = json.loads(environment_path.read_text(encoding="utf-8"))
            environment["token_control_canary"]["status"] = "failed"
            write_json(environment_path, environment)
            fixture.refresh_metadata_and_freeze_digests()
            with self.assertRaisesRegex(ReportError, "descriptor disagrees"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_wrong_canary_evidence_hash(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            for name in ("config.json", "environment.json"):
                path = fixture.root / "metadata" / name
                value = json.loads(path.read_text(encoding="utf-8"))
                descriptor = (
                    value["frozen_environment"]["token_control_canary"]
                    if name == "config.json"
                    else value["token_control_canary"]
                )
                descriptor["sha256"] = "0" * 64
                write_json(path, value)
            fixture.refresh_metadata_and_freeze_digests()
            with self.assertRaisesRegex(ReportError, "canary evidence changed"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_failed_canary_evidence_status(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            evidence = json.loads(fixture.canary_path.read_text(encoding="utf-8"))
            evidence["status"] = "failed"
            write_json(fixture.canary_path, evidence)
            fixture.refreeze_canary_evidence()
            with self.assertRaisesRegex(ReportError, "failed or invalid status"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_canary_freeze_summary_mismatch(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            freeze = json.loads(fixture.freeze_path.read_text(encoding="utf-8"))
            freeze["token_control_canary"]["thread_count"] = 2
            write_json(fixture.freeze_path, freeze)
            fixture.refresh_freeze_digest()
            with self.assertRaisesRegex(ReportError, "invalid token-control canary summary"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_token_canary_endpoint_after_its_exact_crossing(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            freeze = json.loads(fixture.freeze_path.read_text(encoding="utf-8"))
            summary = freeze["token_control_canary"]
            summary["final_endpoint_tokens"] = summary["first_crossing_tokens"] + 1
            write_json(fixture.freeze_path, freeze)
            fixture.refresh_freeze_digest()
            with mock.patch.object(
                render_report_module.token_canary,
                "validate_attestation_document",
                return_value=summary,
            ), self.assertRaisesRegex(
                ReportError, "invalid token-control canary summary"
            ):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_canary_projections_bind_exact_ordered_gate_response_ids(self) -> None:
        for kind, verifier_name in (
            ("token_control_canary", "validate_attestation_document"),
            ("ultra_orchestration_canary", "verify_frozen_attestation"),
        ):
            mutations = (
                ("reordered", "forged")
                if kind == "token_control_canary"
                else ("forged",)
            )
            for mutation in mutations:
                with self.subTest(kind=kind, mutation=mutation), tempfile.TemporaryDirectory() as raw:
                    fixture = ReportFixture(raw)
                    freeze = json.loads(fixture.freeze_path.read_text(encoding="utf-8"))
                    summary = freeze[kind]
                    projection = summary["accounting_projection"]
                    response_ids = list(projection["provider_gate_response_ids"])
                    projection["provider_gate_response_ids"] = (
                        list(reversed(response_ids))
                        if mutation == "reordered"
                        else [*response_ids[:-1], "forged-response-id"]
                    )
                    if "projection_payload_sha256" in projection:
                        projection["projection_payload_sha256"] = document_digest(
                            {
                                key: value
                                for key, value in projection.items()
                                if key != "projection_payload_sha256"
                            }
                        )
                    write_json(fixture.freeze_path, freeze)
                    fixture.refresh_freeze_digest()
                    module = (
                        render_report_module.token_canary
                        if kind == "token_control_canary"
                        else render_report_module.ultra_canary
                    )
                    with mock.patch.object(
                        module,
                        verifier_name,
                        return_value=summary,
                    ), self.assertRaisesRegex(
                        ReportError, "(token-control canary summary|projection-v6)"
                    ):
                        load_report_inputs(fixture.root, fixture.analysis_path)

    def test_token_canary_prompt_release_summary_fails_closed(self) -> None:
        prompt_release = token_canary_prompt_release()
        self.assertTrue(
            render_report_module._valid_token_canary_prompt_release(prompt_release)
        )
        prompt_release["deadline_monotonic_ns"] += 1
        self.assertFalse(
            render_report_module._valid_token_canary_prompt_release(prompt_release)
        )

    def test_refuses_inexact_or_incompletely_drained_ultra_canary(self) -> None:
        for field, replacement in (("measurement_exact", False), ("drain_complete", True)):
            with self.subTest(field=field), tempfile.TemporaryDirectory() as raw:
                fixture = ReportFixture(raw)
                evidence = json.loads(fixture.canary_path.read_text(encoding="utf-8"))
                evidence["outcome"][field] = replacement
                write_json(fixture.canary_path, evidence)
                fixture.refreeze_canary_evidence()
                with self.assertRaisesRegex(
                    ReportError, "exact root-only gate crossing"
                ):
                    load_report_inputs(fixture.root, fixture.analysis_path)

    def test_report_explains_exact_axiom_policy_and_authenticated_setup(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            latex = render_report(load_report_inputs(fixture.root, fixture.analysis_path))
            self.assertIn("does not ban every axiom", latex)
            self.assertIn("task-local helper module", latex)
            self.assertNotIn("Only the normal trusted foundations", latex)
            self.assertIn("Authenticated release, compiled setup, and network evidence", latex)
            self.assertIn("Frozen-run check", latex)
            self.assertIn(r"freeze\_check.json", latex)
            self.assertIn("damaged marker evidence", latex)
            self.assertIn(".olean.server, .olean.private, and .ir support files", latex)
            self.assertIn("The host folders /usr, /bin, /lib*, and /etc", latex)
            self.assertIn("not one fully fingerprinted OCI filesystem", latex)

    def test_refuses_construction_tool_not_authenticated_by_release(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(fixture.construction_path.read_text(encoding="utf-8"))
            construction["verification_basis"]["tools"]["tools/preflight.py"] = "0" * 64
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(ReportError, "preflight.py.*not authenticated"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_wrong_pruned_library_mount(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(fixture.construction_path.read_text(encoding="utf-8"))
            construction["verification_basis"]["numstability_compiled"]["mount_root"] = (
                str((fixture.repo / ".lake" / "build" / "lib" / "lean").resolve())
            )
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(ReportError, "exact pruned library mount"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_stale_pruned_library_identity(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(fixture.construction_path.read_text(encoding="utf-8"))
            construction["verification_basis"]["numstability_compiled"]["sha256"] = (
                "0" * 64
            )
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(ReportError, "stale or incomplete.*compiled"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_stale_pruned_package_identity(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(fixture.construction_path.read_text(encoding="utf-8"))
            construction["verification_basis"]["packages_runtime"]["sha256"] = "0" * 64
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(ReportError, "stale or incomplete.*package"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_construction_python_that_differs_from_frozen_runtime(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(fixture.construction_path.read_text(encoding="utf-8"))
            construction["verification_basis"]["executables"]["python"]["version"] = (
                "different"
            )
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(ReportError, "executable identities"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_n_scan_that_did_not_cover_staged_task(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            construction = json.loads(fixture.construction_path.read_text(encoding="utf-8"))
            n_result = next(
                result for result in construction["results"] if result["condition"] == "N"
            )
            n_result["n_preflight"]["filesystem_scan"]["regular_file_count"] = 0
            write_json(fixture.construction_path, construction)
            fixture.refresh_construction_pointer_digest()
            with self.assertRaisesRegex(ReportError, "complete staged task"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_refuses_tampered_adjacent_freeze_check(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            freeze = json.loads(fixture.freeze_path.read_text(encoding="utf-8"))
            freeze["release_manifest"]["file_count"] += 1
            write_json(fixture.freeze_path, freeze)
            with self.assertRaisesRegex(ReportError, "not linked"):
                load_report_inputs(fixture.root, fixture.analysis_path)

    def test_cli_writes_tex(self) -> None:
        with tempfile.TemporaryDirectory() as raw:
            fixture = ReportFixture(raw)
            status = main(
                [
                    "--benchmark-root",
                    str(fixture.root),
                    "--analysis",
                    str(fixture.analysis_path),
                    "--output-tex",
                    str(fixture.output_tex),
                ]
            )
            self.assertEqual(status, 0)
            self.assertTrue(fixture.output_tex.is_file())
            latex = fixture.output_tex.read_text()
            self.assertIn("Private benchmark measurement", latex)
            self.assertIn("not approved for public release", latex)
    def test_job1509778_interrupted_child_may_have_reactivated_current_turn(
        self,
    ) -> None:
        root_thread_id = "thread-root-1509405"
        child_thread_id = "thread-child-1509405"
        parent_turn_id = "turn-parent-1509405"
        child_turn_id = "turn-child-1509405"
        arguments_sha256 = "a" * 64
        interrupting = {
            "response_id": "resp-interrupt-1509405",
            "call_id": "provider-call-interrupt-1509405",
            "request_metadata": {
                "thread_id": root_thread_id,
                "turn_id": parent_turn_id,
                "request_kind": "turn",
            },
            "admitted_unix_ns": 1_000_000,
            "admitted_monotonic_ns": 1_000_000,
            "commit_unix_ns": 3_000_000,
            "commit_monotonic_ns": 3_000_000,
            "client_release_complete": True,
            "error": None,
            "crossed_cap": False,
            "release_kind": "byte_identity",
            "appserver_crossbind": {
                "thread_id": root_thread_id,
                "turn_id": parent_turn_id,
                "bind_unix_ns": 4_000_000,
                "bind_monotonic_ns": 4_000_000,
            },
            "appserver_delivery": {
                "kind": "direct_raw_response",
                "successor_call_id": None,
                "successor_response_id": None,
                "bind_unix_ns": 4_000_000,
                "bind_monotonic_ns": 4_000_000,
            },
            "response_output_manifest": {
                "output_item_count": 1,
                "action_capable_item_count": 1,
                "items": [
                    {
                        "index": 0,
                        "id": "interrupt-function-item-1509405",
                        "type": "function_call",
                        "name": "interrupt_agent",
                        "namespace": "collaboration",
                        "call_id": "interrupt-call-1509405",
                        "arguments_sha256": arguments_sha256,
                        "arguments_bytes": 56,
                        "wait_timeout_ms": None,
                    }
                ],
            },
        }
        target = {
            "response_id": "resp-child-late-1509405",
            "call_id": "provider-call-child-late-1509405",
            "request_metadata": {
                "thread_id": child_thread_id,
                "turn_id": child_turn_id,
                "request_kind": "turn",
            },
            "admitted_unix_ns": 2_000_000,
            "admitted_monotonic_ns": 2_000_000,
            "commit_unix_ns": 10_000_000,
            "commit_monotonic_ns": 10_000_000,
            "client_release_complete": False,
            "error": None,
            "crossed_cap": False,
            "release_kind": "byte_identity",
            "appserver_crossbind": None,
            "appserver_delivery": {
                "kind": "discarded_after_explicit_child_interrupt",
                "successor_call_id": interrupting["call_id"],
                "successor_response_id": interrupting["response_id"],
                "bind_unix_ns": 11_000_000,
                "bind_monotonic_ns": 11_000_000,
            },
        }
        evidence = {
            "response_id": target["response_id"],
            "provider_call_id": target["call_id"],
            "thread_id": child_thread_id,
            "turn_id": child_turn_id,
            "interrupting_response_id": interrupting["response_id"],
            "interrupting_provider_call_id": interrupting["call_id"],
            "interrupt_function_item_id": "interrupt-function-item-1509405",
            "interrupt_function_call_id": "interrupt-call-1509405",
            "interrupt_function_arguments_sha256": arguments_sha256,
            "interrupt_parent_thread_id": root_thread_id,
            "interrupt_parent_turn_id": parent_turn_id,
            "interrupted_agent_path": "/root/interrupt_delivery_design",
            "interrupt_activity_item_sha256": "b" * 64,
            "interrupt_output_item_id": "interrupt-output-item-1509405",
            "interrupt_output_item_sha256": "c" * 64,
            "interrupt_function_observed_at_unix_ns": 5_000_000,
            "interrupt_function_observed_at_monotonic_ns": 5_000_000,
            "interrupt_activity_observed_at_unix_ns": 6_000_000,
            "interrupt_activity_observed_at_monotonic_ns": 6_000_000,
            "interrupt_output_observed_at_unix_ns": 7_000_000,
            "interrupt_output_observed_at_monotonic_ns": 7_000_000,
            "interrupted_turn_observed_at_unix_ns": 8_000_000,
            "interrupted_turn_observed_at_monotonic_ns": 8_000_000,
        }
        threads = [
            {
                "thread_id": root_thread_id,
                "parent_thread_id": None,
                "agent_path": "root",
                "provisional": False,
                "spawn_binding_status": "root_zero",
                "turn_status": "completed",
                "turn_seen": True,
                "active_turn_id": None,
            },
            {
                "thread_id": child_thread_id,
                "parent_thread_id": root_thread_id,
                "agent_path": "/root/interrupt_delivery_design",
                "provisional": False,
                "spawn_binding_status": "resolved",
                "turn_status": "inProgress",
                "turn_seen": True,
                "active_turn_id": "child-followup-turn-1509778",
            },
        ]
        self.assertEqual(
            set(evidence),
            set(
                render_report_module.codex_isolated.DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_EVIDENCE_KEYS
            ),
        )
        render_report_module._validate_explicit_child_interrupt_discard(
            evidence_value=evidence,
            target=target,
            interrupting=interrupting,
            thread_accounting=threads,
            root_thread_id=root_thread_id,
            label="job1509405 fixture",
        )
        render_report_module._validate_projected_explicit_child_interrupt_evidence(
            evidence_value=evidence,
            discarded_response_id=target["response_id"],
            interrupting=interrupting,
            thread_accounting=threads,
            root_thread_id=root_thread_id,
            label="job1509778 projected fixture",
        )

        wrong_path = json.loads(json.dumps(evidence))
        wrong_path["interrupted_agent_path"] = "/root/wrong-child"
        with self.assertRaisesRegex(ReportError, "direct interrupted child"):
            render_report_module._validate_explicit_child_interrupt_discard(
                evidence_value=wrong_path,
                target=target,
                interrupting=interrupting,
                thread_accounting=threads,
                root_thread_id=root_thread_id,
                label="job1509778 wrong path",
            )
        with self.assertRaisesRegex(ReportError, "parent-child tree"):
            render_report_module._validate_projected_explicit_child_interrupt_evidence(
                evidence_value=wrong_path,
                discarded_response_id=target["response_id"],
                interrupting=interrupting,
                thread_accounting=threads,
                root_thread_id=root_thread_id,
                label="job1509778 projected wrong path",
            )

        tampered = json.loads(json.dumps(evidence))
        tampered["interrupt_function_arguments_sha256"] = "d" * 64
        with self.assertRaisesRegex(ReportError, "interrupt_agent manifest"):
            render_report_module._validate_explicit_child_interrupt_discard(
                evidence_value=tampered,
                target=target,
                interrupting=interrupting,
                thread_accounting=threads,
                root_thread_id=root_thread_id,
                label="job1509405 tamper",
            )

        late_target = json.loads(json.dumps(target))
        late_target["admitted_unix_ns"] = evidence[
            "interrupt_function_observed_at_unix_ns"
        ]
        with self.assertRaisesRegex(ReportError, "timing"):
            render_report_module._validate_explicit_child_interrupt_discard(
                evidence_value=evidence,
                target=late_target,
                interrupting=interrupting,
                thread_accounting=threads,
                root_thread_id=root_thread_id,
                label="job1509703 late child admission",
            )


if __name__ == "__main__":
    unittest.main()
