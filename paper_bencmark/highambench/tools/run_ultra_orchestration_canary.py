#!/usr/bin/env python3
"""Run or independently verify the non-scored Ultra submission canary.

The scored HighamBench tasks are deliberately not used here.  The canary sends
one small synthetic ``True`` theorem through the production ``runner.py`` and
``codex_isolated.py`` path.  It requires both a positive-usage descendant and
an authenticated, runner-validated ``submit_proof`` boundary.  Its token ceiling
is the full frozen benchmark ceiling, rather than a low stop threshold, so the
coordinator can delegate before the root submits its immutable candidate.

No provider call is made by ``--verify-only``.  That mode authenticates every
frozen artifact and replays the app-server audit log through the same
``AttemptUsageLedger`` used by live attempts, then rebinds the retained
challenge/call/request/ack/snapshot chain to the accepted boundary.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import stat
import subprocess
import sys
import tempfile
from typing import Any, Iterable, Mapping, Sequence

try:
    from .common import BenchmarkToolError, read_json, sha256_file, write_json
    from .hashes import create_manifest, load_manifest, verify_manifest
    from . import codex_isolated
    from . import runner
except ImportError:  # Direct script execution.
    from common import BenchmarkToolError, read_json, sha256_file, write_json  # type: ignore
    from hashes import create_manifest, load_manifest, verify_manifest  # type: ignore
    import codex_isolated  # type: ignore
    import runner  # type: ignore


CANARY_ID = "ULTRA-ORCHESTRATION-SUBMISSION-CANARY-V12"
EVIDENCE_KIND = "highambench-live-ultra-orchestration-canary"
FROZEN_EVIDENCE_PATH = (
    "paper_bencmark/highambench/metadata/evidence/"
    "ultra_orchestration_live_canary.json"
)
PROMPT_PROTOCOL = (
    "synthetic-root-and-child-fork3-denial-fork-all-nested-submit-proof-v12"
)
DEFAULT_CANARY_TIME_LIMIT_SECONDS = 300
ACCOUNTING_PROJECTION_SCHEMA_VERSION = runner.ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION
SPAWN_BINDING_SOURCE = "raw_function_call.call_id=subAgentActivity.id"
_TOKEN_FIELDS = (
    "input_tokens",
    "cached_input_tokens",
    "cache_write_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
    "total_tokens",
)
_VALIDATION_AUTHENTICATION_FIELDS = {
    "schema_version",
    "run_id",
    "task_id",
    "candidate_sha256",
    "target_theorem",
    "controlled_manifest_sha256",
    "validator_contract_sha256",
    "submission_request_sha256",
    "submission_sequence",
}
_FORK_POLICY_FIELDS = {
    "schema_version",
    "enforcement",
    "hook_notification",
    "hook_event_name",
    "matcher",
    "source",
    "source_path",
    "execution_mode",
    "handler_type",
    "scope",
    "display_order",
    "command",
    "helper_filename",
    "helper_sha256",
    "hooks_json_sha256",
    "block_reason_template",
    "usage_hint",
    "usage_hint_sha256",
    "hook_trust_bypass_cli_flag_present",
    "hook_trust_bypass_thread_config",
    "hook_trust_bypass_effective_source",
    "allowed_fork_turns",
    "positive_integer_fork_turns_allowed",
    "call_evidence",
    "complete",
}
_FORK_POLICY_CALL_FIELDS = {
    "call_id",
    "parent_thread_id",
    "parent_turn_id",
    "parent_response_id",
    "fork_turns",
    "fork_semantics",
    "hook_run_id",
    "hook_source_path",
    "hook_thread_id",
    "hook_turn_id",
    "hook_started_observed",
    "hook_started_count",
    "hook_completed_observed",
    "hook_completed_count",
    "hook_status",
    "decision",
    "feedback",
    "resolution_status",
    "child_activity_observed",
}
ARTIFACT_LABELS = (
    "agent_log",
    "usage",
    "freeze_check",
    "runner_freeze_check",
    "invocation",
    "common_prompt",
    "context",
    "synthetic_target",
    "controlled_manifest",
    "dependency_audit_helper",
    "runner_record",
    "raw_jsonl",
    "validation",
    "accepted_candidate",
    "barrier_challenge",
    "barrier_call",
    "barrier_request",
    "barrier_ack",
    "barrier_snapshot",
    "provider_gate",
)
PRODUCTION_EXECUTION_COMPONENT_FIELDS = (
    "filesystem_adapter_sha256",
    "provider_token_gate_sha256",
    "lean_adapter_sha256",
    "offline_shell_source_sha256",
    "runner_sha256",
    "validator_sha256",
    "dependency_audit_sha256",
    "offline_shell_binary_sha256",
)

# These strings are code constants on purpose.  They are hashed into the
# attestation, and the tool itself is authenticated by the release manifest.
# No benchmark task statement, context, target, or shared source is reused or
# changed by this probe.
SYNTHETIC_COMMON_PROMPT = """# Private synthetic Ultra orchestration canary

This is an unscored infrastructure probe, not a benchmark task.

Your first task action MUST be exactly one `exec_command` call that runs `pwd`.
Wait for that tool result so the root has completed one model response. Then,
in the next model response, deliberately make exactly one `spawn_agent` call
with `fork_turns="3"`. Assign the attempted child only the bounded task of
returning `HIGHAMBENCH_FORBIDDEN_ROOT_CHILD`. The frozen policy hook must deny
this call. Treat that denial as the expected canary result, and do not retry the
positive-integer fork.

After the denial, in a separate model response make exactly one `spawn_agent`
call with `fork_turns="all"`. Assign that child only this bounded task: first
deliberately make exactly one `spawn_agent` call with `fork_turns="3"`, asking
the attempted grandchild only to return `HIGHAMBENCH_FORBIDDEN_GRANDCHILD`;
require the policy hook to deny that call; then return the exact text
`HIGHAMBENCH_ULTRA_CHILD_OK` and do nothing else. Do not answer the allowed
child task yourself and do not intentionally spawn any other child. Wait until
the allowed child is terminal and collect its result.

Then create `Candidate.lean` in the workspace root by copying the fixed target
statement exactly and retaining its valid `True` proof. Run `lean Candidate.lean`
and require success. Never create, modify, rename, or copy to `Submission.lean`.
In a separate final model response, make exactly one model tool call: code-mode
`exec` with this exact raw two-line source, including the final newline:
```javascript
// @exec: {"yield_time_ms": 2400000}
await tools.submit_proof({candidate_path:"Candidate.lean"});
```
That program must make exactly one nested `submit_proof` call with
`candidate_path="Candidate.lean"`. The yield pragma is transport-only and does
not extend the measured deadline. Do not make any other tool call or action in
that response, and do not answer after acceptance.

If delegation, Lean checking, or submission is unavailable, do not imitate it
or claim success; report the failure plainly."""

SYNTHETIC_CONTEXT = """There is no paper, score, or matrix assignment. The
fixed theorem is deliberately trivial. Success is determined only from trusted
delegation evidence and the authenticated runner-owned submission boundary."""

SYNTHETIC_TARGET = """theorem highamBenchUltraCanary : True := by
  -- PROOF_START
  trivial
"""
SYNTHETIC_TARGET_THEOREM = "highamBenchUltraCanary"


def _mapping(value: Any, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise BenchmarkToolError(f"{label} must be a JSON object")
    return value


def _nonnegative_int(value: Any, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise BenchmarkToolError(f"Ultra orchestration canary has invalid {label}")
    return value


def _positive_int(value: Any, label: str) -> int:
    result = _nonnegative_int(value, label)
    if result == 0:
        raise BenchmarkToolError(f"Ultra orchestration canary has nonpositive {label}")
    return result


def _validated_nested_submit_yield_contract(
    value: Mapping[str, Any], *, label: str
) -> dict[str, Any]:
    """Authenticate and independently rederive the schema-v5 anti-yield envelope."""

    expected = codex_isolated.nested_submission_exec_yield_record()
    if any(value.get(field) != wanted for field, wanted in expected.items()):
        raise BenchmarkToolError(f"{label} has an inexact nested-exec yield contract")
    wall_seconds = value.get("outer_exec_yield_attempt_wall_seconds")
    reserve_seconds = value.get(
        "outer_exec_yield_post_submission_validation_reserve_seconds"
    )
    envelope_ms = value.get("outer_exec_yield_envelope_ms")
    yield_ms = value.get("outer_exec_yield_time_ms")
    margin_ms = value.get("outer_exec_yield_margin_ms")
    if (
        type(wall_seconds) is not int
        or type(reserve_seconds) is not int
        or type(envelope_ms) is not int
        or type(yield_ms) is not int
        or type(margin_ms) is not int
        or envelope_ms != 1_000 * (wall_seconds + reserve_seconds)
        or margin_ms != yield_ms - envelope_ms
        or margin_ms <= 0
        or yield_ms <= envelope_ms
        or value.get("outer_exec_timer_starts_at_or_after_prompt_release") is not True
        or value.get("outer_exec_yield_exceeds_envelope") is not True
    ):
        raise BenchmarkToolError(f"{label} has an invalid nested-exec yield envelope")
    return dict(expected)


def _canonical_sha256(value: Mapping[str, Any]) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _text_sha256(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def synthetic_effective_prompt() -> str:
    """Return the exact text assembled by ``codex_isolated.build_prompt``."""

    return "\n\n".join(
        (
            SYNTHETIC_COMMON_PROMPT.rstrip(),
            "## Task context\n\n" + SYNTHETIC_CONTEXT.rstrip(),
            "## Fixed Lean target\n\n```lean\n"
            + SYNTHETIC_TARGET.rstrip()
            + "\n```",
        )
    ) + "\n"


def prompt_record() -> dict[str, Any]:
    return {
        "protocol": PROMPT_PROTOCOL,
        "composition": (
            "common_prompt_then_task_context_then_synthetic_target_via_"
            "codex_isolated_build_prompt"
        ),
        "common_prompt_sha256": _text_sha256(SYNTHETIC_COMMON_PROMPT),
        "context_sha256": _text_sha256(SYNTHETIC_CONTEXT),
        "synthetic_target_sha256": _text_sha256(SYNTHETIC_TARGET),
        "effective_prompt_sha256": _text_sha256(synthetic_effective_prompt()),
    }


def _json_messages(path: Path) -> list[dict[str, Any]]:
    messages: list[dict[str, Any]] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        raise BenchmarkToolError(
            f"cannot read Ultra orchestration canary audit log: {error}"
        ) from error
    for line in lines:
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            messages.append(value)
    return messages


_STABLE_LEDGER_FIELDS = (
    "schema_version",
    "measurement_source",
    "notification",
    "usage_scope",
    "live_cumulative",
    "input_includes_cached",
    "root_thread_id",
    "root_turn_id",
    "thread_count",
    "response_count",
    "input_tokens",
    "cached_input_tokens",
    "cache_write_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
    "total_tokens",
    "notification_sequence",
    "first_crossing",
    "stop_reason",
    "interrupt_requested",
    "pending_interrupt_response_count",
    "active_thread_ids",
    "unresolved_thread_ids",
    "drain_complete",
    "measurement_exact",
    "invalid_reasons",
    "threads",
    "response_ids",
    "submission_boundary",
    "accounting_projection_schema_version",
    "spawn_binding_source",
    "raw_spawn_call_ids",
    "activity_spawn_call_ids",
    "collab_spawn_call_ids",
    "resolved_spawn_call_ids",
    "failed_spawn_call_ids",
    "policy_blocked_spawn_call_ids",
    "unresolved_spawn_call_ids",
    "unsupported_spawn_call_ids",
    "inference_child_thread_ids",
    "hook_observed_spawn_call_ids",
    "hook_allowed_spawn_call_ids",
    "hook_blocked_spawn_call_ids",
    "hook_invalid_spawn_call_ids",
    "spawn_linkage_complete",
    "descendant_accounting_complete",
    "cumulative_projection_complete",
    "fork_policy_complete",
    "accounting_complete",
    "fork_policy",
)


def replay_ledger(
    agent_log: Path,
    *,
    root_thread_id: str,
    token_limit: int,
    submission_boundary: Mapping[str, Any],
) -> dict[str, Any]:
    """Replay provider events, then bind the authenticated accepted boundary."""

    with tempfile.TemporaryDirectory(prefix="highambench-canary-replay-") as raw:
        ledger = codex_isolated.AttemptUsageLedger(
            Path(raw) / "usage.json",
            token_limit,
            root_thread_id,
            fork_policy=codex_isolated.ultra_fork_policy_static_record(),
        )
        boundary_response_id = submission_boundary.get("response_id")
        if not isinstance(boundary_response_id, str) or not boundary_response_id:
            raise BenchmarkToolError(
                "Ultra orchestration canary boundary lacks a response id"
            )
        boundary_response_seen = False
        boundary_inner_call_seen = False
        for message in _json_messages(agent_log):
            method = message.get("method")
            params = message.get("params")
            if boundary_response_seen and boundary_inner_call_seen:
                if (
                    method == codex_isolated.ULTRA_USAGE_NOTIFICATION
                    and isinstance(params, Mapping)
                    and params.get("responseId") == boundary_response_id
                ):
                    # Exact duplicate delivery is not later inference activity;
                    # AttemptUsageLedger authenticates and deduplicates it.
                    ledger.observe(message)
                    continue
                if method == "thread/tokenUsage/updated":
                    if (
                        not isinstance(params, Mapping)
                        or params.get("threadId") != root_thread_id
                    ):
                        raise BenchmarkToolError(
                            "Ultra orchestration canary observed post-boundary child activity"
                        )
                    ledger.observe(message)
                    continue
                if (
                    method == "thread/status/changed"
                    and isinstance(params, Mapping)
                    and params.get("threadId") == root_thread_id
                    and isinstance(params.get("status"), Mapping)
                    and params["status"].get("type")
                    in ("idle", "shutdown", "notLoaded")
                ):
                    # App-server may emit a root shutdown status after the adapter
                    # has published and killed the accepted blocked boundary.  It
                    # is operational teardown, not post-boundary model activity,
                    # and therefore must not mutate the replayed boundary ledger.
                    continue
                if method is not None:
                    raise BenchmarkToolError(
                        "Ultra orchestration canary observed post-boundary model activity"
                    )
                continue
            if method == "item/tool/call":
                # SubmissionBarrier consumes this dynamic request before the
                # usage ledger sees it. Authenticate that same request below.
                if (
                    message.get("id") != submission_boundary.get("jsonrpc_request_id")
                    or not isinstance(params, Mapping)
                    or params.get("tool") != codex_isolated.SUBMISSION_TOOL_NAME
                    or params.get("threadId") != submission_boundary.get("thread_id")
                    or params.get("turnId") != submission_boundary.get("turn_id")
                    or params.get("callId") != submission_boundary.get("call_id")
                    or params.get("arguments") != {"candidate_path": "Candidate.lean"}
                ):
                    raise BenchmarkToolError(
                        "Ultra orchestration canary log has an unauthenticated dynamic call"
                    )
                if boundary_inner_call_seen:
                    raise BenchmarkToolError(
                        "Ultra orchestration canary log repeats its dynamic call"
                    )
                boundary_inner_call_seen = True
                continue
            if boundary_response_seen and not boundary_inner_call_seen:
                item = params.get("item") if isinstance(params, Mapping) else None
                if not (
                    method == "item/started"
                    and isinstance(item, Mapping)
                    and item.get("type") == "dynamicToolCall"
                    and item.get("id") == submission_boundary.get("call_id")
                ):
                    raise BenchmarkToolError(
                        "Ultra orchestration canary observed unrelated activity between "
                        "the raw response and its delayed inner dynamic call"
                    )
            if ledger.observe_interrupt_response(message):
                continue
            ledger.observe(message)
            if (
                method == codex_isolated.ULTRA_USAGE_NOTIFICATION
                and isinstance(params, Mapping)
                and params.get("responseId") == boundary_response_id
            ):
                boundary_response_seen = True
        if not boundary_response_seen or not boundary_inner_call_seen:
            raise BenchmarkToolError(
                "Ultra orchestration canary log lacks the submission response/call pair"
            )
        wire_fields = (
            "submission_transport",
            "outer_raw_item_id",
            "outer_raw_item_type",
            "outer_exec_name",
            "outer_exec_call_id",
            "outer_exec_program",
            "outer_exec_program_bytes",
            "outer_exec_program_sha256",
            "outer_exec_yield_time_ms",
            "outer_exec_yield_envelope_basis",
            "outer_exec_yield_attempt_wall_seconds",
            "outer_exec_yield_post_submission_validation_reserve_seconds",
            "outer_exec_yield_envelope_ms",
            "outer_exec_yield_margin_ms",
            "outer_exec_timer_starts_at_or_after_prompt_release",
            "outer_exec_yield_exceeds_envelope",
            "outer_raw_item_observed_at_monotonic_ns",
            "inner_dynamic_item_started_at_monotonic_ns",
            "outer_raw_item_observed_before_inner_dynamic_call",
        )
        expected_wire = {
            field: submission_boundary.get(field) for field in wire_fields
        }
        outer_observation = ledger.raw_item_observations.get(
            str(submission_boundary.get("outer_raw_item_id", ""))
        )
        inner_observation = ledger.dynamic_tool_starts.get(
            str(submission_boundary.get("call_id", ""))
        )
        if not isinstance(outer_observation, Mapping) or not isinstance(
            inner_observation, Mapping
        ):
            raise BenchmarkToolError(
                "Ultra orchestration canary replay lacks outer/inner observations"
            )
        expected_wire["outer_raw_item_observed_at_monotonic_ns"] = (
            outer_observation.get("observed_at_monotonic_ns")
        )
        expected_wire["inner_dynamic_item_started_at_monotonic_ns"] = (
            inner_observation.get("observed_at_monotonic_ns")
        )
        match = ledger.matching_submit_response(
            turn_id=str(submission_boundary.get("turn_id", "")),
            call_id=str(submission_boundary.get("call_id", "")),
            candidate_path="Candidate.lean",
            expected_wire=expected_wire,
        )
        if match is None:
            raise BenchmarkToolError(
                "Ultra orchestration canary replay did not bind the outer custom "
                "exec to the same completed raw response as the inner submission"
            )
        response_id, _response, wire = match
        stable_wire_fields = tuple(
            field
            for field in wire_fields
            if field
            not in (
                "outer_raw_item_observed_at_monotonic_ns",
                "inner_dynamic_item_started_at_monotonic_ns",
            )
        )
        if response_id != boundary_response_id or any(
            submission_boundary.get(field) != wire.get(field)
            for field in stable_wire_fields
        ):
            raise BenchmarkToolError(
                "Ultra orchestration canary replay changed its nested submission wire"
            )
        ledger.accept_submission_boundary(submission_boundary)
        return ledger.snapshot(drain_complete=False)


def _validated_submission_event_order(
    value: Mapping[str, Any], *, label: str, derive_from_timestamps: bool
) -> str:
    """Return the unique schema-v5 order after independently validating it."""

    dynamic_before = value.get(
        "dynamic_call_observed_before_raw_response_completed"
    )
    response_before = value.get(
        "raw_response_completed_before_dynamic_call_observed"
    )
    order = value.get("submission_event_order")
    if (dynamic_before, response_before) == (True, False):
        expected = codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
    elif (dynamic_before, response_before) == (False, True):
        expected = codex_isolated.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER
    else:
        raise BenchmarkToolError(
            f"{label} does not attest exactly one submission event order"
        )
    if order != expected:
        raise BenchmarkToolError(f"{label} submission event-order enum is inconsistent")
    if value.get("raw_response_completed_before_boundary_publication") is not True:
        raise BenchmarkToolError(
            f"{label} does not precede publication with raw-response completion"
        )
    if derive_from_timestamps:
        captured_ns = value.get("captured_at_monotonic_ns")
        response_ns = value.get("raw_response_observed_at_monotonic_ns")
        published_ns = value.get("request_published_at_monotonic_ns")
        if any(
            type(item) is not int or item <= 0
            for item in (captured_ns, response_ns, published_ns)
        ):
            raise BenchmarkToolError(f"{label} event-order timestamps are malformed")
        assert isinstance(captured_ns, int)
        assert isinstance(response_ns, int)
        assert isinstance(published_ns, int)
        if (
            captured_ns == response_ns
            or dynamic_before is not (captured_ns < response_ns)
            or response_ns > published_ns
            or captured_ns > published_ns
        ):
            raise BenchmarkToolError(
                f"{label} event-order timestamps contradict its attestation"
            )
    return str(order)


def _audit_nested_submission_wire(
    agent_log: Path, submission_boundary: Mapping[str, Any]
) -> dict[str, Any]:
    """Authenticate outer exec -> inner dynamic call -> same raw response."""

    matching_outer_indexes: list[int] = []
    matching_started_indexes: list[int] = []
    matching_inner_indexes: list[int] = []
    matching_response_indexes: list[int] = []
    for index, message in enumerate(_json_messages(agent_log)):
        method = message.get("method")
        params = message.get("params")
        item = params.get("item") if isinstance(params, Mapping) else None
        if method == "rawResponseItem/completed" and isinstance(item, Mapping):
            if (
                params.get("threadId") == submission_boundary.get("thread_id")
                and params.get("turnId") == submission_boundary.get("turn_id")
                and item.get("id") == submission_boundary.get("outer_raw_item_id")
                and item.get("type") == "custom_tool_call"
                and item.get("name") == "exec"
                and item.get("status") == "completed"
                and item.get("call_id")
                == submission_boundary.get("outer_exec_call_id")
                and item.get("input")
                == submission_boundary.get("outer_exec_program")
                and codex_isolated.is_canonical_nested_submit_exec_input(
                    item.get("input"), candidate_path="Candidate.lean"
                )
            ):
                matching_outer_indexes.append(index)
        elif (
            method == "item/started"
            and isinstance(params, Mapping)
            and isinstance(item, Mapping)
        ):
            if (
                params.get("threadId") == submission_boundary.get("thread_id")
                and params.get("turnId") == submission_boundary.get("turn_id")
                and item.get("type") == "dynamicToolCall"
                and item.get("id") == submission_boundary.get("call_id")
                and item.get("tool") == codex_isolated.SUBMISSION_TOOL_NAME
                and item.get("namespace") in (None, "")
                and item.get("status") == "inProgress"
                and item.get("arguments") == {"candidate_path": "Candidate.lean"}
            ):
                matching_started_indexes.append(index)
        elif method == "item/tool/call" and isinstance(params, Mapping):
            if (
                message.get("id") == submission_boundary.get("jsonrpc_request_id")
                and params.get("tool") == codex_isolated.SUBMISSION_TOOL_NAME
                and params.get("namespace") in (None, "")
                and params.get("threadId") == submission_boundary.get("thread_id")
                and params.get("turnId") == submission_boundary.get("turn_id")
                and params.get("callId") == submission_boundary.get("call_id")
                and params.get("arguments") == {"candidate_path": "Candidate.lean"}
            ):
                matching_inner_indexes.append(index)
        elif (
            method == codex_isolated.ULTRA_USAGE_NOTIFICATION
            and isinstance(params, Mapping)
            and params.get("responseId") == submission_boundary.get("response_id")
            and params.get("threadId") == submission_boundary.get("thread_id")
            and params.get("turnId") == submission_boundary.get("turn_id")
        ):
            matching_response_indexes.append(index)
    if (
        len(matching_outer_indexes) != 1
        or len(matching_started_indexes) != 1
        or len(matching_inner_indexes) != 1
        or not matching_response_indexes
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary log lacks one exact outer-exec/inner-call/"
            "raw-response chain"
        )
    outer_index = matching_outer_indexes[0]
    started_index = matching_started_indexes[0]
    inner_index = matching_inner_indexes[0]
    response_index = min(matching_response_indexes)
    event_order = _validated_submission_event_order(
        submission_boundary,
        label="Ultra orchestration canary boundary",
        derive_from_timestamps=False,
    )
    if event_order == codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE:
        event_indexes_valid = (
            outer_index < started_index < inner_index < response_index
        )
    else:
        event_indexes_valid = (
            outer_index < response_index < started_index < inner_index
        )
    if not event_indexes_valid:
        raise BenchmarkToolError(
            "Ultra orchestration canary nested submission events are out of order"
        )
    outer_call_id = submission_boundary.get("outer_exec_call_id")
    outer_raw_item_id = submission_boundary.get("outer_raw_item_id")
    inner_call_id = submission_boundary.get("call_id")
    if (
        not isinstance(outer_call_id, str)
        or not outer_call_id
        or not isinstance(outer_raw_item_id, str)
        or not outer_raw_item_id
        or not isinstance(inner_call_id, str)
        or not inner_call_id
        or len({outer_raw_item_id, outer_call_id, inner_call_id}) != 3
        or submission_boundary.get("inner_dynamic_call_id") != inner_call_id
        or submission_boundary.get("inner_dynamic_tool_name") != "submit_proof"
        or submission_boundary.get("inner_dynamic_arguments")
        != {"candidate_path": "Candidate.lean"}
        or submission_boundary.get("submission_transport")
        != codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT
        or submission_boundary.get("outer_raw_item_type") != "custom_tool_call"
        or submission_boundary.get("outer_exec_name") != "exec"
        or submission_boundary.get("outer_exec_program")
        != codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE
        or submission_boundary.get("outer_exec_program_bytes")
        != codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_BYTES
        or submission_boundary.get("outer_exec_program_sha256")
        != codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_SHA256
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary nested submission identities are inexact"
        )
    yield_contract = _validated_nested_submit_yield_contract(
        submission_boundary,
        label="Ultra orchestration canary nested submission",
    )
    outer_ns = submission_boundary.get(
        "outer_raw_item_observed_at_monotonic_ns"
    )
    inner_ns = submission_boundary.get(
        "inner_dynamic_item_started_at_monotonic_ns"
    )
    if (
        type(outer_ns) is not int
        or type(inner_ns) is not int
        or not 0 < outer_ns <= inner_ns
        or submission_boundary.get(
            "outer_raw_item_observed_before_inner_dynamic_call"
        )
        is not True
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary nested submission timing is inconsistent"
        )
    return {
        "submission_transport": codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT,
        "outer_raw_item_type": "custom_tool_call",
        "outer_exec_name": "exec",
        "outer_exec_program_bytes": (
            codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_BYTES
        ),
        "outer_exec_program_sha256": (
            codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_SHA256
        ),
        **yield_contract,
        "outer_raw_item_and_call_ids_pairwise_distinct": True,
        "outer_raw_item_observed_before_inner_dynamic_call": True,
        "inner_dynamic_item_started_observed": True,
        "inner_dynamic_item_started_before_jsonrpc_call": True,
        "submission_event_order": event_order,
        "dynamic_call_observed_before_raw_response_completed": (
            event_order
            == codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
        ),
        "raw_response_completed_before_dynamic_call_observed": (
            event_order
            == codex_isolated.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER
        ),
        "same_outer_raw_response_authenticated": True,
        "same_thread_and_turn": True,
        "replayed_from_agent_log": True,
    }


def _audit_fork_policy(
    policy_value: Any,
    *,
    raw_calls: Mapping[str, Mapping[str, Any]],
    activities: Mapping[str, Mapping[str, Any]],
    collab_ids: set[str],
    responses: Sequence[Mapping[str, Any]],
    root_thread_id: str,
) -> dict[str, Any]:
    """Authenticate one hook decision for every raw synthetic spawn call."""

    policy = _mapping(policy_value, "Ultra orchestration canary fork policy")
    if set(policy) != _FORK_POLICY_FIELDS:
        raise BenchmarkToolError(
            "Ultra orchestration canary fork-policy fields are not exact"
        )
    expected_static = codex_isolated.ultra_fork_policy_static_record()
    static = dict(policy)
    static.pop("call_evidence")
    static.pop("complete")
    if static != expected_static or policy.get("complete") is not True:
        raise BenchmarkToolError(
            "Ultra orchestration canary fork-policy freeze is inconsistent"
        )
    reason_template = codex_isolated.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE

    raw_evidence = policy.get("call_evidence")
    if not isinstance(raw_evidence, list):
        raise BenchmarkToolError(
            "Ultra orchestration canary fork policy lacks call evidence"
        )
    evidence_by_id: dict[str, Mapping[str, Any]] = {}
    for index, raw in enumerate(raw_evidence):
        evidence = _mapping(raw, f"Ultra canary fork-policy call {index}")
        call_id = evidence.get("call_id")
        if (
            set(evidence) != _FORK_POLICY_CALL_FIELDS
            or not isinstance(call_id, str)
            or not call_id
            or call_id in evidence_by_id
        ):
            raise BenchmarkToolError(
                "Ultra orchestration canary fork-policy call evidence is malformed"
            )
        evidence_by_id[call_id] = evidence
    if list(evidence_by_id) != sorted(evidence_by_id) or set(evidence_by_id) != set(
        raw_calls
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary fork-policy call evidence is not canonical"
        )

    blocked_ids: set[str] = set()
    allowed_ids: set[str] = set()
    blocked_parents: set[str] = set()
    response_positions: dict[str, int] = {}
    for call_id, raw_call in raw_calls.items():
        containing = [
            response
            for response in responses
            if response["index"] > raw_call["index"]
            and response["thread_id"] == raw_call["parent_thread_id"]
            and response["turn_id"] == raw_call["parent_turn_id"]
        ]
        if not containing:
            raise BenchmarkToolError(
                "Ultra orchestration canary raw spawn lacks its completed response"
            )
        response = containing[0]
        response_positions[call_id] = int(response["index"])
        evidence = evidence_by_id[call_id]
        fork_turns = raw_call["fork_turns"]
        child_observed = call_id in activities
        common_ok = (
            evidence.get("parent_thread_id") == raw_call["parent_thread_id"]
            and evidence.get("parent_turn_id") == raw_call["parent_turn_id"]
            and evidence.get("parent_response_id") == response["response_id"]
            and evidence.get("fork_turns") == fork_turns
            and isinstance(evidence.get("fork_semantics"), str)
            and bool(evidence.get("fork_semantics"))
            and evidence.get("hook_run_id")
            == (
                f"pre-tool-use:{policy['display_order']}:"
                f"{policy['source_path']}:{call_id}"
            )
            and evidence.get("hook_source_path") == policy.get("source_path")
            and evidence.get("hook_thread_id") == raw_call["parent_thread_id"]
            and evidence.get("hook_turn_id") == raw_call["parent_turn_id"]
            and evidence.get("hook_started_observed") is True
            and evidence.get("hook_started_count") == 1
            and evidence.get("hook_completed_observed") is True
            and evidence.get("hook_completed_count") == 1
            and evidence.get("child_activity_observed") is child_observed
        )
        if not common_ok:
            raise BenchmarkToolError(
                "Ultra orchestration canary fork-policy call binding is inexact"
            )
        if fork_turns == "all":
            allowed_ids.add(call_id)
            if (
                evidence.get("fork_semantics") != "full_history_parent_pre_response"
                or evidence.get("hook_status")
                != codex_isolated.ULTRA_FORK_POLICY_ALLOW_STATUS
                or evidence.get("decision")
                != codex_isolated.ULTRA_FORK_POLICY_ALLOW_DECISION
                or evidence.get("feedback") not in (None, "")
                or evidence.get("resolution_status") != "resolved_child"
                or not child_observed
            ):
                raise BenchmarkToolError(
                    "Ultra orchestration canary allowed fork-policy decision is invalid"
                )
        else:
            blocked_ids.add(call_id)
            blocked_parents.add(str(raw_call["parent_thread_id"]))
            if (
                fork_turns != "3"
                or evidence.get("fork_semantics")
                != "unsupported_positive_turn_suffix"
                or evidence.get("hook_status")
                != codex_isolated.ULTRA_FORK_POLICY_BLOCK_STATUS
                or evidence.get("decision")
                != codex_isolated.ULTRA_FORK_POLICY_BLOCK_DECISION
                or evidence.get("feedback")
                != reason_template.format(call_id=call_id)
                or evidence.get("resolution_status")
                != codex_isolated.ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS
                or child_observed
                or call_id in collab_ids
            ):
                raise BenchmarkToolError(
                    "Ultra orchestration canary blocked fork-policy decision is invalid"
                )

    allowed_children = {
        str(activities[call_id]["child_thread_id"]) for call_id in allowed_ids
    }
    if (
        len(allowed_ids) != 1
        or len(blocked_ids) != 2
        or blocked_parents != {root_thread_id} | allowed_children
        or len(allowed_children) != 1
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary did not prove root and descendant fork3 denial"
        )
    root_allowed = [
        call_id
        for call_id in allowed_ids
        if raw_calls[call_id]["parent_thread_id"] == root_thread_id
    ]
    root_blocked = [
        call_id
        for call_id in blocked_ids
        if raw_calls[call_id]["parent_thread_id"] == root_thread_id
    ]
    if (
        len(root_allowed) != 1
        or len(root_blocked) != 1
        or response_positions[root_blocked[0]] >= raw_calls[root_allowed[0]]["index"]
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary did not deny fork3 before fork-all"
        )
    return dict(policy)


def _audit_accounting_projection(
    usage: Mapping[str, Any],
    agent_log: Path,
    normalized_usage: Mapping[str, Any],
    gate_authentication: Mapping[str, Any],
) -> dict[str, Any]:
    """Rebind projection-v6 spawn, provider-gate, hook, and baseline evidence."""

    messages = _json_messages(agent_log)
    raw_calls: dict[str, dict[str, Any]] = {}
    activities: dict[str, dict[str, Any]] = {}
    collab_ids: set[str] = set()
    responses: list[dict[str, Any]] = []
    for index, message in enumerate(messages):
        parsed_response = codex_isolated.normalized_raw_response(message)
        if parsed_response is not None:
            response_id, thread_id, turn_id, breakdown = parsed_response
            responses.append(
                {
                    "index": index,
                    "response_id": response_id,
                    "thread_id": thread_id,
                    "turn_id": turn_id,
                    "usage": dict(breakdown),
                }
            )
        method = message.get("method")
        params = message.get("params")
        if not isinstance(params, Mapping):
            continue
        item = params.get("item")
        if method == "rawResponseItem/completed" and isinstance(item, Mapping):
            if item.get("type") != "function_call" or item.get("name") not in (
                "spawn_agent",
                "collaboration.spawn_agent",
            ):
                continue
            call_id = item.get("call_id")
            parent = params.get("threadId")
            turn_id = params.get("turnId")
            if (
                not isinstance(call_id, str)
                or not call_id
                or call_id in raw_calls
                or not isinstance(parent, str)
                or not parent
                or not isinstance(turn_id, str)
                or not turn_id
                or item.get("namespace") not in (None, "", "collaboration")
            ):
                raise BenchmarkToolError(
                    "Ultra orchestration canary has a malformed raw spawn call"
                )
            try:
                arguments = json.loads(str(item.get("arguments")))
            except json.JSONDecodeError as error:
                raise BenchmarkToolError(
                    "Ultra orchestration canary spawn arguments are malformed"
                ) from error
            if not isinstance(arguments, Mapping) or arguments.get("fork_turns") not in (
                "3",
                "all",
            ):
                raise BenchmarkToolError(
                    "Ultra orchestration canary spawn did not use the exact fork3/all probe"
                )
            raw_calls[call_id] = {
                "index": index,
                "parent_thread_id": parent,
                "parent_turn_id": turn_id,
                "fork_turns": arguments["fork_turns"],
            }
        if (
            method in ("item/started", "item/completed")
            and isinstance(item, Mapping)
            and item.get("type") == "subAgentActivity"
            and item.get("kind") == "started"
        ):
            activity_id = item.get("id")
            child = item.get("agentThreadId")
            parent = params.get("threadId")
            turn_id = params.get("turnId")
            if not all(
                isinstance(value, str) and value
                for value in (activity_id, child, parent, turn_id)
            ):
                raise BenchmarkToolError(
                    "Ultra orchestration canary has malformed subagent activity"
                )
            canonical = {
                "parent_thread_id": parent,
                "parent_turn_id": turn_id,
                "child_thread_id": child,
            }
            prior = activities.get(str(activity_id))
            if prior is not None and prior != canonical:
                raise BenchmarkToolError(
                    "Ultra orchestration canary reused a subagent activity id"
                )
            activities[str(activity_id)] = canonical
        if (
            method in ("item/started", "item/completed")
            and isinstance(item, Mapping)
            and item.get("type") == "collabAgentToolCall"
            and item.get("tool") == "spawnAgent"
        ):
            collab_id = item.get("id")
            if not isinstance(collab_id, str) or not collab_id:
                raise BenchmarkToolError(
                    "Ultra orchestration canary has malformed collab spawn evidence"
                )
            collab_ids.add(collab_id)

    if not raw_calls:
        raise BenchmarkToolError(
            "Ultra orchestration canary observed no raw fork-policy probe"
        )
    raw_ids = set(raw_calls)
    allowed_ids = {
        call_id
        for call_id, call in raw_calls.items()
        if call["fork_turns"] == "all"
    }
    blocked_ids = raw_ids - allowed_ids
    activity_ids = set(activities)
    if allowed_ids != activity_ids or blocked_ids & activity_ids:
        raise BenchmarkToolError(
            "Ultra orchestration canary allowed raw calls do not exactly match "
            "subAgentActivity IDs, or a blocked call created a child"
        )
    for call_id in allowed_ids:
        raw_call = raw_calls[call_id]
        activity = activities[call_id]
        if (
            activity["parent_thread_id"] != raw_call["parent_thread_id"]
            or activity["parent_turn_id"] != raw_call["parent_turn_id"]
        ):
            raise BenchmarkToolError(
                "Ultra orchestration canary raw/activity parent identities disagree"
            )

    expected_sets = {
        "raw_spawn_call_ids": sorted(raw_ids),
        "activity_spawn_call_ids": sorted(activity_ids),
        "collab_spawn_call_ids": sorted(collab_ids),
        "resolved_spawn_call_ids": sorted(allowed_ids),
        "failed_spawn_call_ids": sorted(blocked_ids),
        "policy_blocked_spawn_call_ids": sorted(blocked_ids),
        "unresolved_spawn_call_ids": [],
        "unsupported_spawn_call_ids": [],
        "inference_child_thread_ids": sorted(
            str(activity["child_thread_id"]) for activity in activities.values()
        ),
        "hook_observed_spawn_call_ids": sorted(raw_ids),
        "hook_allowed_spawn_call_ids": sorted(allowed_ids),
        "hook_blocked_spawn_call_ids": sorted(blocked_ids),
        "hook_invalid_spawn_call_ids": [],
    }
    for field, expected in expected_sets.items():
        if usage.get(field) != expected or normalized_usage.get(field) != expected:
            raise BenchmarkToolError(
                f"Ultra orchestration canary has an inexact {field} projection"
            )
    if (
        usage.get("accounting_projection_schema_version")
        != ACCOUNTING_PROJECTION_SCHEMA_VERSION
        or normalized_usage.get("accounting_projection_schema_version")
        != ACCOUNTING_PROJECTION_SCHEMA_VERSION
        or usage.get("spawn_binding_source") != SPAWN_BINDING_SOURCE
        or normalized_usage.get("spawn_binding_source") != SPAWN_BINDING_SOURCE
        or usage.get("fork_policy_complete") is not True
        or normalized_usage.get("fork_policy_complete") is not True
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary has the wrong accounting projection schema"
        )
    accounting_booleans = (
        "spawn_linkage_complete",
        "descendant_accounting_complete",
        "cumulative_projection_complete",
        "fork_policy_complete",
        "accounting_complete",
    )
    if any(
        usage.get(field) is not True or normalized_usage.get(field) is not True
        for field in accounting_booleans
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary accounting projection is incomplete"
        )

    raw_root_id = usage.get("root_thread_id")
    if not isinstance(raw_root_id, str) or not raw_root_id:
        raise BenchmarkToolError("Ultra orchestration canary lacks a projection root")
    if usage.get("fork_policy") != normalized_usage.get("fork_policy"):
        raise BenchmarkToolError(
            "Ultra orchestration canary raw and normalized fork policies disagree"
        )
    fork_policy = _audit_fork_policy(
        usage.get("fork_policy"),
        raw_calls=raw_calls,
        activities=activities,
        collab_ids=collab_ids,
        responses=responses,
        root_thread_id=raw_root_id,
    )
    accounting_raw = normalized_usage.get("thread_accounting")
    if not isinstance(accounting_raw, list):
        raise BenchmarkToolError(
            "Ultra orchestration canary lacks normalized thread accounting"
        )
    accounting: dict[str, Mapping[str, Any]] = {}
    for index, raw_thread in enumerate(accounting_raw):
        thread = _mapping(raw_thread, f"normalized canary thread accounting {index}")
        thread_id = thread.get("thread_id")
        if not isinstance(thread_id, str) or not thread_id or thread_id in accounting:
            raise BenchmarkToolError(
                "Ultra orchestration canary has malformed normalized thread accounting"
            )
        accounting[thread_id] = thread
    if set(accounting) != {raw_root_id} | set(expected_sets["inference_child_thread_ids"]):
        raise BenchmarkToolError(
            "Ultra orchestration canary normalized accounting changed the thread tree"
        )

    nonzero_baseline_children: list[str] = []
    spawn_parent_response_ids: dict[str, str] = {}
    pre_spawn_root_response_counts: dict[str, int] = {}
    for call_id in sorted(allowed_ids):
        raw_call = raw_calls[call_id]
        parent = str(raw_call["parent_thread_id"])
        turn_id = str(raw_call["parent_turn_id"])
        if parent != raw_root_id:
            raise BenchmarkToolError(
                "Ultra orchestration canary spawn is not owned by the root thread"
            )
        earlier_completed = [
            response
            for response in responses
            if response["index"] < raw_call["index"]
            and response["thread_id"] == parent
        ]
        if not earlier_completed:
            raise BenchmarkToolError(
                "Ultra orchestration canary spawned before a completed root response"
            )
        pre_spawn_root_response_counts[call_id] = len(earlier_completed)
        containing_responses = [
            response
            for response in responses
            if response["index"] > raw_call["index"]
            and response["thread_id"] == parent
            and response["turn_id"] == turn_id
        ]
        if not containing_responses:
            raise BenchmarkToolError(
                "Ultra orchestration canary raw spawn lacks its parent response"
            )
        spawn_response = containing_responses[0]
        expected_baseline = {field: 0 for field in _TOKEN_FIELDS}
        for response in responses:
            if (
                response["index"] < spawn_response["index"]
                and response["thread_id"] == parent
            ):
                for field in _TOKEN_FIELDS:
                    expected_baseline[field] += int(response["usage"][field])
        child_id = str(activities[call_id]["child_thread_id"])
        child = accounting.get(child_id)
        if child is None or (
            child.get("parent_thread_id") != parent
            or child.get("spawn_call_id") != call_id
            or child.get("spawn_parent_turn_id") != turn_id
            or child.get("spawn_parent_response_id") != spawn_response["response_id"]
            or child.get("spawn_fork_turns") != "all"
            or child.get("spawn_fork_semantics")
            != "full_history_parent_pre_response"
            or child.get("spawn_binding_status") != "resolved"
            or child.get("expected_cumulative_baseline") != expected_baseline
            or child.get("cumulative_projection_exempt_response_id") is not None
            or child.get("cumulative_projection_exempt_response_usage") is not None
            or child.get("cumulative_projection_status") != "matched_full_projection"
            or child.get("cumulative_projection_match") is not True
            or child.get("accounting_complete") is not True
        ):
            raise BenchmarkToolError(
                "Ultra orchestration canary child accounting projection is inconsistent"
            )
        if expected_baseline["total_tokens"] <= 0:
            raise BenchmarkToolError(
                "Ultra orchestration canary child inherited a zero baseline"
            )
        nonzero_baseline_children.append(child_id)
        spawn_parent_response_ids[call_id] = str(spawn_response["response_id"])

    root = accounting[raw_root_id]
    boundary = _mapping(
        normalized_usage.get("submission_boundary"),
        "normalized Ultra canary submission boundary",
    )
    if (
        root.get("spawn_binding_status") != "root_zero"
        or root.get("expected_cumulative_baseline")
        != {field: 0 for field in _TOKEN_FIELDS}
        or root.get("cumulative_projection_exempt_response_id")
        != boundary.get("response_id")
        or root.get("cumulative_projection_match") is not True
        or root.get("accounting_complete") is not True
        or normalized_usage.get("submission_boundary_exact") is not True
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary root accounting exception is inconsistent"
        )
    gate_record = _mapping(
        gate_authentication.get("record"), "Ultra canary provider-gate record"
    )
    gate_state = _mapping(
        gate_record.get("state"), "Ultra canary provider-gate state"
    )
    gate_derived = _mapping(
        gate_authentication.get("derived"), "Ultra canary provider-gate derivation"
    )
    gate_invariants = _mapping(
        gate_record.get("invariants"), "Ultra canary provider-gate invariants"
    )
    teardown = _mapping(usage.get("adapter_teardown"), "Ultra canary adapter teardown")
    if (
        gate_authentication.get("authenticated") is not True
        or gate_state.get("close_reason") != "accepted_submission"
        or gate_state.get("crossing") is not None
        or gate_record.get("setup_requests") != []
        or gate_invariants.get("all_appserver_deliveries_reconciled") is not True
        or teardown.get("completed") is not True
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary lacks exact projection-v6 gate evidence"
        )
    try:
        from . import run_matrix as matrix_verifier
    except ImportError:  # Direct script execution.
        import run_matrix as matrix_verifier  # type: ignore
    appserver_usage = {
        field: _nonnegative_int(usage.get(field), f"app-server {field}")
        for field in _TOKEN_FIELDS
    }
    provider_usage = {
        **{
            field: _nonnegative_int(
                normalized_usage.get(field), f"provider {field}"
            )
            for field in _TOKEN_FIELDS[:-1]
        },
        "total_tokens": _nonnegative_int(
            normalized_usage.get("model_tokens"), "provider total_tokens"
        ),
    }
    reconciliation = matrix_verifier.verify_provider_usage_reconciliation(
        usage.get("provider_usage_reconciliation"),
        expected_provider_usage=provider_usage,
        expected_appserver_usage=appserver_usage,
        expected_provider_response_ids=gate_derived.get("response_ids"),
        expected_appserver_response_ids=usage.get("response_ids"),
        expected_appserver_response_ledger=usage.get("appserver_response_ledger"),
        required_suppressed_wait_count=None,
    )
    if (
        normalized_usage.get("provider_usage_reconciliation") != reconciliation
        or normalized_usage.get("provider_response_count")
        != reconciliation["provider_response_count"]
        or normalized_usage.get("appserver_response_count")
        != reconciliation["appserver_response_count"]
        or normalized_usage.get("suppressed_collaboration_wait_response_count")
        != reconciliation["suppressed_collaboration_wait_response_count"]
        or normalized_usage.get(
            "superseded_by_collaboration_message_response_count"
        )
        != reconciliation[
            "superseded_by_collaboration_message_response_count"
        ]
        or normalized_usage.get(
            "discarded_after_explicit_child_interrupt_response_count"
        )
        != reconciliation[
            "discarded_after_explicit_child_interrupt_response_count"
        ]
        or normalized_usage.get("provider_response_ids")
        != reconciliation["provider_response_ids"]
        or normalized_usage.get("appserver_response_ids")
        != reconciliation["appserver_response_ids"]
        or normalized_usage.get("response_count")
        != reconciliation["provider_response_count"]
        or normalized_usage.get("response_ids")
        != reconciliation["provider_response_ids"]
        or normalized_usage.get("call_count")
        != reconciliation["provider_response_count"]
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary normalized provider totals are inconsistent"
        )
    projection_evidence = {
        "accounting_projection_schema_version": ACCOUNTING_PROJECTION_SCHEMA_VERSION,
        "provider_gate_protocol": runner.PROVIDER_GATE_PROTOCOL,
        "provider_gate_record_sha256": gate_authentication.get("record_sha256"),
        "provider_gate_close_reason": gate_state.get("close_reason"),
        "provider_gate_response_ids": gate_derived.get("response_ids"),
        "provider_gate_deliveries_reconciled": True,
        "provider_usage_reconciliation": reconciliation,
        "provider_gate_setup_requests_empty": True,
        "provider_requests_quiescent": gate_state.get("all_complete") is True,
        "adapter_teardown_complete": True,
        "spawn_binding_source": SPAWN_BINDING_SOURCE,
        **expected_sets,
        "spawn_parent_response_ids": dict(sorted(spawn_parent_response_ids.items())),
        "pre_spawn_completed_root_response_counts": dict(
            sorted(pre_spawn_root_response_counts.items())
        ),
        "raw_call_activity_id_match": True,
        "completed_root_response_before_spawn": True,
        "fork_turns_all_child_thread_count": len(allowed_ids),
        "nonzero_inherited_baseline_child_thread_ids": sorted(
            nonzero_baseline_children
        ),
        "spawn_linkage_complete": True,
        "descendant_accounting_complete": True,
        "cumulative_projection_complete": True,
        "fork_policy_complete": True,
        "accounting_complete": True,
        "fork_policy": fork_policy,
        "thread_accounting": [
            dict(accounting[thread_id]) for thread_id in sorted(accounting)
        ],
    }
    projection_evidence["projection_payload_sha256"] = _canonical_sha256(
        projection_evidence
    )
    return projection_evidence


def validate_usage_and_log(
    usage: Mapping[str, Any],
    agent_log: Path,
    *,
    token_limit: int,
    normalized_usage: Mapping[str, Any] | None = None,
    gate_authentication: Mapping[str, Any],
) -> dict[str, Any]:
    """Fail closed unless the log proves delegation at an exact submit boundary."""

    if token_limit <= 0:
        raise BenchmarkToolError("Ultra orchestration canary token limit is invalid")
    root_thread_id = usage.get("root_thread_id")
    if not isinstance(root_thread_id, str) or not root_thread_id:
        raise BenchmarkToolError("Ultra orchestration canary lacks a root thread")
    submission_boundary = _mapping(
        usage.get("submission_boundary"), "Ultra canary submission boundary"
    )
    try:
        replayed = replay_ledger(
            agent_log,
            root_thread_id=root_thread_id,
            token_limit=token_limit,
            submission_boundary=submission_boundary,
        )
    except RuntimeError as error:
        raise BenchmarkToolError(
            f"Ultra orchestration canary ledger replay failed: {error}"
        ) from error
    for field in _STABLE_LEDGER_FIELDS:
        if usage.get(field) != replayed.get(field):
            raise BenchmarkToolError(
                f"Ultra orchestration canary ledger replay disagrees on {field}"
            )
    artifact_normalized = runner._read_ultra_token_usage(usage)
    replay_normalized = runner._read_ultra_token_usage(replayed)
    if normalized_usage is not None and dict(normalized_usage) != artifact_normalized:
        raise BenchmarkToolError(
            "Ultra orchestration canary runner normalization disagrees with its ledger"
        )
    def stable_replay_projection(value: Mapping[str, Any]) -> dict[str, Any]:
        projected = json.loads(json.dumps(value, sort_keys=True))
        projected.pop("observed_at_unix_ns", None)
        # Gate calls and teardown are authenticated from the sealed mode-0444
        # artifact below.  They are intentionally absent from a raw app-server
        # log replay, so compare the independently replayable ledger after
        # removing only those attached records.
        projected.pop("provider_token_gate", None)
        projected.pop("adapter_teardown", None)
        appserver_usage = projected.get("appserver_usage")
        appserver_count = projected.get("appserver_response_count")
        appserver_ids = projected.get("appserver_response_ids")
        if (
            isinstance(appserver_usage, Mapping)
            and isinstance(appserver_count, int)
            and isinstance(appserver_ids, list)
        ):
            for field in _TOKEN_FIELDS[:-1]:
                projected[field] = appserver_usage.get(field)
            projected["model_tokens"] = appserver_usage.get("total_tokens")
            projected["call_count"] = appserver_count
            projected["response_count"] = appserver_count
            projected["response_ids"] = appserver_ids
        for field in (
            "provider_response_count",
            "provider_response_ids",
            "provider_usage",
            "suppressed_collaboration_wait_response_count",
            "suppressed_collaboration_wait_response_ids",
            "suppressed_collaboration_wait_usage",
            "suppressed_collaboration_wait_evidence",
            "superseded_by_collaboration_message_response_count",
            "superseded_by_collaboration_message_response_ids",
            "superseded_by_collaboration_message_usage",
            "superseded_by_collaboration_message_evidence",
            "discarded_after_explicit_child_interrupt_response_count",
            "discarded_after_explicit_child_interrupt_response_ids",
            "discarded_after_explicit_child_interrupt_usage",
            "discarded_after_explicit_child_interrupt_evidence",
            "provider_usage_reconciliation",
        ):
            projected.pop(field, None)
        response_ledger = projected.get("appserver_response_ledger")
        if isinstance(response_ledger, list):
            for response in response_ledger:
                if isinstance(response, dict):
                    response["provider_gate_call"] = None
                    response.pop("raw_response_observed_at_unix_ns", None)
                    response.pop("raw_response_observed_at_monotonic_ns", None)
        return projected

    stable_artifact_normalized = stable_replay_projection(artifact_normalized)
    stable_replay_normalized = stable_replay_projection(replay_normalized)
    if stable_artifact_normalized != stable_replay_normalized:
        raise BenchmarkToolError(
            "Ultra orchestration canary normalized usage disagrees with replay"
        )
    normalized = artifact_normalized

    if (
        usage.get("measurement_source")
        != codex_isolated.ULTRA_USAGE_MEASUREMENT_SOURCE
        or usage.get("notification") != codex_isolated.ULTRA_USAGE_NOTIFICATION
        or usage.get("usage_scope") != codex_isolated.ULTRA_USAGE_SCOPE
        or usage.get("live_cumulative") is not True
        or usage.get("input_includes_cached") is not True
        or usage.get("drain_complete") is not False
        or usage.get("measurement_exact") is not True
        or usage.get("first_crossing") is not None
        or usage.get("stop_reason") != "first_valid_proof"
        or usage.get("interrupt_requested") is not False
        or usage.get("pending_interrupt_response_count") != 0
        or usage.get("active_thread_ids") != [root_thread_id]
        or usage.get("unresolved_thread_ids") != []
        or usage.get("invalid_reasons") != []
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary did not stop at an exact submission boundary"
        )
    for field, wanted in (
        ("schema_version", codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION),
        ("submission_transport", codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT),
        ("authenticated", True),
        ("status", "accepted"),
        ("exact", True),
        ("root_only", True),
        ("descendants_quiescent", True),
        ("sole_model_tool_call_in_response", True),
        ("outer_exec_final_raw_item", True),
        ("inner_dynamic_call_observed", True),
        ("inner_dynamic_item_started", True),
        ("inner_submit_invocation_exact", True),
        ("inner_submit_only_nested_tool_call", True),
        ("inner_dynamic_call_left_blocked", True),
        ("inner_dynamic_tool_response_sent", False),
        ("outer_exec_output_emitted", False),
        ("later_model_response_possible", False),
    ):
        if submission_boundary.get(field) != wanted:
            raise BenchmarkToolError(
                f"Ultra orchestration canary boundary has wrong {field}"
            )
    gate_record = _mapping(
        gate_authentication.get("record"), "Ultra canary provider-gate record"
    )
    transitions = gate_record.get("transitions")
    gate_close = submission_boundary.get("provider_gate_close")
    accepted_closes = (
        [
            transition
            for transition in transitions
            if isinstance(transition, Mapping)
            and transition.get("to_phase") == "CLOSED"
            and transition.get("reason") == "terminal_close:accepted_submission"
        ]
        if isinstance(transitions, list)
        else []
    )
    if (
        not isinstance(gate_close, Mapping)
        or set(gate_close)
        != {"won", "requested_reason", "effective_reason", "phase", "sequence"}
        or gate_close.get("won") is not True
        or gate_close.get("requested_reason") != "accepted_submission"
        or gate_close.get("effective_reason") != "accepted_submission"
        or gate_close.get("phase") != "CLOSED"
        or len(accepted_closes) != 1
        or gate_close.get("sequence") != accepted_closes[0].get("sequence")
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary boundary/gate close crossbinding changed"
        )
    if submission_boundary.get("thread_id") != root_thread_id:
        raise BenchmarkToolError("Ultra orchestration canary boundary is not root-owned")
    nested_wire = _audit_nested_submission_wire(agent_log, submission_boundary)

    threads_raw = usage.get("threads")
    if not isinstance(threads_raw, list):
        raise BenchmarkToolError("Ultra orchestration canary has no thread ledger")
    threads: dict[str, Mapping[str, Any]] = {}
    for index, raw_thread in enumerate(threads_raw):
        thread = _mapping(raw_thread, f"Ultra canary thread {index}")
        thread_id = thread.get("thread_id")
        if not isinstance(thread_id, str) or not thread_id or thread_id in threads:
            raise BenchmarkToolError("Ultra orchestration canary has invalid thread IDs")
        threads[thread_id] = thread
    if set(threads) != {
        str(item.get("thread_id"))
        for item in replayed.get("threads", [])
        if isinstance(item, Mapping)
    }:
        raise BenchmarkToolError("Ultra orchestration canary replay changed its tree")
    root = threads.get(root_thread_id)
    if root is None or root.get("parent_thread_id") is not None:
        raise BenchmarkToolError("Ultra orchestration canary root is malformed")
    if (
        root.get("active_turn_id") != usage.get("root_turn_id")
        or root.get("turn_status") in ("completed", "failed", "interrupted")
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary root is not blocked at submission"
        )

    descendants = [
        thread for thread_id, thread in threads.items() if thread_id != root_thread_id
    ]
    positive_descendants = [
        thread
        for thread in descendants
        if isinstance(thread.get("parent_thread_id"), str)
        and thread.get("provisional") is False
        and thread.get("turn_seen") is True
        and thread.get("active_turn_id") is None
        and thread.get("turn_status") == "completed"
        and _nonnegative_int(thread.get("response_count"), "child response_count") > 0
        and _nonnegative_int(thread.get("total_tokens"), "child total_tokens") > 0
    ]
    if not positive_descendants:
        raise BenchmarkToolError(
            "Ultra orchestration canary observed no completed positive-usage descendant"
        )

    appserver_response_count = _positive_int(
        usage.get("response_count"), "app-server response_count"
    )
    provider_response_count = _positive_int(
        normalized.get("provider_response_count"), "provider response_count"
    )
    thread_count = _positive_int(usage.get("thread_count"), "thread_count")
    total_tokens = _positive_int(normalized.get("model_tokens"), "provider total_tokens")
    input_tokens = _nonnegative_int(normalized.get("input_tokens"), "provider input_tokens")
    cached_input_tokens = _nonnegative_int(
        normalized.get("cached_input_tokens"), "provider cached_input_tokens"
    )
    output_tokens = _nonnegative_int(
        normalized.get("output_tokens"), "provider output_tokens"
    )
    if thread_count != len(threads) or thread_count < 2:
        raise BenchmarkToolError("Ultra orchestration canary lacks a delegated tree")
    if cached_input_tokens > input_tokens:
        raise BenchmarkToolError("Ultra orchestration canary cached input is invalid")
    if total_tokens != input_tokens + output_tokens or total_tokens >= token_limit:
        raise BenchmarkToolError("Ultra orchestration canary total is invalid")
    if usage.get("notification_sequence") != appserver_response_count:
        raise BenchmarkToolError("Ultra orchestration canary response sequence is invalid")
    raw_notifications = [
        message
        for message in _json_messages(agent_log)
        if message.get("method") == codex_isolated.ULTRA_USAGE_NOTIFICATION
    ]
    raw_response_ids = {
        params.get("responseId")
        for message in raw_notifications
        if isinstance((params := message.get("params")), Mapping)
        and isinstance(params.get("responseId"), str)
        and params.get("responseId")
    }
    if len(raw_response_ids) != appserver_response_count:
        raise BenchmarkToolError(
            "Ultra orchestration canary log has the wrong unique response count"
        )
    projection = _audit_accounting_projection(
        usage, agent_log, normalized, gate_authentication
    )

    return {
        "root_terminal_status": "active_at_submission_boundary",
        "thread_count": thread_count,
        "observed_descendant_thread_count": len(descendants),
        "positive_usage_descendant_thread_count": len(positive_descendants),
        "response_count": provider_response_count,
        "provider_response_count": provider_response_count,
        "appserver_response_count": appserver_response_count,
        "suppressed_collaboration_wait_response_count": (
            normalized["suppressed_collaboration_wait_response_count"]
        ),
        "superseded_by_collaboration_message_response_count": (
            normalized["superseded_by_collaboration_message_response_count"]
        ),
        "discarded_after_explicit_child_interrupt_response_count": (
            normalized[
                "discarded_after_explicit_child_interrupt_response_count"
            ]
        ),
        "notification_count_in_audit_log": len(raw_notifications),
        "unique_raw_response_count_in_audit_log": len(raw_response_ids),
        "input_tokens_including_cached": input_tokens,
        "cached_input_tokens": cached_input_tokens,
        "output_tokens": output_tokens,
        "total_model_tokens": total_tokens,
        "submission_boundary_sequence": _positive_int(
            submission_boundary.get("sequence"), "submission boundary sequence"
        ),
        "candidate_sha256": submission_boundary.get("candidate_sha256"),
        "nested_submission_wire": nested_wire,
        "root_active_at_boundary": True,
        "descendants_quiescent": True,
        "drain_complete": False,
        "measurement_exact": True,
        "submission_boundary_exact": True,
        "stop_reason": "first_valid_proof",
        "token_limit_triggered": False,
        "accounting_projection": projection,
    }


def _artifact_path(
    project_root: Path,
    artifact_root: Path,
    descriptor: Mapping[str, Any],
    label: str,
) -> Path:
    relative = descriptor.get("path")
    digest = descriptor.get("sha256")
    if (
        not isinstance(relative, str)
        or not relative
        or PurePosixPath(relative).is_absolute()
        or ".." in PurePosixPath(relative).parts
        or not isinstance(digest, str)
        or len(digest) != 64
        or any(character not in "0123456789abcdef" for character in digest)
    ):
        raise BenchmarkToolError(f"Ultra orchestration canary artifact {label} is invalid")
    path = (artifact_root / relative).resolve()
    try:
        path.relative_to(artifact_root)
        artifact_root.relative_to(project_root)
    except ValueError as error:
        raise BenchmarkToolError(
            f"Ultra orchestration canary artifact {label} escapes its root"
        ) from error
    if path.is_symlink() or not path.is_file() or sha256_file(path) != digest:
        raise BenchmarkToolError(
            f"Ultra orchestration canary artifact {label} failed authentication"
        )
    if label == "provider_gate" and stat.S_IMODE(path.lstat().st_mode) != 0o444:
        raise BenchmarkToolError(
            "Ultra orchestration canary provider gate is not sealed mode 0444"
        )
    return path


def _runner_freeze_record(freeze_check: Mapping[str, Any]) -> dict[str, Any]:
    """Derive the runner check for a synthetic prompt without weakening identity."""

    value = json.loads(json.dumps(freeze_check, sort_keys=True))
    if not isinstance(value, dict):
        raise BenchmarkToolError("Ultra orchestration canary freeze check is invalid")
    production_prompt = value.pop("prompt_protocol", None)
    value["prompt_protocol"] = synthetic_runner_prompt_protocol()
    value["synthetic_canary"] = {
        "canary_id": CANARY_ID,
        "matrix_assignment": False,
        "prompt_protocol": PROMPT_PROTOCOL,
        "production_prompt_protocol_sha256": (
            _canonical_sha256(dict(production_prompt))
            if isinstance(production_prompt, Mapping)
            else None
        ),
        "scored": False,
    }
    return value


def _synthetic_descriptor(path: str, text: str) -> dict[str, Any]:
    payload = text.encode("utf-8")
    return {
        "path": path,
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
    }


def synthetic_runner_prompt_protocol() -> dict[str, Any]:
    """Give the synthetic N canary the production authenticated-release path."""

    return {
        "version": "signposted-library-v1",
        "composition_order": [
            "common_prompt",
            "condition_L_supplement_if_condition_L",
            "task_context",
            "fixed_target",
        ],
        "common_prompt": _synthetic_descriptor("prompt.md", SYNTHETIC_COMMON_PROMPT),
        # This synthetic canary never runs L.  A real controlled synthetic file
        # is nevertheless named so the production protocol schema remains exact;
        # condition N receives no supplement bytes.
        "condition_supplements": {
            "L": _synthetic_descriptor("context.md", SYNTHETIC_CONTEXT)
        },
        "N_receives_condition_supplement": False,
        "relevant_theorem_or_module_hints_supplied": False,
    }


def synthetic_runner_prompt_provenance() -> dict[str, Any]:
    effective = synthetic_effective_prompt().encode("utf-8")
    return {
        "protocol_version": "signposted-library-v1",
        "condition": "N",
        "composition_order": [
            "common_prompt",
            "condition_L_supplement_if_condition_L",
            "task_context",
            "fixed_target",
        ],
        "common_prompt": _synthetic_descriptor("prompt.md", SYNTHETIC_COMMON_PROMPT),
        "condition_supplement": None,
        "task_context": _synthetic_descriptor("context.md", SYNTHETIC_CONTEXT),
        "fixed_target": _synthetic_descriptor("SyntheticTarget.lean", SYNTHETIC_TARGET),
        "effective_prompt": {
            "sha256": hashlib.sha256(effective).hexdigest(),
            "bytes": len(effective),
            "encoding": "utf-8",
            "composition": "utf8_rstrip_each_section_join_two_newlines_final_newline_v1",
        },
        "authentication": {
            "computed_before_prompt_release": True,
            "frozen_protocol_match": True,
            "controlled_task_sources_match": True,
            "agent_command_match": True,
        },
    }


def _option_value(argv: Sequence[str], option: str, *, required: bool = True) -> str | None:
    positions = [index for index, item in enumerate(argv) if item == option]
    if not positions:
        if required:
            raise BenchmarkToolError(
                f"Ultra orchestration canary invocation lacks {option}"
            )
        return None
    if len(positions) != 1 or positions[0] + 1 >= len(argv):
        raise BenchmarkToolError(
            f"Ultra orchestration canary invocation has ambiguous {option}"
        )
    return argv[positions[0] + 1]


def _authenticated_json(
    path: Path, *, label: str, hash_field: str, kind: str
) -> dict[str, Any]:
    try:
        value = codex_isolated.verify_authenticated_record(
            read_json(path), hash_field
        )
    except RuntimeError as error:
        raise BenchmarkToolError(
            f"Ultra orchestration canary {label} is unauthenticated: {error}"
        ) from error
    if (
        value.get("schema_version")
        != codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION
        or value.get("kind") != kind
    ):
        raise BenchmarkToolError(
            f"Ultra orchestration canary {label} has the wrong schema"
        )
    return value


def _verify_prompt_release(
    runner_record: Mapping[str, Any],
    *,
    usage_path: Path,
    request_path: Path,
    artifact_root: Path,
    wall_time_seconds: int,
) -> dict[str, Any]:
    """Reauthenticate the synthetic prompt clock and publication endpoint."""

    release = _mapping(
        runner_record.get("prompt_release"), "Ultra canary prompt release"
    )
    expected_top_fields = {
        "schema_version",
        "protocol_version",
        "required",
        "status",
        "authenticated",
        "timing_exact",
        "useful_work_basis",
        "startup_timeout_seconds",
        "startup_timeout_triggered",
        "go_minimum_release_window_seconds",
        "handshake_nonce",
        "elapsed_clock",
        "artifact_paths",
        "effective_prompt_sha256",
        "effective_prompt_bytes",
        "ready",
        "go",
        "released",
        "stale_artifacts_removed",
        "error",
    }
    prompt = synthetic_effective_prompt()
    prompt_bytes = prompt.encode("utf-8")
    nonce = release.get("handshake_nonce")
    if (
        set(release) != expected_top_fields
        or release.get("schema_version") != 1
        or release.get("protocol_version") != "highambench-prompt-release-v1"
        or release.get("required") is not True
        or release.get("status") != "released_authenticated"
        or release.get("authenticated") is not True
        or release.get("timing_exact") is not True
        or release.get("useful_work_basis") != "authenticated_release"
        or release.get("startup_timeout_seconds") != 120.0
        or release.get("startup_timeout_triggered") is not False
        or release.get("go_minimum_release_window_seconds") != 5.0
        or not isinstance(nonce, str)
        or len(nonce) != 64
        or any(character not in "0123456789abcdef" for character in nonce)
        or release.get("elapsed_clock") != "CLOCK_MONOTONIC"
        or release.get("effective_prompt_sha256")
        != hashlib.sha256(prompt_bytes).hexdigest()
        or release.get("effective_prompt_bytes") != len(prompt_bytes)
        or release.get("error") is not None
    ):
        raise BenchmarkToolError("Ultra canary prompt-release summary is invalid")
    stale = release.get("stale_artifacts_removed")
    if (
        not isinstance(stale, list)
        or stale != sorted(set(stale))
        or any(not isinstance(item, str) or not Path(item).is_absolute() for item in stale)
    ):
        raise BenchmarkToolError("Ultra canary stale prompt artifacts are invalid")
    artifact_paths = _mapping(
        release.get("artifact_paths"), "Ultra canary prompt artifact paths"
    )
    if set(artifact_paths) != {"ready", "go", "release"}:
        raise BenchmarkToolError("Ultra canary prompt artifact paths are incomplete")
    command = runner_record.get("agent_command")
    if not isinstance(command, list) or not all(isinstance(item, str) for item in command):
        raise BenchmarkToolError("Ultra canary prompt command is malformed")
    expected_command_paths = {
        "ready": _option_value(command, "--prompt-ready-output"),
        "go": _option_value(command, "--prompt-go-input"),
        "release": _option_value(command, "--prompt-release-output"),
    }
    if (
        dict(artifact_paths) != expected_command_paths
        or _option_value(command, "--prompt-handshake-nonce") != nonce
        or _option_value(command, "--prompt-run-id") != CANARY_ID
        or Path(str(_option_value(command, "--usage-output"))).resolve()
        != usage_path.resolve()
    ):
        raise BenchmarkToolError("Ultra canary prompt command binding is invalid")
    base = (
        usage_path.name[: -len(".usage.json")]
        if usage_path.name.endswith(".usage.json")
        else usage_path.stem
    )
    expected_names = {
        "ready": f"{base}.prompt-ready.json",
        "go": f"{base}.prompt-go.json",
        "release": f"{base}.prompt-release.json",
    }
    if any(
        not isinstance(value, str)
        or not Path(value).is_absolute()
        or Path(value).parent.resolve() != usage_path.parent.resolve()
        or Path(value).name != expected_names[name]
        for name, value in expected_command_paths.items()
    ):
        raise BenchmarkToolError("Ultra canary prompt paths are not usage-derived")

    agent = _mapping(runner_record.get("agent"), "Ultra canary agent identity")
    usage = _mapping(runner_record.get("token_usage"), "Ultra canary rooted usage")
    root_thread_id = usage.get("root_thread_id")
    if not isinstance(root_thread_id, str) or not root_thread_id:
        raise BenchmarkToolError("Ultra canary prompt release has no root thread")
    common = {
        "schema_version": 1,
        "protocol_version": "highambench-prompt-release-v1",
        "handshake_nonce": nonce,
        "run_id": CANARY_ID,
        "condition": "N",
        "model": agent.get("model"),
        "reasoning_effort": agent.get("reasoning_effort"),
        "root_thread_id": root_thread_id,
        "turn_start_request_id": 3,
        "effective_prompt_sha256": hashlib.sha256(prompt_bytes).hexdigest(),
        "effective_prompt_bytes": len(prompt_bytes),
        "adapter_name": "codex_isolated.py",
        "adapter_version": "1",
        "app_server_client_name": "highambench-isolated",
        "app_server_client_version": "1",
        "elapsed_clock": "CLOCK_MONOTONIC",
    }
    common_fields = set(common)
    specifications = {
        "ready": (
            "ready_sha256",
            "highambench_prompt_ready",
            {"kind", "turn_start_write_state", "ready_at_monotonic_ns", "ready_at_unix_ns"},
        ),
        "go": (
            "go_sha256",
            "highambench_prompt_go",
            {
                "kind",
                "ready_sha256",
                "turn_start_write_authorized",
                "authorized_at_monotonic_ns",
                "authorized_at_unix_ns",
            },
        ),
        "released": (
            "release_sha256",
            "highambench_prompt_released",
            {
                "kind",
                "ready_sha256",
                "go_sha256",
                "turn_start_write_state",
                "timestamp_capture_point",
                "turn_start_request_sha256",
                "turn_start_request_bytes",
                "released_at_monotonic_ns",
                "released_at_unix_ns",
                "turn_start_flushed_at_monotonic_ns",
                "turn_start_flushed_at_unix_ns",
            },
        ),
    }
    records: dict[str, Mapping[str, Any]] = {}
    for name, (hash_field, kind, extras) in specifications.items():
        descriptor = _mapping(
            release.get(name), f"Ultra canary prompt {name} descriptor"
        )
        record = _mapping(
            descriptor.get("record"), f"Ultra canary prompt {name} record"
        )
        path_key = "release" if name == "released" else name
        if (
            set(descriptor) != {"path", "file_sha256", "record_sha256", "record"}
            or descriptor.get("path") != artifact_paths.get(path_key)
            or set(record) != common_fields | extras | {hash_field}
            or any(record.get(field) != value for field, value in common.items())
            or record.get("kind") != kind
            or record.get(hash_field) != descriptor.get("record_sha256")
            or _canonical_sha256(
                {key: value for key, value in record.items() if key != hash_field}
            )
            != record.get(hash_field)
        ):
            raise BenchmarkToolError(
                f"Ultra canary prompt {name} descriptor is unauthenticated"
            )
        raw_path = Path(str(descriptor.get("path")))
        try:
            details = raw_path.lstat()
            path = raw_path.resolve()
            path.relative_to(artifact_root.resolve())
        except (OSError, ValueError) as error:
            raise BenchmarkToolError(
                f"Ultra canary prompt {name} artifact escapes or is missing"
            ) from error
        if (
            stat.S_ISLNK(details.st_mode)
            or not stat.S_ISREG(details.st_mode)
            or stat.S_IMODE(details.st_mode) != 0o444
        ):
            raise BenchmarkToolError(
                f"Ultra canary prompt {name} artifact is not sealed 0444"
            )
        payload = path.read_bytes()
        canonical = (
            json.dumps(record, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
            + "\n"
        ).encode("utf-8")
        if (
            payload != canonical
            or hashlib.sha256(payload).hexdigest() != descriptor.get("file_sha256")
        ):
            raise BenchmarkToolError(
                f"Ultra canary prompt {name} artifact failed byte authentication"
            )
        records[name] = record

    ready, go, released = records["ready"], records["go"], records["released"]
    times = (
        ready.get("ready_at_monotonic_ns"),
        ready.get("ready_at_unix_ns"),
        go.get("authorized_at_monotonic_ns"),
        go.get("authorized_at_unix_ns"),
        released.get("released_at_monotonic_ns"),
        released.get("released_at_unix_ns"),
        released.get("turn_start_flushed_at_monotonic_ns"),
        released.get("turn_start_flushed_at_unix_ns"),
    )
    if any(
        not isinstance(value, int) or isinstance(value, bool) or value <= 0
        for value in times
    ) or not (times[0] <= times[2] <= times[4] <= times[6] and times[5] <= times[7]):
        raise BenchmarkToolError("Ultra canary prompt-release timestamp order is invalid")
    if (
        ready.get("turn_start_write_state") != "not_started"
        or go.get("ready_sha256") != ready.get("ready_sha256")
        or go.get("turn_start_write_authorized") is not True
        or released.get("ready_sha256") != ready.get("ready_sha256")
        or released.get("go_sha256") != go.get("go_sha256")
        or released.get("turn_start_write_state") != "flushed"
        or released.get("timestamp_capture_point")
        != "immediately_before_turn_start_write"
    ):
        raise BenchmarkToolError("Ultra canary prompt-release chain is inconsistent")
    request_wire = {
        "id": 3,
        "method": "turn/start",
        "params": {
            "approvalPolicy": "never",
            "cwd": "/workspace",
            "effort": agent.get("reasoning_effort"),
            "input": [{"type": "text", "text": prompt}],
            "model": agent.get("model"),
            "sandboxPolicy": {"type": "dangerFullAccess"},
            "threadId": root_thread_id,
        },
    }
    wire = (
        json.dumps(request_wire, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")
    if (
        released.get("turn_start_request_sha256") != hashlib.sha256(wire).hexdigest()
        or released.get("turn_start_request_bytes") != len(wire)
    ):
        raise BenchmarkToolError("Ultra canary prompt release has the wrong wire")

    request = _authenticated_json(
        request_path,
        label="barrier request for prompt timing",
        hash_field="request_sha256",
        kind="highambench_submission_request",
    )
    boundary = _mapping(usage.get("submission_boundary"), "Ultra canary boundary timing")
    _validated_nested_submit_yield_contract(
        request,
        label="Ultra canary prompt-timed submission request",
    )
    published = request.get("request_published_at_monotonic_ns")
    outer_exec_observed = request.get(
        "outer_raw_item_observed_at_monotonic_ns"
    )
    release_ns = released.get("released_at_monotonic_ns")
    deadline_ns = release_ns + wall_time_seconds * 1_000_000_000
    if (
        not isinstance(published, int)
        or isinstance(published, bool)
        or request.get("request_published_at_monotonic_ns")
        != boundary.get("request_published_at_monotonic_ns")
        or request.get("request_published_at_unix_ns")
        != boundary.get("request_published_at_unix_ns")
        or request.get("request_sha256") != boundary.get("request_sha256")
        or not isinstance(outer_exec_observed, int)
        or isinstance(outer_exec_observed, bool)
        or outer_exec_observed < release_ns
        or outer_exec_observed > published
        or published < release_ns
        or published >= deadline_ns
        or runner_record.get("first_valid_seconds")
        != round((published - release_ns) / 1_000_000_000, 6)
        or runner_record.get("time_measurement")
        != (
            "authenticated CLOCK_MONOTONIC turn/start write to authenticated nested "
            "submission-boundary publication after outer exec raw-response completion "
            "with inner submit_proof blocked; hidden validation certifies the immutable "
            "requested bytes"
        )
    ):
        raise BenchmarkToolError("Ultra canary release/publication timing is invalid")
    return {
        "schema_version": 1,
        "protocol_version": "highambench-prompt-release-v1",
        "authenticated": True,
        "timing_exact": True,
        "elapsed_clock": "CLOCK_MONOTONIC",
        "startup_timeout_seconds": 120,
        "artifact_count": 3,
        "artifacts_reauthenticated": True,
        "released_at_monotonic_ns": release_ns,
        "measurement_deadline_monotonic_ns": deadline_ns,
        "request_published_at_monotonic_ns": published,
        "request_publication_timing_verified": True,
    }


def _verify_barrier_chain(
    paths: Mapping[str, Path],
    *,
    invocation_argv: Sequence[str],
    usage: Mapping[str, Any],
    normalized_usage: Mapping[str, Any],
    runner_record: Mapping[str, Any],
) -> dict[str, Any]:
    """Authenticate retained production runner artifacts and their bindings."""

    challenge = _authenticated_json(
        paths["barrier_challenge"],
        label="barrier challenge",
        hash_field="challenge_sha256",
        kind="highambench_submission_challenge",
    )
    call = _authenticated_json(
        paths["barrier_call"],
        label="barrier call",
        hash_field="call_sha256",
        kind="highambench_submission_call",
    )
    request = _authenticated_json(
        paths["barrier_request"],
        label="barrier request",
        hash_field="request_sha256",
        kind="highambench_submission_request",
    )
    ack = _authenticated_json(
        paths["barrier_ack"],
        label="barrier ack",
        hash_field="ack_sha256",
        kind="highambench_submission_ack",
    )
    boundary = _mapping(
        usage.get("submission_boundary"), "Ultra canary accepted boundary"
    )
    gate_close = boundary.get("provider_gate_close")
    if (
        boundary.get("schema_version")
        != codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION
        or not isinstance(gate_close, Mapping)
        or set(gate_close)
        != {"won", "requested_reason", "effective_reason", "phase", "sequence"}
        or gate_close.get("won") is not True
        or gate_close.get("requested_reason") != "accepted_submission"
        or gate_close.get("effective_reason") != "accepted_submission"
        or gate_close.get("phase") != "CLOSED"
        or type(gate_close.get("sequence")) is not int
        or gate_close["sequence"] <= 0
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary boundary lacks its exact provider-gate close"
        )
    _validated_nested_submit_yield_contract(
        challenge,
        label="Ultra orchestration canary submission challenge",
    )
    for label, record in (
        ("submission call", call),
        ("submission request", request),
        ("accepted boundary", boundary),
    ):
        try:
            runner._validate_submission_wire(
                record, candidate_path="Candidate.lean", label=label
            )
        except BenchmarkToolError as error:
            raise BenchmarkToolError(
                f"Ultra orchestration canary {label} has an invalid nested wire: {error}"
            ) from error
    wire_identity_fields = (
        "jsonrpc_request_id",
        "call_id",
        "submission_transport",
        "outer_raw_item_id",
        "outer_raw_item_type",
        "outer_exec_name",
        "outer_exec_call_id",
        "outer_exec_program",
        "outer_exec_program_bytes",
        "outer_exec_program_sha256",
        "outer_exec_yield_time_ms",
        "outer_exec_yield_envelope_basis",
        "outer_exec_yield_attempt_wall_seconds",
        "outer_exec_yield_post_submission_validation_reserve_seconds",
        "outer_exec_yield_envelope_ms",
        "outer_exec_yield_margin_ms",
        "outer_exec_timer_starts_at_or_after_prompt_release",
        "outer_exec_yield_exceeds_envelope",
        "outer_raw_item_observed_at_monotonic_ns",
        "inner_dynamic_item_started_at_monotonic_ns",
        "outer_raw_item_observed_before_inner_dynamic_call",
        "inner_dynamic_call_id",
        "inner_dynamic_tool_name",
        "inner_dynamic_arguments",
    )
    if any(
        call.get(field) != request.get(field)
        or request.get(field) != boundary.get(field)
        for field in wire_identity_fields
    ) or any(
        challenge.get(field) != call.get(field)
        for field in codex_isolated.nested_submission_exec_yield_record()
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary barrier changed its nested wire identity"
        )
    _validated_submission_event_order(
        request,
        label="Ultra orchestration canary submission request",
        derive_from_timestamps=True,
    )
    _validated_submission_event_order(
        boundary,
        label="Ultra orchestration canary accepted boundary",
        derive_from_timestamps=False,
    )
    event_order_fields = (
        "submission_event_order",
        "dynamic_call_observed_before_raw_response_completed",
        "raw_response_completed_before_dynamic_call_observed",
    )
    if any(request.get(field) != boundary.get(field) for field in event_order_fields):
        raise BenchmarkToolError(
            "Ultra orchestration canary request/boundary event order changed"
        )
    request_truth_flags = (
        "raw_response_completed_before_boundary_publication",
        "candidate_captured_at_dynamic_call",
        "root_only",
        "descendants_quiescent",
        "sole_model_tool_call_in_response",
        "outer_exec_final_raw_item",
        "inner_dynamic_call_observed",
        "inner_dynamic_item_started",
        "inner_submit_invocation_exact",
        "inner_submit_only_nested_tool_call",
    )
    if any(
        request.get(field) is not True or boundary.get(field) is not True
        for field in request_truth_flags
    ) or any(
        boundary.get(field) is not value
        for field, value in (
            ("inner_dynamic_call_left_blocked", True),
            ("inner_dynamic_tool_response_sent", False),
            ("outer_exec_output_emitted", False),
            ("later_model_response_possible", False),
        )
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary barrier has false nested-wire semantics"
        )
    candidate = paths["barrier_snapshot"].read_bytes()
    candidate_sha256 = hashlib.sha256(candidate).hexdigest()
    if (
        challenge.get("challenge_sha256") != call.get("challenge_sha256")
        or challenge.get("challenge_sha256") != request.get("challenge_sha256")
        or call.get("call_sha256") != request.get("call_sha256")
        or request.get("request_sha256") != ack.get("request_sha256")
        or request.get("candidate_sha256") != ack.get("candidate_sha256")
        or ack.get("decision") != "accept"
        or request.get("candidate_path") != "Candidate.lean"
        or request.get("candidate_sha256") != candidate_sha256
        or request.get("candidate_size_bytes") != len(candidate)
        or call.get("candidate_sha256") != candidate_sha256
        or call.get("candidate_size_bytes") != len(candidate)
        or call.get("sequence") != request.get("sequence")
        or ack.get("sequence") != request.get("sequence")
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary barrier artifact bindings disagree"
        )
    for field in ("attempt_nonce", "run_id", "validator_contract_sha256"):
        if not (
            challenge.get(field) == call.get(field) == request.get(field)
        ):
            raise BenchmarkToolError(
                f"Ultra orchestration canary barrier changed {field}"
            )

    compile_raw = _option_value(invocation_argv, "--compile-command-json")
    assert compile_raw is not None
    try:
        compile_command = json.loads(compile_raw)
    except json.JSONDecodeError as error:
        raise BenchmarkToolError("Ultra canary compile command is invalid JSON") from error
    if not isinstance(compile_command, list) or not all(
        isinstance(item, str) for item in compile_command
    ):
        raise BenchmarkToolError("Ultra canary compile command is malformed")
    audit_raw = _option_value(invocation_argv, "--audit-command-json")
    assert audit_raw is not None
    try:
        audit_command = json.loads(audit_raw)
    except json.JSONDecodeError as error:
        raise BenchmarkToolError("Ultra canary audit command is invalid JSON") from error
    if not isinstance(audit_command, list) or not all(
        isinstance(item, str) for item in audit_command
    ):
        raise BenchmarkToolError("Ultra canary audit command is malformed")
    audit_helper_raw = _option_value(invocation_argv, "--audit-helper")
    assert audit_helper_raw is not None
    audit_helper = Path(audit_helper_raw).resolve()
    if (
        not audit_helper.is_file()
        or audit_helper.name != "dependency_audit.lean"
        or _option_value(audit_command, "--audit-helper")
        != str(audit_helper)
        or _option_value(audit_command, "--source") != "{checked_submission}"
        or _option_value(audit_command, "--submission-module")
        != "{submission_module}"
        or _option_value(audit_command, "--target-theorem")
        != SYNTHETIC_TARGET_THEOREM
        or _option_value(audit_command, "--expected-module")
        != "{expected_module}"
        or _option_value(audit_command, "--expected-theorem")
        != "{expected_theorem}"
        or _option_value(audit_command, "--local-modules-file")
        != "{local_modules_file}"
        or len(audit_command) < 3
        or Path(audit_command[1]).name != "lean_isolated.py"
        or audit_command[2] != "audit"
    ):
        raise BenchmarkToolError(
            "Ultra canary did not use the production dependency-audit command"
        )
    contract = {
        "condition": "N",
        "submission_relative": "Submission.lean",
        "canonical_relative": "task/SyntheticTarget.lean",
        "target_theorem": SYNTHETIC_TARGET_THEOREM,
        "compile_command": compile_command,
        "audit_command": audit_command,
        "controlled_manifest_sha256": sha256_file(paths["controlled_manifest"]),
        "reject_workspace_local_module_imports": True,
    }
    contract_sha256 = _canonical_sha256(contract)
    if challenge.get("validator_contract_sha256") != contract_sha256:
        raise BenchmarkToolError(
            "Ultra orchestration canary validator contract is unauthenticated"
        )

    try:
        runner._bind_final_submission_boundary(normalized_usage, request, ack)
    except BenchmarkToolError as error:
        raise BenchmarkToolError(
            f"Ultra orchestration canary boundary binding failed: {error}"
        ) from error
    if any(
        boundary.get(field) != request.get(field)
        for field in (
            "sequence",
            "challenge_sha256",
            "call_sha256",
            "attempt_nonce",
            "run_id",
            "validator_contract_sha256",
            "request_sha256",
            "jsonrpc_request_id",
            "call_id",
            "thread_id",
            "turn_id",
            "response_id",
            "raw_response_notification_sequence",
            "candidate_path",
            "candidate_sha256",
            "candidate_size_bytes",
            "request_published_at_monotonic_ns",
            "request_published_at_unix_ns",
            "submission_event_order",
            "dynamic_call_observed_before_raw_response_completed",
            "raw_response_completed_before_dynamic_call_observed",
            "submission_transport",
            "outer_raw_item_id",
            "outer_raw_item_type",
            "outer_exec_name",
            "outer_exec_call_id",
            "outer_exec_program",
            "outer_exec_program_bytes",
            "outer_exec_program_sha256",
            "outer_exec_yield_time_ms",
            "outer_exec_yield_envelope_basis",
            "outer_exec_yield_attempt_wall_seconds",
            "outer_exec_yield_post_submission_validation_reserve_seconds",
            "outer_exec_yield_envelope_ms",
            "outer_exec_yield_margin_ms",
            "outer_exec_timer_starts_at_or_after_prompt_release",
            "outer_exec_yield_exceeds_envelope",
            "outer_raw_item_observed_at_monotonic_ns",
            "inner_dynamic_item_started_at_monotonic_ns",
            "outer_raw_item_observed_before_inner_dynamic_call",
            "inner_dynamic_call_id",
            "inner_dynamic_tool_name",
            "inner_dynamic_arguments",
        )
    ) or boundary.get("ack_sha256") != ack.get("ack_sha256"):
        raise BenchmarkToolError(
            "Ultra orchestration canary usage boundary is not artifact-bound"
        )

    record_boundary = _mapping(
        runner_record.get("ultra_submission_boundary"),
        "Ultra canary runner boundary",
    )
    recorded_artifacts = _mapping(
        record_boundary.get("artifacts"), "Ultra canary runner barrier artifacts"
    )
    if (
        record_boundary.get("verified") is not True
        or record_boundary.get("sequence") != request.get("sequence")
        or record_boundary.get("request_sha256") != request.get("request_sha256")
        or record_boundary.get("ack_sha256") != ack.get("ack_sha256")
        or set(recorded_artifacts) != {"challenge", "call", "request", "ack", "snapshot"}
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary runner did not retain its accepted barrier"
        )
    label_paths = {
        "challenge": paths["barrier_challenge"],
        "call": paths["barrier_call"],
        "request": paths["barrier_request"],
        "ack": paths["barrier_ack"],
        "snapshot": paths["barrier_snapshot"],
    }
    record_hashes = {
        "challenge": challenge["challenge_sha256"],
        "call": call["call_sha256"],
        "request": request["request_sha256"],
        "ack": ack["ack_sha256"],
    }
    for label, path in label_paths.items():
        descriptor = _mapping(
            recorded_artifacts.get(label), f"runner barrier artifact {label}"
        )
        if (
            Path(str(descriptor.get("path"))).resolve() != path
            or descriptor.get("file_sha256") != sha256_file(path)
            or (label != "snapshot" and descriptor.get("record_sha256") != record_hashes[label])
            or (label == "snapshot" and descriptor.get("size_bytes") != len(candidate))
            or path.stat().st_mode & 0o777 != 0o444
        ):
            raise BenchmarkToolError(
                f"Ultra orchestration canary retained {label} artifact is invalid"
            )

    accepted = paths["accepted_candidate"].read_bytes()
    if (
        accepted != candidate
        or runner_record.get("submission_sha256") != candidate_sha256
        or runner_record.get("final_submission_sha256") != candidate_sha256
        or runner_record.get("submission_changed_after_acceptance") is not False
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary accepted candidate changed after validation"
        )
    return {
        "schema_version": codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
        "sequence": request["sequence"],
        "challenge_sha256": challenge["challenge_sha256"],
        "call_sha256": call["call_sha256"],
        "request_sha256": request["request_sha256"],
        "ack_sha256": ack["ack_sha256"],
        "candidate_sha256": candidate_sha256,
        "candidate_size_bytes": len(candidate),
        "candidate_path": "Candidate.lean",
        "validator_contract_sha256": contract_sha256,
        "request_published_at_monotonic_ns": request[
            "request_published_at_monotonic_ns"
        ],
        "submission_transport": request["submission_transport"],
        "outer_raw_item_id": request["outer_raw_item_id"],
        "outer_raw_item_type": request["outer_raw_item_type"],
        "outer_exec_name": request["outer_exec_name"],
        "outer_exec_call_id": request["outer_exec_call_id"],
        "outer_exec_program": request["outer_exec_program"],
        "outer_exec_program_bytes": request["outer_exec_program_bytes"],
        "outer_exec_program_sha256": request["outer_exec_program_sha256"],
        **_validated_nested_submit_yield_contract(
            request,
            label="Ultra orchestration canary retained request",
        ),
        "outer_raw_item_observed_at_monotonic_ns": request[
            "outer_raw_item_observed_at_monotonic_ns"
        ],
        "inner_dynamic_item_started_at_monotonic_ns": request[
            "inner_dynamic_item_started_at_monotonic_ns"
        ],
        "captured_at_monotonic_ns": request["captured_at_monotonic_ns"],
        "raw_response_observed_at_monotonic_ns": request[
            "raw_response_observed_at_monotonic_ns"
        ],
        "call_id": request["call_id"],
        "inner_dynamic_call_id": request["inner_dynamic_call_id"],
        "inner_dynamic_tool_name": request["inner_dynamic_tool_name"],
        "inner_dynamic_arguments": request["inner_dynamic_arguments"],
        "outer_raw_item_and_call_ids_pairwise_distinct": len(
            {
                request["outer_raw_item_id"],
                request["outer_exec_call_id"],
                request["inner_dynamic_call_id"],
            }
        )
        == 3,
        "outer_raw_item_observed_before_inner_dynamic_call": True,
        "inner_dynamic_item_started": True,
        "inner_submit_invocation_exact": True,
        "inner_submit_only_nested_tool_call": True,
        "raw_response_completed_before_boundary_publication": True,
        "submission_event_order": boundary["submission_event_order"],
        "dynamic_call_observed_before_raw_response_completed": boundary[
            "dynamic_call_observed_before_raw_response_completed"
        ],
        "raw_response_completed_before_dynamic_call_observed": boundary[
            "raw_response_completed_before_dynamic_call_observed"
        ],
        "root_blocked_at_boundary": True,
        "descendants_quiescent": True,
        "drain_complete": False,
        "measurement_exact": True,
        "submission_boundary_exact": True,
        "no_later_model_response": True,
        "retained_read_only": True,
    }


def _verify_validation_authentication(
    paths: Mapping[str, Path],
    *,
    validation: Mapping[str, Any],
    runner_record: Mapping[str, Any],
    barrier: Mapping[str, Any],
) -> dict[str, Any]:
    """Authenticate the validator record, its bytes, and its submit request."""

    record_sha256 = validation.get("record_sha256")
    if (
        not isinstance(record_sha256, str)
        or len(record_sha256) != 64
        or any(character not in "0123456789abcdef" for character in record_sha256)
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary validation record lacks a self hash"
        )
    canonical = dict(validation)
    canonical.pop("record_sha256", None)
    if _canonical_sha256(canonical) != record_sha256:
        raise BenchmarkToolError(
            "Ultra orchestration canary validation record self hash disagrees"
        )
    validation_file_sha256 = sha256_file(paths["validation"])
    if (
        Path(str(runner_record.get("validation_log", ""))).resolve()
        != paths["validation"]
        or runner_record.get("validation_log_sha256") != validation_file_sha256
        or runner_record.get("validation_record_sha256") != record_sha256
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary runner validation hashes disagree"
        )
    authentication = _mapping(
        validation.get("authentication"),
        "Ultra canary validation authentication",
    )
    if set(authentication) != _VALIDATION_AUTHENTICATION_FIELDS:
        raise BenchmarkToolError(
            "Ultra orchestration canary validation authentication schema is inexact"
        )
    expected = {
        "schema_version": 1,
        "run_id": CANARY_ID,
        "task_id": CANARY_ID,
        "candidate_sha256": barrier.get("candidate_sha256"),
        "target_theorem": SYNTHETIC_TARGET_THEOREM,
        "controlled_manifest_sha256": sha256_file(paths["controlled_manifest"]),
        "validator_contract_sha256": barrier.get("validator_contract_sha256"),
        "submission_request_sha256": barrier.get("request_sha256"),
        "submission_sequence": barrier.get("sequence"),
    }
    if dict(authentication) != expected:
        raise BenchmarkToolError(
            "Ultra orchestration canary validation authentication bindings disagree"
        )
    return {
        "schema_version": 1,
        "authenticated": True,
        "record_sha256": record_sha256,
        "validation_log_sha256": validation_file_sha256,
        "candidate_sha256": expected["candidate_sha256"],
        "validator_contract_sha256": expected["validator_contract_sha256"],
        "submission_request_sha256": expected["submission_request_sha256"],
        "submission_sequence": expected["submission_sequence"],
    }


def controls_record(token_limit: int, wall_time_seconds: int) -> dict[str, Any]:
    """Return the exact accepted-boundary canary control declaration."""

    if token_limit <= 0 or wall_time_seconds <= 0:
        raise BenchmarkToolError("Ultra orchestration canary controls are invalid")
    return {
        "outer_token_limit": token_limit,
        "advisory_rollout_budget_limit": token_limit,
        "canary_wall_time_seconds": wall_time_seconds,
        "condition_isolation_mode": "N_without_library",
        "measurement_source": codex_isolated.ULTRA_USAGE_MEASUREMENT_SOURCE,
        "notification": codex_isolated.ULTRA_USAGE_NOTIFICATION,
        "usage_scope": codex_isolated.ULTRA_USAGE_SCOPE,
        "cached_input_counted_once": True,
        "response_id_deduplication": True,
        "accounting_projection_schema_version": (
            ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "spawn_binding_source": SPAWN_BINDING_SOURCE,
        "exact_spawn_identifier_sets_required": True,
        "raw_call_activity_id_match_required": True,
        "completed_root_response_before_spawn_required": True,
        "authenticated_pre_tool_use_hook_per_raw_spawn_required": True,
        "fork3_policy_denial_without_child_required": True,
        "root_and_descendant_fork3_denial_required": True,
        "fork_policy_complete_required": True,
        "fork_turns_all_required": True,
        "nonzero_inherited_child_baseline_required": True,
        "spawn_linkage_complete_required": True,
        "descendant_accounting_complete_required": True,
        "cumulative_projection_complete_required": True,
        "accounting_complete_required": True,
        "positive_usage_descendant_required": True,
        "accepted_submission_boundary_required": True,
        "submission_barrier_schema_version": (
            codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION
        ),
        "submission_transport": codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT,
        "outer_raw_item_type": "custom_tool_call",
        "outer_exec_name": "exec",
        "outer_exec_program_bytes": (
            codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_BYTES
        ),
        "outer_exec_program_sha256": (
            codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_SHA256
        ),
        **codex_isolated.nested_submission_exec_yield_record(),
        "outer_raw_item_before_inner_start_and_call_required": True,
        "submission_event_order_values": [
            codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE,
            codex_isolated.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER,
        ],
        "submission_event_order_flags_exactly_one_true": True,
        "request_event_order_derived_from_timestamps": True,
        "raw_response_and_inner_call_before_boundary_publication_required": True,
        "same_outer_raw_response_authenticated": True,
        "authenticated_nested_submit_proof_boundary_required": True,
        "blocked_inner_dynamic_tool_call_required": True,
        "inner_dynamic_tool_response_forbidden_on_acceptance": True,
        "outer_exec_output_forbidden_on_acceptance": True,
        "runner_validated_candidate_required": True,
        "validation_result_authentication_required": True,
        "validation_result_self_hash_required": True,
        "validation_log_byte_hash_required": True,
        "production_dependency_audit_required": True,
        "dependency_audit_complete_required": True,
        "authenticated_prompt_release_required": True,
        "prompt_release_protocol_version": "highambench-prompt-release-v1",
        "prompt_startup_timeout_seconds": 120,
        "prompt_release_artifact_count": 3,
        "release_based_deadline_required": True,
        "request_publication_endpoint_required": True,
        "root_blocked_at_boundary": True,
        "descendant_quiescence_required": True,
        "direct_submission_path_forbidden": True,
        "workspace_local_module_imports_rejected": True,
        "natural_completion_required": False,
        "no_later_model_response": True,
        "trusted_usage_path_outside_workspace": True,
        "ephemeral_thread": False,
        "history_persistence": "none",
        "thread_resume_or_fork_used": False,
        "state_directory_reused": False,
    }


def verify_evidence_document(
    evidence: Mapping[str, Any],
    *,
    project_root: Path,
    expected_benchmark_id: str,
    expected_agent: Mapping[str, Any],
    expected_token_limit: int,
    expected_prompt_protocol: Mapping[str, Any] | None = None,
    expected_execution_components: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Authenticate one evidence document and independently replay its ledger."""

    if (
        evidence.get("schema_version") != 1
        or evidence.get("kind") != EVIDENCE_KIND
        or evidence.get("status") != "passed"
        or evidence.get("public_release") is not False
        or evidence.get("scored") is not False
        or evidence.get("matrix_assignment") is not False
        or evidence.get("synthetic_input") is not True
        or evidence.get("canary_id") != CANARY_ID
        or evidence.get("benchmark_id") != expected_benchmark_id
    ):
        raise BenchmarkToolError("Ultra orchestration canary evidence header is invalid")
    if evidence.get("agent") != dict(expected_agent):
        raise BenchmarkToolError("Ultra orchestration canary used the wrong frozen agent")
    if evidence.get("prompt") != prompt_record():
        raise BenchmarkToolError("Ultra orchestration canary used the wrong synthetic prompt")

    controls = _mapping(evidence.get("controls"), "Ultra canary controls")
    wall_time_seconds = _positive_int(
        controls.get("canary_wall_time_seconds"), "canary_wall_time_seconds"
    )
    if dict(controls) != controls_record(expected_token_limit, wall_time_seconds):
        raise BenchmarkToolError("Ultra orchestration canary controls are invalid")

    artifact_root_raw = evidence.get("artifact_root")
    if not isinstance(artifact_root_raw, str) or not artifact_root_raw:
        raise BenchmarkToolError("Ultra orchestration canary artifact root is missing")
    project = project_root.resolve()
    artifact_root = (project / artifact_root_raw).resolve()
    try:
        artifact_root.relative_to(project)
    except ValueError as error:
        raise BenchmarkToolError(
            "Ultra orchestration canary artifact root escapes the project"
        ) from error
    artifacts = _mapping(evidence.get("artifacts"), "Ultra canary artifacts")
    if set(artifacts) != set(ARTIFACT_LABELS):
        raise BenchmarkToolError("Ultra orchestration canary artifact set is incomplete")
    paths = {
        label: _artifact_path(
            project, artifact_root, _mapping(artifacts[label], label), label
        )
        for label in ARTIFACT_LABELS
    }

    freeze_check = _mapping(read_json(paths["freeze_check"]), "canary freeze check")
    freeze_digest = _canonical_sha256(freeze_check)
    if expected_prompt_protocol is None:
        expected_prompt_protocol = _mapping(
            freeze_check.get("prompt_protocol"),
            "embedded production prompt protocol",
        )
    if expected_execution_components is None:
        expected_execution_components = _mapping(
            freeze_check.get("execution_components"),
            "embedded production execution components",
        )
    if not isinstance(expected_prompt_protocol, Mapping) or not expected_prompt_protocol:
        raise BenchmarkToolError("expected production prompt protocol is empty")
    if not isinstance(expected_execution_components, Mapping) or set(
        expected_execution_components
    ) != set(
        PRODUCTION_EXECUTION_COMPONENT_FIELDS
    ) or any(
        not isinstance(expected_execution_components.get(field), str)
        or re.fullmatch(r"[0-9a-f]{64}", str(expected_execution_components[field]))
        is None
        for field in PRODUCTION_EXECUTION_COMPONENT_FIELDS
    ):
        raise BenchmarkToolError(
            "expected production execution-component freeze is incomplete"
        )
    if (
        evidence.get("freeze_check_sha256") != freeze_digest
        or freeze_check.get("benchmark_id") != expected_benchmark_id
        or freeze_check.get("agent") != dict(expected_agent)
        or freeze_check.get("prompt_protocol") != dict(expected_prompt_protocol)
        or freeze_check.get("execution_components")
        != dict(expected_execution_components)
        or evidence.get("pre_canary_environment_id")
        != freeze_check.get("environment_id")
    ):
        raise BenchmarkToolError("Ultra orchestration canary freeze check is inconsistent")
    isolation = _mapping(
        freeze_check.get("agent_session_isolation"), "canary session isolation"
    )
    for field, wanted in (
        ("ephemeral_thread", False),
        ("fresh_state_directory", True),
        ("memories_disabled", True),
        ("resume_or_fork_used", False),
        ("state_directory_reused", False),
    ):
        if isolation.get(field) != wanted:
            raise BenchmarkToolError(
                f"Ultra orchestration canary freeze check has wrong {field}"
            )

    runner_freeze_check = _mapping(
        read_json(paths["runner_freeze_check"]), "canary runner freeze check"
    )
    if dict(runner_freeze_check) != _runner_freeze_record(freeze_check):
        raise BenchmarkToolError(
            "Ultra orchestration canary runner freeze check is not the synthetic derivation"
        )

    invocation = _mapping(read_json(paths["invocation"]), "canary invocation")
    argv = invocation.get("argv")
    if (
        invocation.get("schema_version") != 1
        or invocation.get("kind")
        != "highambench-ultra-orchestration-canary-invocation"
        or invocation.get("submission_evidence_role")
        != "production_runner_authenticated_nested_submit_proof_boundary"
        or not isinstance(argv, list)
        or not all(isinstance(item, str) for item in argv)
        or len(argv) < 2
        or Path(argv[1]).name != "runner.py"
    ):
        raise BenchmarkToolError("Ultra orchestration canary invocation is malformed")
    for option, wanted in (
        ("--condition", "N"),
        ("--task-id", CANARY_ID),
        ("--submission-relative", "Submission.lean"),
        ("--canonical-relative", "task/SyntheticTarget.lean"),
        ("--target-theorem", SYNTHETIC_TARGET_THEOREM),
        ("--model", str(expected_agent.get("model"))),
        ("--reasoning-effort", "ultra"),
        ("--token-limit", str(expected_token_limit)),
        ("--prompt-startup-timeout-seconds", "120"),
    ):
        positions = [index for index, item in enumerate(argv) if item == option]
        if (
            len(positions) != 1
            or positions[0] + 1 >= len(argv)
            or argv[positions[0] + 1] != wanted
        ):
            raise BenchmarkToolError(
                f"Ultra orchestration canary invocation has wrong {option}"
            )
    if invocation.get("network_evidence_role") != "production_runner_marker_and_monitor":
        raise BenchmarkToolError(
            "Ultra orchestration canary invocation lacks production network evidence"
        )
    for required_flag in (
        "--reject-workspace-local-module-imports",
        "--fresh-conversation",
        "--filesystem-isolated",
        "--network-disabled",
        "--token-enforced",
    ):
        if argv.count(required_flag) != 1:
            raise BenchmarkToolError(
                f"Ultra orchestration canary invocation lacks {required_flag}"
            )
    for forbidden in (
        "--condition-prompt-file",
        "--condition-prompt-sha256",
        "--library-source",
        "--library-root-file",
        "--library-olean",
        "--shared-olean-root",
    ):
        if forbidden in argv:
            raise BenchmarkToolError(
                f"Ultra orchestration canary invocation contains forbidden {forbidden}"
            )
    path_options = {
        "--task-root": paths["common_prompt"].parent,
        "--controlled-manifest": paths["controlled_manifest"],
        "--usage-output": paths["usage"],
        "--output": paths["runner_record"],
    }
    for option, wanted_path in path_options.items():
        raw_path = _option_value(argv, option)
        assert raw_path is not None
        if Path(raw_path).resolve() != wanted_path:
            raise BenchmarkToolError(
                f"Ultra orchestration canary invocation has wrong {option}"
            )
    audit_helper_raw = _option_value(argv, "--audit-helper")
    assert audit_helper_raw is not None
    production_audit_helper = Path(audit_helper_raw).resolve()
    if (
        not production_audit_helper.is_file()
        or production_audit_helper.name != "dependency_audit.lean"
        or paths["dependency_audit_helper"].read_bytes()
        != production_audit_helper.read_bytes()
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary dependency-audit helper is not the frozen production helper"
        )
    frozen_json = _option_value(argv, "--freeze-check-json")
    if frozen_json != json.dumps(
        runner_freeze_check,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary invocation has wrong runner freeze check"
        )
    nested_raw = _option_value(argv, "--agent-command-json")
    assert nested_raw is not None
    try:
        nested = json.loads(nested_raw)
    except json.JSONDecodeError as error:
        raise BenchmarkToolError("Ultra canary adapter command is invalid JSON") from error
    if not isinstance(nested, list) or not all(isinstance(item, str) for item in nested):
        raise BenchmarkToolError("Ultra canary adapter command is malformed")
    if len(nested) < 2 or Path(nested[1]).name != "codex_isolated.py":
        raise BenchmarkToolError(
            "Ultra orchestration canary did not use the production adapter"
        )
    for option, wanted in (
        ("--condition", "N"),
        ("--prompt-file", "{workspace}/task/prompt.md"),
        ("--context-file", "{workspace}/task/context.md"),
        ("--target-file", "{workspace}/task/SyntheticTarget.lean"),
        ("--model", str(expected_agent.get("model"))),
        ("--reasoning-effort", "ultra"),
        ("--token-limit", str(expected_token_limit)),
        ("--advisory-rollout-budget-limit", str(expected_token_limit)),
        ("--prompt-ready-output", "{prompt_ready_output}"),
        ("--prompt-go-input", "{prompt_go_input}"),
        ("--prompt-release-output", "{prompt_release_output}"),
        ("--prompt-handshake-nonce", "{prompt_handshake_nonce}"),
        ("--prompt-run-id", "{run_id}"),
        ("--provider-gate-live-output", "{provider_gate_live_output}"),
        ("--provider-gate-output", "{provider_gate_output}"),
        ("--model-catalog-sha256", "{model_catalog_sha256}"),
        ("--model-entry-sha256", "{model_entry_sha256}"),
        ("--provider-response-bound", "{provider_response_bound}"),
    ):
        if _option_value(nested, option) != wanted:
            raise BenchmarkToolError(
                f"Ultra orchestration canary adapter has wrong {option}"
            )
    for forbidden in (
        "--condition-prompt-file",
        "--condition-prompt-sha256",
        "--library-source",
        "--library-root-file",
        "--library-olean",
        "--shared-olean-root",
    ):
        if forbidden in nested:
            raise BenchmarkToolError(
                f"Ultra orchestration canary adapter contains forbidden {forbidden}"
            )
    expected_inputs = {
        "common_prompt": SYNTHETIC_COMMON_PROMPT,
        "context": SYNTHETIC_CONTEXT,
        "synthetic_target": SYNTHETIC_TARGET,
    }
    for label, wanted in expected_inputs.items():
        if paths[label].read_text(encoding="utf-8") != wanted:
            raise BenchmarkToolError(
                f"Ultra orchestration canary {label} artifact changed"
            )
    if (
        codex_isolated.build_prompt(
            paths["common_prompt"], paths["context"], paths["synthetic_target"]
        )
        != synthetic_effective_prompt()
    ):
        raise BenchmarkToolError("Ultra orchestration canary prompt replay disagrees")

    controlled = load_manifest(paths["controlled_manifest"])
    controlled_check = verify_manifest(paths["common_prompt"].parent, controlled)
    if not controlled_check["ok"] or {
        entry["path"] for entry in controlled["files"]
    } != {"prompt.md", "context.md", "SyntheticTarget.lean"}:
        raise BenchmarkToolError(
            "Ultra orchestration canary controlled synthetic package is invalid"
        )

    usage = _mapping(read_json(paths["usage"]), "Ultra canary usage")
    normalized_usage = runner.read_token_usage(paths["usage"])
    if normalized_usage is None:
        raise BenchmarkToolError("Ultra orchestration canary has no normalized usage")
    runner_record = _mapping(
        read_json(paths["runner_record"]), "Ultra canary runner record"
    )
    expected_gate_path = runner.provider_gate_paths(paths["usage"].resolve())["final"]
    if paths["provider_gate"].resolve() != expected_gate_path:
        raise BenchmarkToolError("Ultra canary provider-gate path is not usage-derived")
    raw_records = [
        json.loads(line)
        for line in paths["raw_jsonl"].read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    validation = _mapping(
        read_json(paths["validation"]), "Ultra canary validation record"
    )
    dependency_audit = _mapping(
        validation.get("dependency_audit"),
        "Ultra canary production dependency audit",
    )
    dependency_parsed = _mapping(
        dependency_audit.get("parsed"),
        "Ultra canary parsed dependency audit",
    )
    if (
        raw_records != [dict(runner_record)]
        or runner_record.get("run_id") != CANARY_ID
        or runner_record.get("task_id") != CANARY_ID
        or runner_record.get("condition") != "N"
        or runner_record.get("pass") is not True
        or runner_record.get("failure_code") is not None
        or runner_record.get("token_usage") != normalized_usage
        or runner_record.get("prompt_provenance")
        != synthetic_runner_prompt_provenance()
        or type(runner_record.get("agent_exit_code")) is not int
        or runner_record.get("agent_exit_code") != 0
        or validation.get("pass") is not True
        or validation.get("reject_workspace_local_module_imports") is not True
        or validation.get("library_audit_complete") is not True
        or validation.get("library_use") is not False
        or validation.get("library_declarations") != []
        or "system_error" not in dependency_audit
        or dependency_audit.get("system_error") is not None
        or dependency_audit.get("timed_out") is not False
        or dependency_audit.get("exit_code") != 0
        or dependency_parsed.get("ok") is not True
        or dependency_parsed.get("target_seen") is not True
        or dependency_parsed.get("forbidden_dependencies") != []
        or dependency_parsed.get("missing_helper_modules") != []
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary production runner record is invalid"
        )
    protocol = _mapping(runner_record.get("protocol"), "Ultra canary protocol")
    verified = _mapping(protocol.get("verified"), "Ultra canary verified protocol")
    preflight = _mapping(runner_record.get("n_preflight"), "Ultra canary N preflight")
    network = _mapping(
        runner_record.get("network_violation"), "Ultra canary network evidence"
    )
    if (
        verified.get("authenticated_prompt_release") is not True
        or verified.get("authenticated_first_valid_proof_boundary") is not True
        or preflight.get("ok") is not True
        or preflight.get("complete") is not True
        or network.get("detected") is not False
        or network.get("integrity_ok") is not True
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary runner controls are incomplete"
        )
    try:
        from . import run_matrix
    except ImportError:  # Direct script execution.
        import run_matrix  # type: ignore
    gate_authentication = run_matrix.authenticate_runner_provider_gate_summary(
        runner_record
    )
    gate_record = _mapping(
        gate_authentication.get("record"), "Ultra canary provider-gate record"
    )
    gate_state = _mapping(
        gate_record.get("state"), "Ultra canary provider-gate state"
    )
    if (
        gate_state.get("close_reason") != "accepted_submission"
        or gate_state.get("crossing") is not None
        or gate_record.get("setup_requests") != []
    ):
        raise BenchmarkToolError(
            "Ultra canary lacks an accepted, setup-free provider-gate endpoint"
        )
    barrier = _verify_barrier_chain(
        paths,
        invocation_argv=argv,
        usage=usage,
        normalized_usage=normalized_usage,
        runner_record=runner_record,
    )
    prompt_release_summary = _verify_prompt_release(
        runner_record,
        usage_path=paths["usage"],
        request_path=paths["barrier_request"],
        artifact_root=artifact_root,
        wall_time_seconds=wall_time_seconds,
    )
    validation_authentication = _verify_validation_authentication(
        paths,
        validation=validation,
        runner_record=runner_record,
        barrier=barrier,
    )
    audit_raw = _option_value(argv, "--audit-command-json")
    assert audit_raw is not None
    audit_command = json.loads(audit_raw)
    dependency_audit_summary = {
        "complete": True,
        "helper_sha256": sha256_file(paths["dependency_audit_helper"]),
        "command_sha256": _canonical_sha256({"argv": audit_command}),
        "library_use": False,
        "library_declarations": [],
        "target_seen": True,
        "semantic_type_equal": True,
    }
    derived_outcome = validate_usage_and_log(
        usage,
        paths["agent_log"],
        token_limit=expected_token_limit,
        normalized_usage=normalized_usage,
        gate_authentication=gate_authentication,
    )
    derived_outcome["prompt_release"] = prompt_release_summary
    if derived_outcome.get("candidate_sha256") != barrier["candidate_sha256"]:
        raise BenchmarkToolError(
            "Ultra orchestration canary outcome changed its accepted candidate"
        )
    if evidence.get("outcome") != derived_outcome:
        raise BenchmarkToolError("Ultra orchestration canary outcome is stale")

    verified_artifacts = {
        label: {
            "path": artifacts[label]["path"],
            "sha256": artifacts[label]["sha256"],
            "bytes": paths[label].stat().st_size,
        }
        for label in ARTIFACT_LABELS
    }
    return {
        "path": FROZEN_EVIDENCE_PATH,
        "status": "passed",
        "thread_count": derived_outcome["thread_count"],
        "observed_descendant_thread_count": derived_outcome[
            "observed_descendant_thread_count"
        ],
        "positive_usage_descendant_thread_count": derived_outcome[
            "positive_usage_descendant_thread_count"
        ],
        "response_count": derived_outcome["response_count"],
        "total_model_tokens": derived_outcome["total_model_tokens"],
        "drain_complete": False,
        "measurement_exact": True,
        "submission_boundary_exact": True,
        "accounting_projection": derived_outcome["accounting_projection"],
        "prompt_release": prompt_release_summary,
        "dependency_audit": dependency_audit_summary,
        "validation_authentication": validation_authentication,
        "barrier": barrier,
        "artifacts": verified_artifacts,
    }


def verify_frozen_attestation(
    project_root: Path,
    descriptor: Mapping[str, Any],
    *,
    expected_benchmark_id: str,
    expected_agent: Mapping[str, Any],
    expected_token_limit: int,
    expected_prompt_protocol: Mapping[str, Any] | None = None,
    expected_execution_components: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Authenticate the configured evidence descriptor and all live artifacts."""

    if (
        descriptor.get("path") != FROZEN_EVIDENCE_PATH
        or descriptor.get("status") != "passed"
        or not isinstance(descriptor.get("sha256"), str)
        or len(str(descriptor.get("sha256"))) != 64
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary is not frozen with passed status"
        )
    path = (project_root.resolve() / FROZEN_EVIDENCE_PATH).resolve()
    try:
        path.relative_to(project_root.resolve())
    except ValueError as error:
        raise BenchmarkToolError(
            "Ultra orchestration canary evidence path escapes the project"
        ) from error
    if not path.is_file() or sha256_file(path) != descriptor.get("sha256"):
        raise BenchmarkToolError(
            "Ultra orchestration canary evidence failed authentication"
        )
    evidence = _mapping(read_json(path), "Ultra orchestration canary evidence")
    summary = verify_evidence_document(
        evidence,
        project_root=project_root,
        expected_benchmark_id=expected_benchmark_id,
        expected_agent=expected_agent,
        expected_token_limit=expected_token_limit,
        expected_prompt_protocol=expected_prompt_protocol,
        expected_execution_components=expected_execution_components,
    )
    summary["sha256"] = descriptor["sha256"]
    return summary


def _write_synthetic_inputs(task: Path) -> tuple[Path, Path, Path]:
    task.mkdir(parents=True)
    prompt = task / "prompt.md"
    context = task / "context.md"
    target = task / "SyntheticTarget.lean"
    prompt.write_text(SYNTHETIC_COMMON_PROMPT, encoding="utf-8")
    context.write_text(SYNTHETIC_CONTEXT, encoding="utf-8")
    target.write_text(SYNTHETIC_TARGET, encoding="utf-8")
    return prompt, context, target


def _relative_artifact(path: Path, root: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError as error:
        raise BenchmarkToolError(
            f"Ultra orchestration canary artifact is outside its root: {path}"
        ) from error


def _adapter_command(
    args: argparse.Namespace,
    *,
    state_parent: Path,
) -> list[str]:
    return [
        sys.executable,
        str(args.benchmark_root.resolve() / "tools" / "codex_isolated.py"),
        "--condition",
        "N",
        "--workspace",
        "{workspace}",
        "--controlled-relative",
        "task",
        "--shared-root-relative",
        "task/shared",
        "--prompt-file",
        "{workspace}/task/prompt.md",
        "--context-file",
        "{workspace}/task/context.md",
        "--target-file",
        "{workspace}/task/SyntheticTarget.lean",
        "--usage-output",
        "{usage_output}",
        "--prompt-ready-output",
        "{prompt_ready_output}",
        "--prompt-go-input",
        "{prompt_go_input}",
        "--prompt-release-output",
        "{prompt_release_output}",
        "--prompt-handshake-nonce",
        "{prompt_handshake_nonce}",
        "--prompt-run-id",
        "{run_id}",
        "--provider-gate-live-output",
        "{provider_gate_live_output}",
        "--provider-gate-output",
        "{provider_gate_output}",
        "--model-catalog-sha256",
        "{model_catalog_sha256}",
        "--model-entry-sha256",
        "{model_entry_sha256}",
        "--provider-response-bound",
        "{provider_response_bound}",
        "--codex",
        str(args.codex.resolve()),
        "--auth-file",
        str(args.auth_file.resolve()),
        "--offline-shell",
        str(args.offline_shell.resolve()),
        "--toolchain-root",
        str(args.toolchain_root.resolve()),
        "--packages-root",
        str(args.packages_runtime_root.resolve()),
        "--state-parent",
        str(state_parent.resolve()),
        "--model",
        args.model,
        "--reasoning-effort",
        args.reasoning_effort,
        "--token-limit",
        str(args.token_limit),
        "--advisory-rollout-budget-limit",
        str(args.token_limit),
    ]


def _lean_command(args: argparse.Namespace, action: str, source: str) -> list[str]:
    return [
        sys.executable,
        str(args.benchmark_root.resolve() / "tools" / "lean_isolated.py"),
        action,
        "--condition",
        "N",
        "--workspace",
        "{workspace}",
        "--toolchain-root",
        str(args.toolchain_root.resolve()),
        "--packages-root",
        str(args.packages_runtime_root.resolve()),
        "--shared-root-relative",
        "task/shared",
        "--source",
        source,
    ]


def _audit_command(args: argparse.Namespace) -> list[str]:
    return _lean_command(args, "audit", "{checked_submission}") + [
        "--audit-helper",
        str(
            (
                args.benchmark_root.resolve()
                / "tools"
                / "dependency_audit.lean"
            ).resolve()
        ),
        "--submission-module",
        "{submission_module}",
        "--target-theorem",
        SYNTHETIC_TARGET_THEOREM,
        "--expected-module",
        "{expected_module}",
        "--expected-theorem",
        "{expected_theorem}",
        "--local-modules-file",
        "{local_modules_file}",
    ]


def _runner_command(
    args: argparse.Namespace,
    *,
    result_root: Path,
    task_root: Path,
    controlled_manifest: Path,
    runner_freeze_check: Mapping[str, Any],
    usage_output: Path,
    runner_record: Path,
    raw_jsonl: Path,
    state_parent: Path,
) -> list[str]:
    adapter = _adapter_command(args, state_parent=state_parent)
    compile_command = _lean_command(args, "olean", "{checked_submission}")
    probe_command = _lean_command(args, "probe", "{probe}")
    audit_command = _audit_command(args)
    audit_helper = (
        args.benchmark_root.resolve() / "tools" / "dependency_audit.lean"
    ).resolve()
    command = [
        sys.executable,
        str(args.benchmark_root.resolve() / "tools" / "runner.py"),
        "--condition",
        "N",
        "--task-id",
        CANARY_ID,
        "--paper-id",
        "SYNTHETIC",
        "--paper-sha256",
        _text_sha256(SYNTHETIC_TARGET),
        "--tier",
        "T1",
        "--repetition-id",
        "canary",
        "--pair-id",
        CANARY_ID,
        "--pair-order",
        "N-first",
        "--order-index",
        "1",
        "--run-id",
        CANARY_ID,
        "--agent-id",
        args.agent_id,
        "--agent-version",
        args.agent_version,
        "--model",
        args.model,
        "--reasoning-effort",
        args.reasoning_effort,
        "--environment-id",
        args.environment_id,
        "--freeze-check-json",
        json.dumps(
            runner_freeze_check,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        ),
        "--base-workspace",
        str((result_root / "base").resolve()),
        "--task-root",
        str(task_root.resolve()),
        "--controlled-manifest",
        str(controlled_manifest.resolve()),
        "--task-dest",
        "task",
        "--workspace-parent",
        str((result_root / "workspaces").resolve()),
        "--logs-dir",
        str((result_root / "logs").resolve()),
        "--raw-jsonl",
        str(raw_jsonl.resolve()),
        "--submission-relative",
        "Submission.lean",
        "--canonical-relative",
        "task/SyntheticTarget.lean",
        "--target-theorem",
        SYNTHETIC_TARGET_THEOREM,
        "--submission-module",
        "Submission",
        "--audit-helper",
        str(audit_helper),
        "--reject-workspace-local-module-imports",
        "--prompt-relative",
        "task/prompt.md",
        "--usage-output",
        str(usage_output.resolve()),
        "--agent-command-json",
        json.dumps(adapter, separators=(",", ":")),
        "--compile-command-json",
        json.dumps(compile_command, separators=(",", ":")),
        "--audit-command-json",
        json.dumps(audit_command, separators=(",", ":")),
        "--n-probe-command-json",
        json.dumps(probe_command, separators=(",", ":")),
        "--hidden-parent",
        str((result_root / "hidden").resolve()),
        "--time-limit-seconds",
        str(args.canary_time_limit_seconds),
        "--prompt-startup-timeout-seconds",
        "120",
        "--token-limit",
        str(args.token_limit),
        "--fresh-conversation",
        "--filesystem-isolated",
        "--network-disabled",
        "--token-enforced",
        "--output",
        str(runner_record.resolve()),
    ]
    return command


def run_canary(args: argparse.Namespace) -> int:
    # Lazy import avoids a module cycle when run_matrix imports the offline
    # verifier during ordinary matrix startup.
    try:
        from . import run_matrix
    except ImportError:  # Direct script execution.
        import run_matrix  # type: ignore

    if args.canary_time_limit_seconds <= 0:
        raise BenchmarkToolError("canary wall time must be positive")
    result_root = args.results_root.resolve()
    if result_root.exists() and any(result_root.iterdir()):
        raise BenchmarkToolError("canary results root must be absent or empty")
    result_root.mkdir(parents=True, exist_ok=True)
    try:
        artifact_root_relative = result_root.relative_to(args.project_root.resolve())
    except ValueError as error:
        raise BenchmarkToolError(
            "canary results root must be below project root for frozen evidence"
        ) from error
    for name in ("logs", "attempts", "workspaces", "hidden", "state", "base"):
        (result_root / name).mkdir()
    inputs = result_root / "inputs"
    prompt, context, target = _write_synthetic_inputs(inputs)
    frozen_audit_helper = (
        args.benchmark_root.resolve() / "tools" / "dependency_audit.lean"
    ).resolve()
    if not frozen_audit_helper.is_file():
        raise BenchmarkToolError(
            "frozen production dependency-audit helper is missing"
        )
    audit_helper_snapshot = inputs / "dependency_audit.lean"
    shutil.copyfile(frozen_audit_helper, audit_helper_snapshot)
    controlled_manifest = inputs / "controlled.json"
    write_json(
        controlled_manifest,
        create_manifest(
            inputs,
            requested=["prompt.md", "context.md", "SyntheticTarget.lean"],
            label="synthetic-ultra-submission-canary",
        ),
    )
    freeze_check = run_matrix.verify_frozen_run_environment(
        args,
        args.benchmark_root.resolve(),
        regenerating_token_control_canary=True,
        regenerating_ultra_orchestration_canary=True,
    )
    if args.canary_time_limit_seconds > args.time_limit_seconds:
        raise BenchmarkToolError(
            "canary wall time cannot exceed the frozen benchmark wall time"
        )

    logs = result_root / "logs"
    attempts = result_root / "attempts"
    usage_output = logs / "ultra_orchestration_canary.usage.json"
    freeze_output = logs / "ultra_orchestration_canary.freeze_check.json"
    runner_freeze_output = logs / "ultra_orchestration_canary.runner_freeze_check.json"
    invocation_output = logs / "ultra_orchestration_canary.invocation.json"
    runner_record_output = attempts / "ultra_orchestration_canary.record.json"
    raw_jsonl = attempts / "ultra_orchestration_canary.record.jsonl"
    write_json(freeze_output, freeze_check)
    runner_freeze_check = _runner_freeze_record(freeze_check)
    write_json(runner_freeze_output, runner_freeze_check)
    if codex_isolated.build_prompt(prompt, context, target) != synthetic_effective_prompt():
        raise BenchmarkToolError("synthetic canary prompt composition drifted")
    command = _runner_command(
        args,
        result_root=result_root,
        task_root=inputs,
        controlled_manifest=controlled_manifest,
        runner_freeze_check=runner_freeze_check,
        usage_output=usage_output,
        runner_record=runner_record_output,
        raw_jsonl=raw_jsonl,
        state_parent=result_root / "state",
    )
    write_json(
        invocation_output,
        {
            "schema_version": 1,
            "kind": "highambench-ultra-orchestration-canary-invocation",
            "argv": command,
            "network_evidence_role": "production_runner_marker_and_monitor",
            "submission_evidence_role": (
                "production_runner_authenticated_nested_submit_proof_boundary"
            ),
        },
    )
    try:
        completed = subprocess.run(
            command,
            cwd=args.project_root.resolve(),
            check=False,
            timeout=args.canary_time_limit_seconds + 180,
        )
    except subprocess.TimeoutExpired as error:
        raise BenchmarkToolError("Ultra orchestration canary runner timed out") from error
    if completed.returncode != 0:
        raise BenchmarkToolError(
            f"Ultra orchestration canary runner exited {completed.returncode}"
        )

    if not usage_output.is_file():
        raise BenchmarkToolError("Ultra orchestration canary produced no usage ledger")
    if not runner_record_output.is_file():
        raise BenchmarkToolError("Ultra orchestration canary produced no runner record")
    runner_record = _mapping(
        read_json(runner_record_output), "Ultra orchestration canary runner record"
    )
    agent_log = Path(str(runner_record.get("agent_log", ""))).resolve()
    validation_output = Path(str(runner_record.get("validation_log", ""))).resolve()
    accepted_candidate = Path(
        str(runner_record.get("accepted_submission_log", ""))
    ).resolve()
    boundary_record = _mapping(
        runner_record.get("ultra_submission_boundary"),
        "Ultra orchestration canary runner boundary",
    )
    barrier_artifacts = _mapping(
        boundary_record.get("artifacts"),
        "Ultra orchestration canary retained barrier artifacts",
    )
    required_runner_outputs = {
        "agent_log": agent_log,
        "raw_jsonl": raw_jsonl,
        "validation": validation_output,
        "accepted_candidate": accepted_candidate,
    }
    if any(not path.is_file() for path in required_runner_outputs.values()):
        raise BenchmarkToolError(
            "Ultra orchestration canary runner omitted a required output"
        )
    retained = {
        f"barrier_{label}": Path(
            str(_mapping(barrier_artifacts.get(label), label).get("path", ""))
        ).resolve()
        for label in ("challenge", "call", "request", "ack", "snapshot")
    }
    if any(not path.is_file() for path in retained.values()):
        raise BenchmarkToolError(
            "Ultra orchestration canary runner omitted retained barrier evidence"
        )
    usage = _mapping(read_json(usage_output), "Ultra orchestration canary usage")
    try:
        from . import run_matrix
    except ImportError:  # Direct script execution.
        import run_matrix  # type: ignore
    gate_authentication = run_matrix.authenticate_runner_provider_gate_summary(
        runner_record
    )
    outcome = validate_usage_and_log(
        usage,
        agent_log,
        token_limit=args.token_limit,
        gate_authentication=gate_authentication,
    )
    outcome["prompt_release"] = _verify_prompt_release(
        runner_record,
        usage_path=usage_output,
        request_path=retained["barrier_request"],
        artifact_root=result_root,
        wall_time_seconds=args.canary_time_limit_seconds,
    )
    agent = dict(_mapping(freeze_check.get("agent"), "canary frozen agent"))
    controls = controls_record(args.token_limit, args.canary_time_limit_seconds)
    artifacts = {
        label: {
            "path": _relative_artifact(path, result_root),
            "sha256": sha256_file(path),
        }
        for label, path in (
            ("agent_log", agent_log),
            ("usage", usage_output),
            ("freeze_check", freeze_output),
            ("runner_freeze_check", runner_freeze_output),
            ("invocation", invocation_output),
            ("common_prompt", prompt),
            ("context", context),
            ("synthetic_target", target),
            ("controlled_manifest", controlled_manifest),
            ("dependency_audit_helper", audit_helper_snapshot),
            ("runner_record", runner_record_output),
            *required_runner_outputs.items(),
            *retained.items(),
            (
                "provider_gate",
                runner.provider_gate_paths(usage_output.resolve())["final"],
            ),
        )
    }
    evidence = {
        "schema_version": 1,
        "kind": EVIDENCE_KIND,
        "status": "passed",
        "public_release": False,
        "scored": False,
        "matrix_assignment": False,
        "synthetic_input": True,
        "canary_id": CANARY_ID,
        "benchmark_id": freeze_check.get("benchmark_id"),
        "pre_canary_environment_id": freeze_check.get("environment_id"),
        "freeze_check_sha256": _canonical_sha256(freeze_check),
        "agent": agent,
        "prompt": prompt_record(),
        "artifact_root": artifact_root_relative.as_posix(),
        "controls": controls,
        "outcome": outcome,
        "artifacts": artifacts,
    }
    verify_evidence_document(
        evidence,
        project_root=args.project_root,
        expected_benchmark_id=str(freeze_check.get("benchmark_id")),
        expected_agent=agent,
        expected_token_limit=args.token_limit,
        expected_prompt_protocol=_mapping(
            freeze_check.get("prompt_protocol"), "canary production prompt protocol"
        ),
        expected_execution_components=_mapping(
            freeze_check.get("execution_components"),
            "canary production execution components",
        ),
    )
    evidence_output = result_root / "ultra_orchestration_canary_attestation.json"
    write_json(evidence_output, evidence)
    print(
        "HighamBench private Ultra orchestration canary passed: "
        f"{outcome['positive_usage_descendant_thread_count']} positive-usage "
        f"descendant(s), {outcome['thread_count']} total threads, "
        f"{outcome['total_model_tokens']} exact boundary tokens"
    )
    print(f"Attestation: {evidence_output}")
    return 0


def make_parser() -> argparse.ArgumentParser:
    try:
        from . import run_matrix
    except ImportError:  # Direct script execution.
        import run_matrix  # type: ignore

    parser = run_matrix.make_parser()
    parser.description = __doc__
    parser.add_argument(
        "--canary-time-limit-seconds",
        type=int,
        default=DEFAULT_CANARY_TIME_LIMIT_SECONDS,
    )
    parser.add_argument(
        "--verify-only",
        type=Path,
        metavar="EVIDENCE_JSON",
        help="authenticate a frozen evidence file without contacting the provider",
    )
    return parser


def _verify_only(args: argparse.Namespace) -> int:
    try:
        from . import run_matrix
    except ImportError:  # Direct script execution.
        import run_matrix  # type: ignore

    freeze = run_matrix.verify_frozen_run_environment(
        args,
        args.benchmark_root.resolve(),
        regenerating_token_control_canary=True,
        regenerating_ultra_orchestration_canary=True,
    )
    evidence = _mapping(read_json(args.verify_only), "Ultra canary evidence")
    summary = verify_evidence_document(
        evidence,
        project_root=args.project_root,
        expected_benchmark_id=str(freeze.get("benchmark_id")),
        expected_agent=_mapping(freeze.get("agent"), "frozen agent"),
        expected_token_limit=args.token_limit,
        expected_prompt_protocol=_mapping(
            freeze.get("prompt_protocol"), "frozen production prompt protocol"
        ),
        expected_execution_components=_mapping(
            freeze.get("execution_components"),
            "frozen production execution components",
        ),
    )
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    try:
        args = make_parser().parse_args(argv)
        return _verify_only(args) if args.verify_only is not None else run_canary(args)
    except (OSError, BenchmarkToolError, ValueError) as error:
        print(f"Ultra orchestration canary error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
