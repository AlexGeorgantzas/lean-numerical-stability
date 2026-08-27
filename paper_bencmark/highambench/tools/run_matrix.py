#!/usr/bin/env python3
"""Run the frozen HighamBench N/L matrix in its recorded order.

The orchestrator deliberately separates *assignments* from *attempts*.  A
SYSTEM_ERROR is kept as an incident and retried once, as required by the
benchmark specification, but only when useful work has not begun.  An Ultra
attempt that began useful work but cannot establish exact measurement is
preserved as an incident and aborts the matrix without a score or retry.  Every
other outcome becomes the single final record for that assignment.  The command
is resumable: completed assignment records are not run again unless ``--force``
is supplied.

When Slurm supplies ``SLURM_JOB_END_TIME``, the orchestrator starts a new N/L
pair only when the full worst-case pair plus a cleanup margin fits before the
allocation deadline.  An active-attempt marker prevents an unexpected mid-run
termination from becoming an unreported retry on the next invocation.
``--stop-after-paper`` provides an equally resumable intentional boundary: all
assignments through that paper are completed, and no assignment from the next
paper is started.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
from pathlib import PurePosixPath
import platform
import re
import shutil
import stat
import subprocess
import sys
import tempfile
import time
from typing import Any, Iterable, Mapping, Sequence

try:
    from .common import BenchmarkToolError, read_json, sha256_file, write_json
    from .hashes import load_manifest, verify_manifest
    from .task_tags import validate_task_source_tags
    from . import run_ultra_orchestration_canary as ultra_canary
except ImportError:  # Direct script execution.
    from common import BenchmarkToolError, read_json, sha256_file, write_json  # type: ignore
    from hashes import load_manifest, verify_manifest  # type: ignore
    from task_tags import validate_task_source_tags  # type: ignore
    import run_ultra_orchestration_canary as ultra_canary  # type: ignore


# A release manifest must cover the complete benchmark tree.  These entries are
# also named explicitly so a truncated manifest cannot silently omit a runtime
# component while still verifying the files it happens to list.
REQUIRED_RUNTIME_RELEASE_FILES = {
    "agent_prompt.md",
    "condition_prompts/L.md",
    "metadata/library_olean.json",
    "metadata/library_source.json",
    "metadata/manifest.json",
    "metadata/packages_olean.json",
    "metadata/packages_runtime.json",
    "metadata/run_order.json",
    "metadata/evidence/token_control_live_canary.json",
    "metadata/evidence/ultra_orchestration_live_canary.json",
    "tools/codex_isolated.py",
    "tools/__init__.py",
    "tools/analyze.py",
    "tools/check_construction.py",
    "tools/common.py",
    "tools/dependency_audit.lean",
    "tools/hashes.py",
    "tools/lean_isolated.py",
    "tools/manage_p01_campaign.py",
    "tools/offline_shell.c",
    "tools/preflight.py",
    "tools/provider_token_gate.py",
    "tools/promote_live_canary.py",
    "tools/render_p01_report.py",
    "tools/render_report.py",
    "tools/result_set.py",
    "tools/refresh_snapshot.py",
    "tools/run_matrix.py",
    "tools/run_token_control_canary.py",
    "tools/run_ultra_orchestration_canary.py",
    "tools/runner.py",
    "tools/task_tags.py",
    "tools/validator.py",
    "tools/tests/__init__.py",
    "tools/tests/test_analyze.py",
    "tools/tests/test_check_construction.py",
    "tools/tests/test_hashes.py",
    "tools/tests/test_isolation_adapters.py",
    "tools/tests/test_manage_p01_campaign.py",
    "tools/tests/test_preflight.py",
    "tools/tests/test_provider_token_gate.py",
    "tools/tests/test_promote_live_canary.py",
    "tools/tests/test_render_p01_report.py",
    "tools/tests/test_render_report.py",
    "tools/tests/test_result_set.py",
    "tools/tests/test_refresh_snapshot.py",
    "tools/tests/test_run_matrix.py",
    "tools/tests/test_runner.py",
    "tools/tests/test_token_control_canary.py",
    "tools/tests/test_ultra_orchestration_canary.py",
    "tools/tests/test_task_tags.py",
    "tools/tests/test_validator.py",
}
RELEASE_MANIFEST_RELATIVE = "metadata/release_files.json"
FROZEN_RELEASE_MANIFEST_PATH = "paper_bencmark/highambench/metadata/release_files.json"
FROZEN_PACKAGES_RUNTIME_MANIFEST_PATH = (
    "paper_bencmark/highambench/metadata/packages_runtime.json"
)
FROZEN_TOKEN_CANARY_PATH = (
    "paper_bencmark/highambench/metadata/evidence/token_control_live_canary.json"
)
FROZEN_ULTRA_CANARY_PATH = ultra_canary.FROZEN_EVIDENCE_PATH
PACKAGE_BASE_COMPILED_SUFFIX = ".olean"
PACKAGE_COMPILED_SUPPORT_SUFFIXES = (
    ".olean.server",
    ".olean.private",
    ".ir",
)
ENVIRONMENT_BUNDLE_DEFINITION = (
    "SHA-256 of UTF-8 canonical JSON with sorted keys and compact separators over an "
    "object containing the complete config and environment records, after removing "
    "environment_id and environment_bundle_sha256 from their top-level/frozen locations."
)
SLURM_JOB_END_TIME_ENV = "SLURM_JOB_END_TIME"
SLURM_JOB_ID_ENV = "SLURM_JOB_ID"
DEFAULT_ALLOCATION_GUARD_SECONDS = 600.0
DEFAULT_VALIDATION_COMPILE_TIMEOUT_SECONDS = 120.0
DEFAULT_VALIDATION_AUDIT_TIMEOUT_SECONDS = 120.0
DEFAULT_ACCEPTED_SUBMISSION_CLOSE_TIMEOUT_SECONDS = 5.0
DEFAULT_FORCED_TERMINATION_GRACE_SECONDS = 2.0
# Two serial hidden Lean compilations (candidate and immutable checked copy), one
# dependency audit, the accepted-boundary adapter close, and two outer-process
# termination grace windows can all occur after the provider request ends.
DEFAULT_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS = (
    2 * DEFAULT_VALIDATION_COMPILE_TIMEOUT_SECONDS
    + DEFAULT_VALIDATION_AUDIT_TIMEOUT_SECONDS
    + DEFAULT_ACCEPTED_SUBMISSION_CLOSE_TIMEOUT_SECONDS
    + 2 * DEFAULT_FORCED_TERMINATION_GRACE_SECONDS
)
CHUNK_INCOMPLETE_EXIT_CODE = 75
ACTIVE_RUN_MARKER = "active_run.json"
ACTIVE_RUN_MARKER_SCHEMA_VERSION = 2
ALLOCATION_HARDWARE_DIRECTORY = "allocation_hardware"
ALLOCATION_HARDWARE_KIND = "highambench-allocation-hardware-record"
PAIR_COMMIT_PATH = "pair_commit.json"
PAIR_COMMIT_KIND = "highambench-pair-commit"
PAIR_COMMIT_SHA256_FIELD = "pair_commit_sha256"
PAIR_COMMIT_FIELDS = {
    "schema_version",
    "kind",
    "pair_id",
    "condition_order",
    "run_ids",
    "final_records",
    "allocation_hardware",
    "freeze_check_sha256",
    "hardware_matching_policy_sha256",
    PAIR_COMMIT_SHA256_FIELD,
}
GPU_ENVIRONMENT_VARIABLES = (
    "SLURM_GPUS_ON_NODE",
    "SLURM_JOB_GPUS",
    "CUDA_VISIBLE_DEVICES",
)
MATRIX_RECORD_SHA256_FIELD = "matrix_record_sha256"
MATRIX_INCIDENT_SHA256_FIELD = "matrix_incident_sha256"
MATRIX_ATTEMPT_FIELD = "matrix_attempt"
DEFAULT_PROMPT_STARTUP_TIMEOUT_SECONDS = 120.0
CONDITION_L_PROMPT_RELATIVE = "condition_prompts/L.md"
PROMPT_PROTOCOL_VERSION = "signposted-library-v1"
FROZEN_MODEL_VERSION = "gpt-5.6-sol"
FROZEN_REASONING_EFFORT = "ultra"
ULTRA_MULTI_AGENT_VERSION = "v2"
ULTRA_MAX_CONCURRENT_THREADS_PER_SESSION = 4
EXPECTED_FAILURE_REASON_PRIORITY = (
    "TIME_LIMIT",
    "TOKEN_LIMIT",
    "NO_SUBMISSION",
    "RULE_VIOLATION",
    "SYNTAX_OR_ELAB",
    "PROOF_ERROR",
    "SYSTEM_ERROR",
)
SESSION_ISOLATION_FIELDS = {
    "ephemeral_thread_start_per_run": False,
    "fresh_codex_state_directory_per_run": True,
    "history_persistence": "none",
    "memories_feature_disabled": True,
    "normal_exit_state_cleanup": True,
    "prior_outputs_or_submissions_mounted": False,
    "state_directory_reused_across_runs": False,
    "thread_resume_or_fork_used": False,
}
PREFIX_CACHE_FIELDS = {
    "automatic_prefix_caching_may_occur": True,
    "cached_input_charged_at_full_token_weight": True,
    "cached_object": "exact-prefix prefill key/value computation, not generated output",
    "cross_run_answer_or_proof_replay": False,
    "kind": "automatic exact-input-prefix prefill computation reuse",
    "pinned_codex_disable_control_available": False,
    "semantic_history_transfer": False,
}
EXECUTION_COMPONENT_FIELDS = (
    "filesystem_adapter_sha256",
    "provider_token_gate_sha256",
    "lean_adapter_sha256",
    "offline_shell_source_sha256",
    "runner_sha256",
    "validator_sha256",
    "dependency_audit_sha256",
    "offline_shell_binary_sha256",
)
PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION = 3
PROVIDER_USAGE_FIELDS = (
    "input_tokens",
    "cached_input_tokens",
    "cache_write_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
    "total_tokens",
)
PROVIDER_USAGE_RECONCILIATION_FIELDS = {
    "schema_version",
    "provider_response_count",
    "appserver_response_count",
    "suppressed_collaboration_wait_response_count",
    "provider_usage",
    "appserver_usage",
    "suppressed_collaboration_wait_usage",
    "provider_response_ids",
    "appserver_response_ids",
    "suppressed_collaboration_wait_response_ids",
    "suppressed_collaboration_wait_evidence",
    "superseded_by_collaboration_message_response_count",
    "superseded_by_collaboration_message_usage",
    "superseded_by_collaboration_message_response_ids",
    "superseded_by_collaboration_message_evidence",
    "discarded_after_explicit_child_interrupt_response_count",
    "discarded_after_explicit_child_interrupt_usage",
    "discarded_after_explicit_child_interrupt_response_ids",
    "discarded_after_explicit_child_interrupt_evidence",
}
SUPPRESSED_COLLABORATION_WAIT_EVIDENCE_FIELDS = {
    "response_id",
    "provider_call_id",
    "thread_id",
    "turn_id",
    "successor_response_id",
    "successor_call_id",
    "agent_message_item_id",
    "agent_message_sha256",
    "agent_message_author",
    "agent_message_recipient",
    "agent_message_observed_at_unix_ns",
    "agent_message_observed_at_monotonic_ns",
}
SUPERSEDED_BY_COLLABORATION_MESSAGE_EVIDENCE_FIELDS = {
    "response_id",
    "provider_call_id",
    "thread_id",
    "turn_id",
    "successor_response_id",
    "successor_call_id",
    "collaboration_messages",
}
COLLABORATION_MESSAGE_EVIDENCE_FIELDS = {
    "item_id",
    "item_sha256",
    "author",
    "recipient",
    "observed_at_unix_ns",
    "observed_at_monotonic_ns",
}
DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_EVIDENCE_FIELDS = {
    "response_id",
    "provider_call_id",
    "thread_id",
    "turn_id",
    "interrupting_response_id",
    "interrupting_provider_call_id",
    "interrupt_function_item_id",
    "interrupt_function_call_id",
    "interrupt_function_arguments_sha256",
    "interrupt_parent_thread_id",
    "interrupt_parent_turn_id",
    "interrupted_agent_path",
    "interrupt_activity_item_sha256",
    "interrupt_output_item_id",
    "interrupt_output_item_sha256",
    "interrupt_function_observed_at_unix_ns",
    "interrupt_function_observed_at_monotonic_ns",
    "interrupt_activity_observed_at_unix_ns",
    "interrupt_activity_observed_at_monotonic_ns",
    "interrupt_output_observed_at_unix_ns",
    "interrupt_output_observed_at_monotonic_ns",
    "interrupted_turn_observed_at_unix_ns",
    "interrupted_turn_observed_at_monotonic_ns",
}
PROVIDER_GATE_PROVENANCE_INTERPRETER = Path("/usr/bin/python3.10")
PROVIDER_GATE_PROVENANCE_FLAG = "--print-transport-provenance"


def provider_token_gate_environment_record(root: Path) -> dict[str, Any]:
    """Derive the frozen gate/TLS record in the production interpreter.

    The emitter constructs an explicit TLS context but performs no DNS lookup
    or network connection.  Its subprocess starts with the same transport
    override variables removed by the runner before it launches the adapter.
    """

    gate_source = root.resolve() / "tools" / "provider_token_gate.py"
    interpreter = PROVIDER_GATE_PROVENANCE_INTERPRETER
    for path, label in (
        (gate_source, "provider-token-gate source"),
        (interpreter, "provider-token-gate provenance interpreter"),
    ):
        try:
            metadata = path.lstat()
        except OSError as error:
            raise BenchmarkToolError(f"cannot inspect {label}: {error}") from error
        if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
            raise BenchmarkToolError(f"{label} must be a regular non-symlink file")

    required_absent = tuple(
        ultra_canary.runner.PROVIDER_TRANSPORT_ENV_REQUIRED_ABSENT
    )
    environment = os.environ.copy()
    for name in required_absent:
        environment.pop(name, None)
    if any(name in environment for name in required_absent):
        raise BenchmarkToolError(
            "provider transport override survived provenance sanitization"
        )
    try:
        completed = subprocess.run(
            [str(interpreter), str(gate_source), PROVIDER_GATE_PROVENANCE_FLAG],
            cwd=root.resolve(),
            env=environment,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            timeout=30.0,
            check=False,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise BenchmarkToolError(
            f"cannot derive provider-token-gate transport provenance: {error}"
        ) from error
    if completed.returncode != 0 or completed.stderr != b"":
        stderr = completed.stderr.decode("utf-8", errors="replace").strip()
        raise BenchmarkToolError(
            "provider-token-gate transport provenance emitter failed"
            + (f": {stderr}" if stderr else "")
        )
    try:
        text = completed.stdout.decode("utf-8", errors="strict")
        value = json.loads(text)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise BenchmarkToolError(
            f"provider-token-gate transport provenance is not strict JSON: {error}"
        ) from error
    canonical = (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    )
    if text != canonical:
        raise BenchmarkToolError(
            "provider-token-gate transport provenance is not canonical JSON"
        )
    provenance = ultra_canary.runner._validate_provider_transport_provenance(
        value,
        field="frozen provider_token_gate.transport_provenance",
    )
    python_record = _mapping(
        provenance.get("python"), "provider transport Python provenance"
    )
    if (
        provenance.get("connection_factory_mode") != "explicit_tls"
        or python_record.get("executable") != str(interpreter)
        or _mapping(
            python_record.get("binary"), "provider transport Python binary"
        ).get("logical_path")
        != str(interpreter)
    ):
        raise BenchmarkToolError(
            "provider transport provenance used another interpreter or factory"
        )

    source_sha256 = sha256_file(gate_source)
    return {
        "schema_version": 2,
        "kind": "highambench-provider-token-gate-freeze",
        "protocol": ultra_canary.runner.PROVIDER_GATE_PROTOCOL,
        "implementation": {
            "name": ultra_canary.runner.PROVIDER_GATE_IMPLEMENTATION_NAME,
            "version": ultra_canary.runner.PROVIDER_GATE_IMPLEMENTATION_VERSION,
            "path": "tools/provider_token_gate.py",
            "source_sha256": source_sha256,
        },
        "model_catalog": {
            "source": "authenticated_codex_debug_models_bundled",
            "slug": FROZEN_MODEL_VERSION,
            "reasoning_effort": FROZEN_REASONING_EFFORT,
            "catalog_sha256": (
                ultra_canary.runner.FROZEN_BUNDLED_MODEL_CATALOG_SHA256
            ),
            "entry_sha256": (
                ultra_canary.runner.FROZEN_BUNDLED_MODEL_ENTRY_SHA256
            ),
            "response_bound": (
                ultra_canary.runner.PROVIDER_RESPONSE_TOKEN_BOUND
            ),
        },
        "static_configuration": {
            "strict_admission_inequality": (
                "completed_tokens + (open_request_count + 1) * "
                "response_bound < token_limit"
            ),
            "response_bound_enforcement": (
                "runtime_fail_closed_before_buffered_response_release"
            ),
            "upstream_origin": "https://chatgpt.com",
            "upstream_base_path": "/backend-api/codex",
            "loopback_only": True,
            "counted_route": "POST /responses",
            "counted_request_kinds": ["turn", "compaction"],
            "rejected_inference_routes": ["POST /responses/compact"],
            "allowed_setup_route_prefixes": [],
            "websockets_supported": False,
            "request_retries": 0,
            "stream_retries": 0,
            "request_compression": False,
            "response_compression": "identity",
            "crossing_release_policy": (
                ultra_canary.runner.PROVIDER_GATE_CROSSING_RELEASE_POLICY
            ),
            "upstream_response_contract": json.loads(
                json.dumps(
                    ultra_canary.runner.PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT,
                    sort_keys=True,
                )
            ),
            "capability_persisted": False,
            "final_artifact_mode": "0444",
        },
        "provenance_producer": {
            "interpreter": str(interpreter),
            "source_argument": "tools/provider_token_gate.py",
            "flag": PROVIDER_GATE_PROVENANCE_FLAG,
            "environment_policy": "inherit_then_remove_required_absent",
            "required_absent": list(required_absent),
            "dns_queries_performed": False,
            "network_connections_performed": False,
        },
        "transport_provenance": json.loads(
            json.dumps(provenance, sort_keys=True)
        ),
    }


def ultra_submission_barrier_record() -> dict[str, Any]:
    """Return the exact authenticated nested first-valid-proof wire contract."""

    return {
        "schema_version": ultra_canary.codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION,
        "submission_transport": (
            ultra_canary.codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT
        ),
        "tool_name": ultra_canary.codex_isolated.SUBMISSION_TOOL_NAME,
        "candidate_path": "Candidate.lean",
        "runner_owned_submission_path": "Submission.lean",
        "root_coordinator_only": True,
        "descendants_quiescent_before_submission": True,
        "outer_raw_item_type": "custom_tool_call",
        "outer_exec_name": "exec",
        "outer_exec_program": (
            ultra_canary.codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE
        ),
        "outer_exec_program_bytes": (
            ultra_canary.codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_BYTES
        ),
        "outer_exec_program_sha256": (
            ultra_canary.codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_SHA256
        ),
        **ultra_canary.codex_isolated.nested_submission_exec_yield_record(),
        "sole_model_tool_call_in_response": True,
        "outer_exec_final_raw_item": True,
        "inner_dynamic_tool_name": ultra_canary.codex_isolated.SUBMISSION_TOOL_NAME,
        "inner_dynamic_arguments": {"candidate_path": "Candidate.lean"},
        "outer_raw_item_and_call_ids_pairwise_distinct": True,
        "outer_raw_item_observed_before_inner_dynamic_call": True,
        "submission_event_order_values": [
            ultra_canary.codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE,
            ultra_canary.codex_isolated.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER,
        ],
        "submission_event_order_flags": [
            "dynamic_call_observed_before_raw_response_completed",
            "raw_response_completed_before_dynamic_call_observed",
        ],
        "submission_event_order_flags_exactly_one_true": True,
        "raw_response_completed_before_boundary_publication": True,
        "inner_dynamic_call_observed": True,
        "inner_dynamic_item_started": True,
        "inner_submit_invocation_exact": True,
        "inner_submit_only_nested_tool_call": True,
        "inner_dynamic_call_left_blocked": True,
        "inner_dynamic_tool_response_sent": False,
        "outer_exec_output_emitted": False,
        "runner_validates_immutable_candidate_snapshot": True,
        "runner_materializes_submission_after_acceptance": True,
        "direct_submission_path_forbidden": True,
        "workspace_local_module_imports_rejected": True,
        "accepted_boundary": {
            "stop_reason": "first_valid_proof",
            "drain_complete": False,
            "measurement_exact": True,
            "submission_boundary_exact": True,
            "root_turn_active": True,
            "descendants_quiescent": True,
            "later_model_response_possible": False,
        },
    }


def ultra_orchestration_record() -> dict[str, Any]:
    """Return the exact full-Ultra delegation and projection-v6 contract."""

    return {
        "automatic_task_delegation": True,
        "child_model": FROZEN_MODEL_VERSION,
        "child_model_locked": True,
        "child_reasoning_effort": FROZEN_REASONING_EFFORT,
        "child_reasoning_effort_locked": True,
        "codex_config_locks": {
            "agents.default_subagent_model": FROZEN_MODEL_VERSION,
            "agents.default_subagent_reasoning_effort": FROZEN_REASONING_EFFORT,
            "features.multi_agent_v2.expose_spawn_agent_model_overrides": False,
            "features.multi_agent_v2.max_concurrent_threads_per_session": (
                ULTRA_MAX_CONCURRENT_THREADS_PER_SESSION
            ),
            "features.multi_agent_v2.hide_spawn_agent_metadata": True,
            "features.multi_agent_v2.usage_hint_enabled": True,
            "features.multi_agent_v2.usage_hint_text": (
                ultra_canary.codex_isolated.ULTRA_FORK_USAGE_HINT
            ),
            "features.hooks": True,
        },
        "enabled": True,
        "max_concurrency_scope": (
            "root and subagent inference threads in one Codex session"
        ),
        "max_concurrent_threads_per_session": (
            ULTRA_MAX_CONCURRENT_THREADS_PER_SESSION
        ),
        "multi_agent_version": ULTRA_MULTI_AGENT_VERSION,
        "root_model": FROZEN_MODEL_VERSION,
        "root_reasoning_effort": FROZEN_REASONING_EFFORT,
        "spawn_agent_metadata_hidden": True,
        "spawn_model_override_exposed": False,
        "spawn_reasoning_effort_override_exposed": False,
        "accounting_projection_schema_version": (
            ultra_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "fork_policy": (
            ultra_canary.codex_isolated.ultra_fork_policy_static_record()
        ),
        "submission_barrier": ultra_submission_barrier_record(),
    }


def _json_argv(items: Iterable[str | Path]) -> str:
    return json.dumps([str(item) for item in items])


def _require_file(path: Path, label: str) -> Path:
    resolved = path.resolve()
    if not resolved.is_file():
        raise BenchmarkToolError(f"{label} is not a file: {resolved}")
    return resolved


def _require_dir(path: Path, label: str) -> Path:
    resolved = path.resolve()
    if not resolved.is_dir():
        raise BenchmarkToolError(f"{label} is not a directory: {resolved}")
    return resolved


def _mapping(value: Any, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise BenchmarkToolError(f"{label} must be a JSON object")
    return value


def _provider_usage_breakdown(value: Any, label: str) -> dict[str, int]:
    usage = _mapping(value, label)
    if set(usage) != set(PROVIDER_USAGE_FIELDS):
        raise BenchmarkToolError(f"{label} has a missing or extra field")
    result: dict[str, int] = {}
    for field in PROVIDER_USAGE_FIELDS:
        amount = usage.get(field)
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise BenchmarkToolError(f"{label}.{field} is not a nonnegative integer")
        result[field] = amount
    if (
        result["cached_input_tokens"] > result["input_tokens"]
        or result["cache_write_input_tokens"] > result["input_tokens"]
        or result["reasoning_output_tokens"] > result["output_tokens"]
        or result["total_tokens"]
        != result["input_tokens"] + result["output_tokens"]
    ):
        raise BenchmarkToolError(f"{label} is internally inconsistent")
    return result


def _provider_response_id_list(value: Any, label: str) -> list[str]:
    if (
        not isinstance(value, list)
        or any(not isinstance(item, str) or not item for item in value)
        or len(value) != len(set(value))
    ):
        raise BenchmarkToolError(f"{label} is not a unique response-ID sequence")
    return list(value)


def _rooted_agent_path_parts(value: Any) -> tuple[str, ...] | None:
    """Return one canonical ``/root[/child...]`` identity, if exact."""

    if not isinstance(value, str) or not value.startswith("/root"):
        return None
    parts = tuple(value.split("/")[1:])
    if (
        not parts
        or parts[0] != "root"
        or any(not part or part in {".", ".."} for part in parts)
    ):
        return None
    return parts


def _rooted_collaboration_paths_are_adjacent(author: Any, recipient: Any) -> bool:
    """Require a canonical message route between one parent and direct child."""

    author_parts = _rooted_agent_path_parts(author)
    recipient_parts = _rooted_agent_path_parts(recipient)
    return bool(
        author_parts is not None
        and recipient_parts is not None
        and (
            author_parts[:-1] == recipient_parts
            or recipient_parts[:-1] == author_parts
        )
    )


def _provider_reconciliation_thread_routes(
    value: Any,
    *,
    root_thread_id: Any,
) -> dict[str, tuple[str, str | None]]:
    """Normalize the minimum thread-tree identity needed to bind a route."""

    if not isinstance(value, Sequence) or isinstance(value, (str, bytes)):
        raise BenchmarkToolError(
            "provider usage reconciliation thread accounting is malformed"
        )
    raw_routes: dict[str, tuple[Any, str | None]] = {}
    for index, raw in enumerate(value):
        thread = _mapping(raw, f"provider reconciliation thread {index}")
        thread_id = thread.get("thread_id")
        parent_id = thread.get("parent_thread_id")
        stored_path = thread.get("agent_path")
        if (
            not isinstance(thread_id, str)
            or not thread_id
            or thread_id in raw_routes
            or (parent_id is not None and (not isinstance(parent_id, str) or not parent_id))
        ):
            raise BenchmarkToolError(
                "provider usage reconciliation thread accounting is malformed"
            )
        raw_routes[thread_id] = (stored_path, parent_id)
    if root_thread_id is None:
        root_candidates = [
            thread_id
            for thread_id, (path, parent_id) in raw_routes.items()
            if parent_id is None and path in {"root", "/root"}
        ]
        if len(root_candidates) != 1:
            raise BenchmarkToolError(
                "provider usage reconciliation root thread identity is missing"
            )
        root_thread_id = root_candidates[0]
    if not isinstance(root_thread_id, str) or not root_thread_id:
        raise BenchmarkToolError(
            "provider usage reconciliation root thread identity is missing"
        )
    routes: dict[str, tuple[str, str | None]] = {}
    for thread_id, (stored_path, parent_id) in raw_routes.items():
        agent_path = "/root" if thread_id == root_thread_id else stored_path
        if (
            _rooted_agent_path_parts(agent_path) is None
            or (
                thread_id == root_thread_id
                and stored_path not in {"root", "/root"}
            )
        ):
            raise BenchmarkToolError(
                "provider usage reconciliation thread accounting is malformed"
            )
        routes[thread_id] = (str(agent_path), parent_id)
    if root_thread_id not in routes or routes[root_thread_id][1] is not None:
        raise BenchmarkToolError(
            "provider usage reconciliation root thread is malformed"
        )
    if any(
        parent_id is not None and parent_id not in routes
        for _, parent_id in routes.values()
    ):
        raise BenchmarkToolError(
            "provider usage reconciliation thread parent is missing"
        )
    return routes


def verify_provider_usage_reconciliation(
    value: Any,
    *,
    expected_provider_usage: Mapping[str, Any] | None = None,
    expected_appserver_usage: Mapping[str, Any] | None = None,
    expected_provider_response_ids: Sequence[str] | None = None,
    expected_appserver_response_ids: Sequence[str] | None = None,
    required_suppressed_wait_count: int | None = None,
    required_superseded_collaboration_message_count: int | None = None,
    required_discarded_after_explicit_child_interrupt_count: int | None = None,
    expected_thread_accounting: Sequence[Mapping[str, Any]] | None = None,
    expected_root_thread_id: str | None = None,
    expected_appserver_response_ledger: Sequence[Mapping[str, Any]] | None = None,
) -> dict[str, Any]:
    """Verify the exact provider/app-server partition used by projection v6."""

    record = _mapping(value, "provider usage reconciliation")
    if set(record) != PROVIDER_USAGE_RECONCILIATION_FIELDS:
        raise BenchmarkToolError(
            "provider usage reconciliation has a missing or extra field"
        )
    counts: dict[str, int] = {}
    for field in (
        "provider_response_count",
        "appserver_response_count",
        "suppressed_collaboration_wait_response_count",
        "superseded_by_collaboration_message_response_count",
        "discarded_after_explicit_child_interrupt_response_count",
    ):
        amount = record.get(field)
        if not isinstance(amount, int) or isinstance(amount, bool) or amount < 0:
            raise BenchmarkToolError(
                f"provider usage reconciliation {field} is invalid"
            )
        counts[field] = amount
    if (
        record.get("schema_version")
        != PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION
        or counts["provider_response_count"]
        != counts["appserver_response_count"]
        + counts["suppressed_collaboration_wait_response_count"]
        + counts["superseded_by_collaboration_message_response_count"]
        + counts["discarded_after_explicit_child_interrupt_response_count"]
        or (
            required_suppressed_wait_count is not None
            and counts["suppressed_collaboration_wait_response_count"]
            != required_suppressed_wait_count
        )
        or (
            required_superseded_collaboration_message_count is not None
            and counts["superseded_by_collaboration_message_response_count"]
            != required_superseded_collaboration_message_count
        )
        or (
            required_discarded_after_explicit_child_interrupt_count is not None
            and counts[
                "discarded_after_explicit_child_interrupt_response_count"
            ]
            != required_discarded_after_explicit_child_interrupt_count
        )
    ):
        raise BenchmarkToolError("provider usage reconciliation counts disagree")

    provider_usage = _provider_usage_breakdown(
        record.get("provider_usage"), "provider usage reconciliation provider_usage"
    )
    appserver_usage = _provider_usage_breakdown(
        record.get("appserver_usage"), "provider usage reconciliation appserver_usage"
    )
    suppressed_usage = _provider_usage_breakdown(
        record.get("suppressed_collaboration_wait_usage"),
        "provider usage reconciliation suppressed_collaboration_wait_usage",
    )
    superseded_usage = _provider_usage_breakdown(
        record.get("superseded_by_collaboration_message_usage"),
        "provider usage reconciliation "
        "superseded_by_collaboration_message_usage",
    )
    discarded_usage = _provider_usage_breakdown(
        record.get("discarded_after_explicit_child_interrupt_usage"),
        "provider usage reconciliation "
        "discarded_after_explicit_child_interrupt_usage",
    )
    if any(
        provider_usage[field]
        != appserver_usage[field]
        + suppressed_usage[field]
        + superseded_usage[field]
        + discarded_usage[field]
        for field in PROVIDER_USAGE_FIELDS
    ):
        raise BenchmarkToolError("provider usage reconciliation token sums disagree")
    if (
        expected_provider_usage is not None
        and provider_usage != dict(expected_provider_usage)
    ):
        raise BenchmarkToolError(
            "provider usage reconciliation disagrees with provider totals"
        )
    if (
        expected_appserver_usage is not None
        and appserver_usage != dict(expected_appserver_usage)
    ):
        raise BenchmarkToolError(
            "provider usage reconciliation disagrees with app-server totals"
        )

    provider_ids = _provider_response_id_list(
        record.get("provider_response_ids"),
        "provider usage reconciliation provider_response_ids",
    )
    appserver_ids = _provider_response_id_list(
        record.get("appserver_response_ids"),
        "provider usage reconciliation appserver_response_ids",
    )
    suppressed_ids = _provider_response_id_list(
        record.get("suppressed_collaboration_wait_response_ids"),
        "provider usage reconciliation suppressed response IDs",
    )
    superseded_ids = _provider_response_id_list(
        record.get("superseded_by_collaboration_message_response_ids"),
        "provider usage reconciliation superseded response IDs",
    )
    discarded_ids = _provider_response_id_list(
        record.get("discarded_after_explicit_child_interrupt_response_ids"),
        "provider usage reconciliation discarded response IDs",
    )
    if (
        len(provider_ids) != counts["provider_response_count"]
        or len(appserver_ids) != counts["appserver_response_count"]
        or len(suppressed_ids)
        != counts["suppressed_collaboration_wait_response_count"]
        or len(superseded_ids)
        != counts["superseded_by_collaboration_message_response_count"]
        or len(discarded_ids)
        != counts["discarded_after_explicit_child_interrupt_response_count"]
        or set(appserver_ids) & set(suppressed_ids)
        or set(appserver_ids) & set(superseded_ids)
        or set(appserver_ids) & set(discarded_ids)
        or set(suppressed_ids) & set(superseded_ids)
        or set(suppressed_ids) & set(discarded_ids)
        or set(superseded_ids) & set(discarded_ids)
        or set(provider_ids)
        != (
            set(appserver_ids)
            | set(suppressed_ids)
            | set(superseded_ids)
            | set(discarded_ids)
        )
        or (
            expected_provider_response_ids is not None
            and provider_ids != list(expected_provider_response_ids)
        )
        or (
            expected_appserver_response_ids is not None
            and appserver_ids != list(expected_appserver_response_ids)
        )
    ):
        raise BenchmarkToolError("provider usage reconciliation response IDs disagree")

    raw_evidence = record.get("suppressed_collaboration_wait_evidence")
    if not isinstance(raw_evidence, list) or len(raw_evidence) != len(suppressed_ids):
        raise BenchmarkToolError(
            "provider usage reconciliation suppressed-wait evidence is incomplete"
        )
    evidence: list[dict[str, Any]] = []
    seen_calls: set[str] = set()
    seen_messages: set[str] = set()
    for index, raw in enumerate(raw_evidence):
        item = _mapping(raw, f"suppressed collaboration wait evidence {index}")
        if set(item) != SUPPRESSED_COLLABORATION_WAIT_EVIDENCE_FIELDS:
            raise BenchmarkToolError(
                "suppressed collaboration wait evidence has a missing or extra field"
            )
        string_fields = (
            "response_id",
            "provider_call_id",
            "thread_id",
            "turn_id",
            "successor_response_id",
            "successor_call_id",
            "agent_message_item_id",
            "agent_message_author",
            "agent_message_recipient",
        )
        if any(
            not isinstance(item.get(field), str) or not item.get(field)
            for field in string_fields
        ):
            raise BenchmarkToolError(
                "suppressed collaboration wait evidence has an invalid identity"
            )
        message_sha256 = item.get("agent_message_sha256")
        if (
            not isinstance(message_sha256, str)
            or re.fullmatch(r"[0-9a-f]{64}", message_sha256) is None
            or item.get("response_id") != suppressed_ids[index]
            or item.get("successor_response_id") not in set(appserver_ids)
            or provider_ids.index(str(item["response_id"]))
            >= provider_ids.index(str(item["successor_response_id"]))
            or item.get("provider_call_id") in seen_calls
            or item.get("agent_message_item_id") in seen_messages
            or item.get("agent_message_recipient") != "/root"
            or any(
                not isinstance(item.get(field), int)
                or isinstance(item.get(field), bool)
                or item.get(field) <= 0
                for field in (
                    "agent_message_observed_at_unix_ns",
                    "agent_message_observed_at_monotonic_ns",
                )
            )
        ):
            raise BenchmarkToolError(
                "suppressed collaboration wait evidence is inconsistent"
            )
        seen_calls.add(str(item["provider_call_id"]))
        seen_messages.add(str(item["agent_message_item_id"]))
        evidence.append(dict(item))

    raw_superseded_evidence = record.get(
        "superseded_by_collaboration_message_evidence"
    )
    if (
        not isinstance(raw_superseded_evidence, list)
        or len(raw_superseded_evidence) != len(superseded_ids)
    ):
        raise BenchmarkToolError(
            "provider usage reconciliation superseded-message evidence is incomplete"
        )
    thread_routes = (
        _provider_reconciliation_thread_routes(
            expected_thread_accounting,
            root_thread_id=expected_root_thread_id,
        )
        if expected_thread_accounting is not None
        else None
    )
    if expected_thread_accounting is None and expected_root_thread_id is not None:
        raise BenchmarkToolError(
            "provider usage reconciliation thread context is incomplete"
        )
    superseded_evidence: list[dict[str, Any]] = []
    seen_superseded_calls: set[str] = set()
    seen_successor_calls: set[str] = set()
    for index, raw in enumerate(raw_superseded_evidence):
        item = _mapping(raw, f"superseded collaboration response evidence {index}")
        if set(item) != SUPERSEDED_BY_COLLABORATION_MESSAGE_EVIDENCE_FIELDS:
            raise BenchmarkToolError(
                "superseded collaboration response evidence has a missing or extra field"
            )
        string_fields = (
            "response_id",
            "provider_call_id",
            "thread_id",
            "turn_id",
            "successor_response_id",
            "successor_call_id",
        )
        response_id = item.get("response_id")
        successor_response_id = item.get("successor_response_id")
        provider_call_id = item.get("provider_call_id")
        successor_call_id = item.get("successor_call_id")
        if (
            any(
                not isinstance(item.get(field), str) or not item.get(field)
                for field in string_fields
            )
            or response_id != superseded_ids[index]
            or successor_response_id not in set(provider_ids)
            or provider_ids.index(str(successor_response_id))
            <= provider_ids.index(str(response_id))
            or provider_call_id in seen_calls
            or provider_call_id in seen_superseded_calls
            or successor_call_id in seen_successor_calls
        ):
            raise BenchmarkToolError(
                "superseded collaboration response evidence is inconsistent"
            )
        raw_messages = item.get("collaboration_messages")
        if not isinstance(raw_messages, list) or not raw_messages:
            raise BenchmarkToolError(
                "superseded collaboration response lacks message evidence"
            )
        messages: list[dict[str, Any]] = []
        for message_index, raw_message in enumerate(raw_messages):
            message = _mapping(
                raw_message,
                "superseded collaboration response message "
                f"{index}:{message_index}",
            )
            if set(message) != COLLABORATION_MESSAGE_EVIDENCE_FIELDS:
                raise BenchmarkToolError(
                    "superseded collaboration message evidence has a missing or extra field"
                )
            item_id = message.get("item_id")
            digest = message.get("item_sha256")
            if (
                any(
                    not isinstance(message.get(field), str)
                    or not message.get(field)
                    for field in ("item_id", "author", "recipient")
                )
                or not isinstance(digest, str)
                or re.fullmatch(r"[0-9a-f]{64}", digest) is None
                or not _rooted_collaboration_paths_are_adjacent(
                    message.get("author"), message.get("recipient")
                )
                or item_id in seen_messages
                or any(
                    not isinstance(message.get(field), int)
                    or isinstance(message.get(field), bool)
                    or message.get(field) <= 0
                    for field in (
                        "observed_at_unix_ns",
                        "observed_at_monotonic_ns",
                    )
                )
            ):
                raise BenchmarkToolError(
                    "superseded collaboration message evidence is inconsistent"
                )
            if thread_routes is not None:
                target = thread_routes.get(str(item.get("thread_id")))
                author_thread_ids = [
                    thread_id
                    for thread_id, (path, _) in thread_routes.items()
                    if path == message.get("author")
                ]
                if (
                    target is None
                    or target[0] != message.get("recipient")
                    or len(author_thread_ids) != 1
                    or not (
                        target[1] == author_thread_ids[0]
                        or thread_routes[author_thread_ids[0]][1]
                        == item.get("thread_id")
                    )
                ):
                    raise BenchmarkToolError(
                        "superseded collaboration message route changed its thread tree"
                    )
            seen_messages.add(str(item_id))
            messages.append(dict(message))
        seen_superseded_calls.add(str(provider_call_id))
        seen_successor_calls.add(str(successor_call_id))
        copied_item = dict(item)
        copied_item["collaboration_messages"] = messages
        superseded_evidence.append(copied_item)

    raw_discarded_evidence = record.get(
        "discarded_after_explicit_child_interrupt_evidence"
    )
    if (
        not isinstance(raw_discarded_evidence, list)
        or len(raw_discarded_evidence) != len(discarded_ids)
    ):
        raise BenchmarkToolError(
            "provider usage reconciliation interrupted-discard evidence is incomplete"
        )
    if discarded_ids and thread_routes is None:
        raise BenchmarkToolError(
            "interrupted-discard evidence lacks authenticated thread context"
        )
    discarded_evidence: list[dict[str, Any]] = []
    seen_interrupt_calls: set[str] = set()
    seen_interrupt_items: set[str] = set()
    seen_interrupt_outputs: set[str] = set()
    for index, raw in enumerate(raw_discarded_evidence):
        item = _mapping(raw, f"interrupted-discard evidence {index}")
        if set(item) != DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_EVIDENCE_FIELDS:
            raise BenchmarkToolError(
                "interrupted-discard evidence has a missing or extra field"
            )
        string_fields = (
            "response_id",
            "provider_call_id",
            "thread_id",
            "turn_id",
            "interrupting_response_id",
            "interrupting_provider_call_id",
            "interrupt_function_item_id",
            "interrupt_function_call_id",
            "interrupt_parent_thread_id",
            "interrupt_parent_turn_id",
            "interrupted_agent_path",
            "interrupt_output_item_id",
        )
        digest_fields = (
            "interrupt_function_arguments_sha256",
            "interrupt_activity_item_sha256",
            "interrupt_output_item_sha256",
        )
        time_stems = (
            "interrupt_function_observed_at",
            "interrupt_activity_observed_at",
            "interrupt_output_observed_at",
            "interrupted_turn_observed_at",
        )
        unix_times = [item.get(f"{stem}_unix_ns") for stem in time_stems]
        monotonic_times = [
            item.get(f"{stem}_monotonic_ns") for stem in time_stems
        ]
        response_id = item.get("response_id")
        interrupting_response_id = item.get("interrupting_response_id")
        interrupt_call_id = item.get("interrupt_function_call_id")
        interrupt_item_id = item.get("interrupt_function_item_id")
        output_item_id = item.get("interrupt_output_item_id")
        if (
            any(
                not isinstance(item.get(field), str) or not item.get(field)
                for field in string_fields
            )
            or any(
                not isinstance(item.get(field), str)
                or re.fullmatch(r"[0-9a-f]{64}", str(item.get(field))) is None
                for field in digest_fields
            )
            or response_id != discarded_ids[index]
            or interrupting_response_id not in set(appserver_ids)
            or provider_ids.index(str(interrupting_response_id))
            >= provider_ids.index(str(response_id))
            or interrupt_call_id in seen_interrupt_calls
            or interrupt_item_id in seen_interrupt_items
            or output_item_id in seen_interrupt_outputs
            or any(
                not isinstance(value, int)
                or isinstance(value, bool)
                or value <= 0
                for value in (*unix_times, *monotonic_times)
            )
            or unix_times != sorted(unix_times)
            or monotonic_times != sorted(monotonic_times)
        ):
            raise BenchmarkToolError(
                "interrupted-discard evidence is inconsistent"
            )
        assert thread_routes is not None
        target_route = thread_routes.get(str(item.get("thread_id")))
        parent_route = thread_routes.get(str(item.get("interrupt_parent_thread_id")))
        if (
            target_route is None
            or parent_route is None
            or target_route[1] != item.get("interrupt_parent_thread_id")
            or target_route[0] != item.get("interrupted_agent_path")
            or not _rooted_collaboration_paths_are_adjacent(
                parent_route[0], target_route[0]
            )
        ):
            raise BenchmarkToolError(
                "interrupted-discard evidence changed its resolved child edge"
            )
        seen_interrupt_calls.add(str(interrupt_call_id))
        seen_interrupt_items.add(str(interrupt_item_id))
        seen_interrupt_outputs.add(str(output_item_id))
        discarded_evidence.append(dict(item))

    # Global provider order interleaves independently active thread/turn routes.
    # Authenticate supersession against the next response on the *same* route,
    # using the direct app-server ledger for direct endpoints and the three
    # non-direct evidence ledgers for the remaining provider responses.
    if superseded_evidence:
        if (
            not isinstance(expected_appserver_response_ledger, Sequence)
            or isinstance(expected_appserver_response_ledger, (str, bytes))
            or len(expected_appserver_response_ledger) != len(appserver_ids)
        ):
            raise BenchmarkToolError(
                "superseded collaboration response evidence lacks the direct "
                "app-server route ledger"
            )
        bindings: dict[str, tuple[str, str, str, str]] = {}

        def bind_response(
            response_id: Any,
            call_id: Any,
            thread_id: Any,
            turn_id: Any,
            request_kind: Any,
            *,
            label: str,
        ) -> None:
            if (
                any(
                    not isinstance(item, str) or not item
                    for item in (
                        response_id,
                        call_id,
                        thread_id,
                        turn_id,
                        request_kind,
                    )
                )
                or response_id not in set(provider_ids)
                or response_id in bindings
            ):
                raise BenchmarkToolError(
                    f"provider usage reconciliation {label} route binding is invalid"
                )
            bindings[str(response_id)] = (
                str(call_id),
                str(thread_id),
                str(turn_id),
                str(request_kind),
            )

        direct_ids: list[str] = []
        for index, raw_entry in enumerate(expected_appserver_response_ledger):
            entry = _mapping(raw_entry, f"app-server response ledger {index}")
            call = _mapping(
                entry.get("provider_gate_call"),
                f"app-server response ledger {index} provider call",
            )
            metadata = _mapping(
                call.get("request_metadata"),
                f"app-server response ledger {index} request metadata",
            )
            response_id = entry.get("response_id")
            if (
                response_id != appserver_ids[index]
                or call.get("response_id") != response_id
                or entry.get("thread_id") != metadata.get("thread_id")
                or entry.get("turn_id") != metadata.get("turn_id")
            ):
                raise BenchmarkToolError(
                    "app-server response ledger route identity is inconsistent"
                )
            bind_response(
                response_id,
                call.get("call_id"),
                metadata.get("thread_id"),
                metadata.get("turn_id"),
                metadata.get("request_kind"),
                label="direct response",
            )
            direct_ids.append(str(response_id))
        if direct_ids != appserver_ids:
            raise BenchmarkToolError(
                "app-server response ledger order disagrees with reconciliation"
            )

        for label, items in (
            ("suppressed response", evidence),
            ("superseded response", superseded_evidence),
            ("interrupted response", discarded_evidence),
        ):
            for item in items:
                bind_response(
                    item.get("response_id"),
                    item.get("provider_call_id"),
                    item.get("thread_id"),
                    item.get("turn_id"),
                    "turn",
                    label=label,
                )
        if set(bindings) != set(provider_ids) or len(
            {binding[0] for binding in bindings.values()}
        ) != len(bindings):
            raise BenchmarkToolError(
                "provider usage reconciliation route ledger is incomplete"
            )

        provider_positions = {
            response_id: index for index, response_id in enumerate(provider_ids)
        }
        superseded_by_response = {
            str(item["response_id"]): item for item in superseded_evidence
        }
        suppressed_by_response = {
            str(item["response_id"]): item for item in evidence
        }
        allowed_successors = (
            set(appserver_ids) | set(superseded_ids) | set(suppressed_ids)
        )
        for item in superseded_evidence:
            response_id = str(item["response_id"])
            successor_response_id = str(item["successor_response_id"])
            origin = bindings[response_id]
            successor = bindings.get(successor_response_id)
            origin_index = provider_positions[response_id]
            successor_index = provider_positions.get(successor_response_id, -1)
            if (
                successor is None
                or successor_response_id not in allowed_successors
                or successor_index <= origin_index
                or successor[0] != item.get("successor_call_id")
                or successor[1:] != origin[1:]
                or successor[3] != "turn"
                or any(
                    bindings[intervening][1:3] == origin[1:3]
                    for intervening in provider_ids[
                        origin_index + 1 : successor_index
                    ]
                )
            ):
                raise BenchmarkToolError(
                    "superseded collaboration response does not name the "
                    "immediate same-route successor"
                )

        # Suppressed waits are independently classified against a later
        # direct app-server response.  When one is used as the bridge in a
        # supersession chain, reauthenticate that edge from the same route
        # ledger instead of trusting only its response ID.
        for item in evidence:
            response_id = str(item["response_id"])
            successor_response_id = str(item["successor_response_id"])
            origin = bindings[response_id]
            successor = bindings.get(successor_response_id)
            origin_index = provider_positions[response_id]
            successor_index = provider_positions.get(successor_response_id, -1)
            if (
                successor is None
                or successor_response_id not in set(appserver_ids)
                or successor_index <= origin_index
                or successor[0] != item.get("successor_call_id")
                or successor[1:] != origin[1:]
                or successor[3] != "turn"
                or any(
                    intervening in set(appserver_ids)
                    and bindings[intervening][1:3] == origin[1:3]
                    for intervening in provider_ids[
                        origin_index + 1 : successor_index
                    ]
                )
            ):
                raise BenchmarkToolError(
                    "suppressed collaboration wait does not name its "
                    "earliest direct same-route successor"
                )

        for origin_id in superseded_ids:
            cursor_id = origin_id
            seen_chain: set[str] = set()
            while (
                cursor_id in superseded_by_response
                or cursor_id in suppressed_by_response
            ):
                if cursor_id in seen_chain:
                    raise BenchmarkToolError(
                        "superseded collaboration response chain is cyclic"
                    )
                seen_chain.add(cursor_id)
                edge = (
                    superseded_by_response[cursor_id]
                    if cursor_id in superseded_by_response
                    else suppressed_by_response[cursor_id]
                )
                cursor_id = str(edge["successor_response_id"])
            if cursor_id not in set(appserver_ids):
                raise BenchmarkToolError(
                    "superseded collaboration response chain has no direct end"
                )

    return {
        "schema_version": PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION,
        **counts,
        "provider_usage": provider_usage,
        "appserver_usage": appserver_usage,
        "suppressed_collaboration_wait_usage": suppressed_usage,
        "superseded_by_collaboration_message_usage": superseded_usage,
        "discarded_after_explicit_child_interrupt_usage": discarded_usage,
        "provider_response_ids": provider_ids,
        "appserver_response_ids": appserver_ids,
        "suppressed_collaboration_wait_response_ids": suppressed_ids,
        "suppressed_collaboration_wait_evidence": evidence,
        "superseded_by_collaboration_message_response_ids": superseded_ids,
        "superseded_by_collaboration_message_evidence": superseded_evidence,
        "discarded_after_explicit_child_interrupt_response_ids": discarded_ids,
        "discarded_after_explicit_child_interrupt_evidence": discarded_evidence,
    }


def _fixed_value(label: str, *values: Any) -> Any:
    """Return one nonempty value after proving all metadata copies agree."""

    if any(value is None or value == "" for value in values):
        raise BenchmarkToolError(f"frozen {label} is missing")
    first = values[0]
    if any(value != first for value in values[1:]):
        raise BenchmarkToolError(f"frozen {label} disagrees across metadata: {values!r}")
    return first


def production_freeze_bindings(
    config: Mapping[str, Any], environment: Mapping[str, Any]
) -> tuple[dict[str, Any], dict[str, str]]:
    """Return the exact stable production fields a live canary must bind."""

    frozen = _mapping(config.get("frozen_environment"), "config.frozen_environment")
    agent = _mapping(environment.get("agent"), "environment.agent")
    isolation = _mapping(environment.get("isolation"), "environment.isolation")
    prompt_protocol = _fixed_value(
        "production prompt protocol",
        frozen.get("prompt_protocol"),
        agent.get("prompt_protocol"),
    )
    if not isinstance(prompt_protocol, Mapping):
        raise BenchmarkToolError("production prompt protocol must be a JSON object")
    components: dict[str, str] = {}
    for field in EXECUTION_COMPONENT_FIELDS:
        components[field] = _sha256_value(
            isolation.get(field), f"production execution component {field}"
        )
    return _json_copy(prompt_protocol), components


def _verify_prompt_protocol(
    root: Path,
    frozen: Mapping[str, Any],
    agent: Mapping[str, Any],
    *,
    common_prompt_sha256: str,
) -> dict[str, Any]:
    configured = _mapping(
        frozen.get("prompt_protocol"),
        "config.frozen_environment.prompt_protocol",
    )
    implemented = _mapping(
        agent.get("prompt_protocol"),
        "environment.agent.prompt_protocol",
    )
    if dict(configured) != dict(implemented):
        raise BenchmarkToolError("prompt protocol disagrees across frozen metadata")
    expected_order = [
        "common_prompt",
        "condition_L_supplement_if_condition_L",
        "task_context",
        "fixed_target",
    ]
    if (
        configured.get("version") != PROMPT_PROTOCOL_VERSION
        or configured.get("composition_order") != expected_order
        or configured.get("N_receives_condition_supplement") is not False
        or configured.get("relevant_theorem_or_module_hints_supplied") is not False
    ):
        raise BenchmarkToolError("frozen prompt protocol policy is invalid")
    common = _mapping(configured.get("common_prompt"), "prompt protocol common prompt")
    common_path = root / "agent_prompt.md"
    if (
        common.get("path") != "agent_prompt.md"
        or common.get("sha256") != common_prompt_sha256
        or type(common.get("bytes")) is not int
        or common["bytes"] <= 0
        or common["bytes"] != common_path.stat().st_size
    ):
        raise BenchmarkToolError("frozen common-prompt descriptor is invalid")
    supplements = _mapping(
        configured.get("condition_supplements"),
        "prompt protocol condition supplements",
    )
    if set(supplements) != {"L"}:
        raise BenchmarkToolError("prompt protocol must contain exactly one L supplement")
    condition_l = _mapping(supplements["L"], "condition-L prompt descriptor")
    if condition_l.get("path") != CONDITION_L_PROMPT_RELATIVE:
        raise BenchmarkToolError("condition-L prompt uses the wrong frozen path")
    digest = condition_l.get("sha256")
    if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
        raise BenchmarkToolError("condition-L prompt SHA-256 is invalid")
    if type(condition_l.get("bytes")) is not int or condition_l["bytes"] <= 0:
        raise BenchmarkToolError("condition-L prompt byte count is invalid")
    condition_l_path = root / CONDITION_L_PROMPT_RELATIVE
    if condition_l_path.is_symlink():
        raise BenchmarkToolError("condition-L prompt must not be a symlink")
    _require_file(condition_l_path, "condition-L prompt")
    if (
        sha256_file(condition_l_path) != digest
        or condition_l_path.stat().st_size != condition_l["bytes"]
    ):
        raise BenchmarkToolError("condition-L prompt does not match frozen metadata")
    return json.loads(json.dumps(configured, sort_keys=True))


def _load_token_control_canary_module() -> Any:
    """Import the canonical verifier lazily to avoid its run_matrix import cycle."""

    try:
        from . import run_token_control_canary as token_canary
    except ImportError:  # Direct script execution.
        import run_token_control_canary as token_canary  # type: ignore
    return token_canary


def _authenticated_token_canary_artifact(
    project: Path,
    evidence: Mapping[str, Any],
    label: str,
) -> Path:
    """Reauthenticate one canonical token-canary artifact by its descriptor."""

    project = project.resolve()
    root_raw = evidence.get("artifact_root")
    if not isinstance(root_raw, str) or not root_raw:
        raise BenchmarkToolError("token-control canary artifact root is missing")
    root = (project / root_raw).resolve()
    try:
        root.relative_to(project)
    except ValueError as error:
        raise BenchmarkToolError(
            "token-control canary artifact root escapes project"
        ) from error
    artifacts = _mapping(evidence.get("artifacts"), "token-control canary artifacts")
    descriptor = _mapping(artifacts.get(label), f"token-control canary {label}")
    if set(descriptor) != {"path", "sha256"}:
        raise BenchmarkToolError(
            f"token-control canary {label} descriptor schema is invalid"
        )
    relative = descriptor.get("path")
    if (
        not isinstance(relative, str)
        or not relative
        or PurePosixPath(relative).is_absolute()
        or ".." in PurePosixPath(relative).parts
    ):
        raise BenchmarkToolError(f"token-control canary {label} path is invalid")
    digest = _sha256_value(
        descriptor.get("sha256"), f"token-control canary {label} SHA-256"
    )
    path = root / relative
    if path.is_symlink():
        raise BenchmarkToolError(
            f"token-control canary {label} must not be a symlink"
        )
    path = path.resolve()
    try:
        path.relative_to(root)
    except ValueError as error:
        raise BenchmarkToolError(
            f"token-control canary {label} escapes its artifact root"
        ) from error
    _require_file(path, f"token-control canary {label}")
    if sha256_file(path) != digest:
        raise BenchmarkToolError(
            f"token-control canary {label} has the wrong SHA-256"
        )
    return path


def _verify_token_canary_projection(
    value: Any,
    token_canary: Any,
) -> dict[str, Any]:
    projection = _mapping(value, "token-control canary accounting projection")
    expected_fields = {
        "accounting_projection_schema_version",
        "provider_gate_protocol",
        "provider_gate_record_sha256",
        "provider_gate_close_reason",
        "provider_gate_response_ids",
        "provider_gate_deliveries_reconciled",
        "provider_usage_reconciliation",
        "provider_gate_setup_requests_empty",
        "provider_requests_quiescent",
        "adapter_teardown_complete",
        "spawn_binding_source",
        "root_thread_id",
        "root_expected_cumulative_baseline",
        "root_cumulative_projection_status",
        "spawn_linkage_complete",
        "descendant_accounting_complete",
        "cumulative_projection_complete",
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
        "fork_policy_complete",
        "fork_policy",
        "accounting_complete",
        "root_only",
        "projection_payload_sha256",
    }
    baseline = _mapping(
        projection.get("root_expected_cumulative_baseline"),
        "token-control canary root baseline",
    )
    digest = _sha256_value(
        projection.get("projection_payload_sha256"),
        "token-control canary projection payload SHA-256",
    )
    unsigned = dict(projection)
    unsigned.pop("projection_payload_sha256", None)
    expected_policy = {
        **token_canary.codex_isolated.ultra_fork_policy_static_record(),
        "call_evidence": [],
        "complete": True,
    }
    if (
        set(projection) != expected_fields
        or projection.get("accounting_projection_schema_version")
        != token_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        or projection.get("provider_gate_protocol")
        != token_canary.runner.PROVIDER_GATE_PROTOCOL
        or not isinstance(projection.get("provider_gate_record_sha256"), str)
        or re.fullmatch(
            r"[0-9a-f]{64}", str(projection.get("provider_gate_record_sha256"))
        )
        is None
        or projection.get("provider_gate_close_reason") != "token_limit"
        or not isinstance(projection.get("provider_gate_response_ids"), list)
        or len(projection.get("provider_gate_response_ids")) != 2
        or projection.get("provider_gate_deliveries_reconciled") is not True
        or projection.get("provider_gate_setup_requests_empty") is not True
        or projection.get("provider_requests_quiescent") is not True
        or projection.get("adapter_teardown_complete") is not True
        or projection.get("spawn_binding_source") != token_canary.SPAWN_BINDING_SOURCE
        or not isinstance(projection.get("root_thread_id"), str)
        or not projection["root_thread_id"]
        or projection.get("root_cumulative_projection_status")
        not in {"missing_cumulative", "cumulative_projection_mismatch"}
        or not baseline
        or any(type(amount) is not int or amount != 0 for amount in baseline.values())
        or any(
            projection.get(field) is not True
            for field in (
                "spawn_linkage_complete",
                "descendant_accounting_complete",
                "fork_policy_complete",
                "root_only",
            )
        )
        or projection.get("cumulative_projection_complete") is not False
        or projection.get("accounting_complete") is not False
        or any(
            projection.get(field) != []
            for field in (
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
            )
        )
        or projection.get("fork_policy") != expected_policy
        or canonical_document_digest(unsigned) != digest
    ):
        raise BenchmarkToolError(
            "token-control canary lacks a root-only exact accounting projection"
        )
    reconciliation = verify_provider_usage_reconciliation(
        projection.get("provider_usage_reconciliation"),
        expected_provider_response_ids=projection.get("provider_gate_response_ids"),
        expected_appserver_response_ledger=projection.get(
            "appserver_response_ledger"
        ),
        required_suppressed_wait_count=0,
        required_superseded_collaboration_message_count=0,
        required_discarded_after_explicit_child_interrupt_count=0,
    )
    if reconciliation.get("provider_response_count") != 2:
        raise BenchmarkToolError(
            "token-control canary provider reconciliation changed its two responses"
        )
    return dict(projection)


def _verify_token_canary_prompt_release(
    value: Any,
    *,
    artifact_label_count: int,
) -> dict[str, Any]:
    release = _mapping(value, "token-control canary prompt release")
    expected_fields = {
        "schema_version",
        "protocol_version",
        "status",
        "authenticated",
        "timing_exact",
        "useful_work_basis",
        "startup_timeout_seconds",
        "startup_timeout_triggered",
        "go_minimum_release_window_seconds",
        "artifact_content_verified",
        "artifact_count",
        "artifacts",
        "canonical_encoding",
        "sealed_mode",
        "handshake_nonce",
        "root_thread_id",
        "effective_prompt_sha256",
        "effective_prompt_bytes",
        "turn_start_request_sha256",
        "turn_start_wire_verified",
        "command_binding_verified",
        "root_identity_verified",
        "ready_sha256",
        "go_sha256",
        "release_sha256",
        "measurement_time_origin",
        "released_at_monotonic_ns",
        "deadline_monotonic_ns",
        "deadline_derivation",
        "wall_time_seconds",
        "actual_stop_seconds",
        "token_crossing_within_deadline",
        "first_valid_seconds",
        "submission_boundary",
        "sanitized_provider_gate_crossing",
        "top_level_artifact_count_unchanged",
    }
    artifacts = _mapping(
        release.get("artifacts"), "token-control canary prompt artifacts"
    )
    artifact_paths: list[str] = []
    for label in ("ready", "go", "release"):
        descriptor = _mapping(
            artifacts.get(label), f"token-control canary prompt {label}"
        )
        path = descriptor.get("path")
        if (
            set(descriptor) != {"path", "file_sha256", "record_sha256"}
            or not isinstance(path, str)
            or not Path(path).is_absolute()
        ):
            raise BenchmarkToolError(
                f"token-control canary prompt {label} descriptor is invalid"
            )
        _sha256_value(
            descriptor.get("file_sha256"),
            f"token-control canary prompt {label} file SHA-256",
        )
        _sha256_value(
            descriptor.get("record_sha256"),
            f"token-control canary prompt {label} record SHA-256",
        )
        artifact_paths.append(path)
    released = release.get("released_at_monotonic_ns")
    deadline = release.get("deadline_monotonic_ns")
    wall = release.get("wall_time_seconds")
    actual_stop = release.get("actual_stop_seconds")
    if (
        set(release) != expected_fields
        or set(artifacts) != {"ready", "go", "release"}
        or len(set(artifact_paths)) != 3
        or release.get("schema_version") != 1
        or release.get("protocol_version") != "highambench-prompt-release-v1"
        or release.get("status") != "released_authenticated"
        or release.get("authenticated") is not True
        or release.get("timing_exact") is not True
        or release.get("useful_work_basis") != "authenticated_release"
        or release.get("startup_timeout_seconds")
        != DEFAULT_PROMPT_STARTUP_TIMEOUT_SECONDS
        or release.get("startup_timeout_triggered") is not False
        or release.get("go_minimum_release_window_seconds") != 5.0
        or release.get("artifact_content_verified") is not True
        or release.get("artifact_count") != 3
        or release.get("canonical_encoding")
        != "compact_sorted_key_utf8_json_newline"
        or release.get("sealed_mode") != "0444"
        or not isinstance(release.get("handshake_nonce"), str)
        or re.fullmatch(r"[0-9a-f]{64}", release["handshake_nonce"]) is None
        or not isinstance(release.get("root_thread_id"), str)
        or not release["root_thread_id"]
        or type(release.get("effective_prompt_bytes")) is not int
        or release["effective_prompt_bytes"] <= 0
        or release.get("turn_start_wire_verified") is not True
        or release.get("command_binding_verified") is not True
        or release.get("root_identity_verified") is not True
        or release.get("measurement_time_origin")
        != "RELEASED.released_at_monotonic_ns"
        or type(released) is not int
        or released <= 0
        or type(deadline) is not int
        or type(wall) is not int
        or wall <= 0
        or deadline != released + wall * 1_000_000_000
        or release.get("deadline_derivation")
        != "released_at_monotonic_ns + wall_time_seconds*1000000000"
        or not isinstance(actual_stop, (int, float))
        or isinstance(actual_stop, bool)
        or not 0 < actual_stop < wall
        or release.get("token_crossing_within_deadline") is not True
        or release.get("first_valid_seconds") is not None
        or release.get("submission_boundary") is not None
        or release.get("sanitized_provider_gate_crossing") is not True
        or release.get("top_level_artifact_count_unchanged")
        != artifact_label_count
    ):
        raise BenchmarkToolError(
            "token-control canary prompt release is not an exact gate crossing"
        )
    for field in (
        "effective_prompt_sha256",
        "turn_start_request_sha256",
        "ready_sha256",
        "go_sha256",
        "release_sha256",
    ):
        _sha256_value(release.get(field), f"token-control canary {field}")
    return dict(release)


def _verify_token_control_canary(
    project: Path,
    frozen: Mapping[str, Any],
    environment: Mapping[str, Any],
    *,
    benchmark_id: str,
    token_limit: int,
    agent_id: str,
    agent_version: str,
    model: str,
    reasoning_effort: str,
    agent_binary_sha256: str,
    prompt_protocol: Mapping[str, Any],
    execution_components: Mapping[str, Any],
) -> dict[str, Any]:
    """Authenticate the frozen synthetic token canary with its canonical verifier."""

    frozen_descriptor = _mapping(
        frozen.get("token_control_canary"),
        "config.frozen_environment.token_control_canary",
    )
    environment_descriptor = _mapping(
        environment.get("token_control_canary"),
        "environment.token_control_canary",
    )
    if dict(frozen_descriptor) != dict(environment_descriptor):
        raise BenchmarkToolError(
            "token-control canary descriptor disagrees across frozen metadata"
        )
    if (
        set(frozen_descriptor) != {"path", "sha256", "status"}
        or frozen_descriptor.get("status") != "passed"
        or frozen_descriptor.get("path") != FROZEN_TOKEN_CANARY_PATH
    ):
        raise BenchmarkToolError("token-control canary descriptor is invalid")
    expected_digest = _sha256_value(
        frozen_descriptor.get("sha256"), "token-control canary SHA-256"
    )
    project = project.resolve()
    evidence_path = (project / FROZEN_TOKEN_CANARY_PATH).resolve()
    try:
        evidence_path.relative_to(project)
    except ValueError as error:
        raise BenchmarkToolError("token-control canary path escapes project root") from error
    if evidence_path.is_symlink():
        raise BenchmarkToolError("token-control canary evidence must not be a symlink")
    _require_file(evidence_path, "token-control canary evidence")
    if sha256_file(evidence_path) != expected_digest:
        raise BenchmarkToolError("token-control canary evidence has the wrong SHA-256")
    evidence = _mapping(read_json(evidence_path), "token-control canary evidence")

    token_canary = _load_token_control_canary_module()
    if (
        token_canary.CANARY_ID
        != "TOKEN-CONTROL-SYNTHETIC-PROVIDER-GATE-V8"
        or token_canary.PROMPT_PROTOCOL
        != "synthetic-inert-sanitized-provider-gate-compaction-crossing-v8"
        or token_canary.FROZEN_EVIDENCE_PATH != FROZEN_TOKEN_CANARY_PATH
    ):
        raise BenchmarkToolError(
            "token-control canary does not implement the frozen V8 protocol"
        )
    expected_agent = {
        "id": agent_id,
        "version": agent_version,
        "binary_sha256": agent_binary_sha256,
        "model": model,
        "reasoning_effort": reasoning_effort,
        "ultra_orchestration": ultra_orchestration_record(),
    }
    summary = _mapping(
        token_canary.validate_attestation_document(
            evidence,
            project_root=project,
            expected_benchmark_id=benchmark_id,
            expected_agent=expected_agent,
            expected_frozen_token_limit=token_limit,
        ),
        "canonical token-control canary summary",
    )
    expected_summary_fields = {
        "status",
        "canary_limit_tokens",
        "first_crossing_tokens",
        "final_endpoint_tokens",
        "thread_count",
        "observed_child_thread_count",
        "response_count",
        "drain_complete",
        "provider_gate_quiescent",
        "measurement_exact",
        "synthetic_input",
        "matrix_assignment",
        "benchmark_task_bytes_used",
        "prompt_protocol",
        "prompt_release",
        "source_separation_audit_sha256",
        "accounting_projection",
        "artifacts",
    }
    labels = tuple(token_canary.ARTIFACT_LABELS)
    artifacts = _mapping(summary.get("artifacts"), "token-control canary artifacts")
    if set(artifacts) != set(labels) or len(artifacts) != len(labels):
        raise BenchmarkToolError(
            "token-control canary canonical artifact set is incomplete"
        )
    for label in labels:
        descriptor = _mapping(
            artifacts.get(label), f"authenticated token-control artifact {label}"
        )
        if (
            set(descriptor) != {"path", "sha256", "bytes"}
            or not isinstance(descriptor.get("path"), str)
            or not descriptor["path"]
            or type(descriptor.get("bytes")) is not int
            or descriptor["bytes"] <= 0
        ):
            raise BenchmarkToolError(
                f"authenticated token-control artifact {label} is invalid"
            )
        _sha256_value(
            descriptor.get("sha256"),
            f"authenticated token-control artifact {label} SHA-256",
        )
    first = summary.get("first_crossing_tokens")
    final = summary.get("final_endpoint_tokens")
    if (
        set(summary) != expected_summary_fields
        or summary.get("status") != "passed"
        or summary.get("canary_limit_tokens")
        != token_canary.DEFAULT_CANARY_TOKEN_LIMIT
        or type(first) is not int
        or type(final) is not int
        or first < token_canary.DEFAULT_CANARY_TOKEN_LIMIT
        or final != first
        or summary.get("thread_count") != 1
        or summary.get("observed_child_thread_count") != 0
        or summary.get("response_count") != 2
        or summary.get("drain_complete") is not False
        or summary.get("provider_gate_quiescent") is not True
        or summary.get("measurement_exact") is not True
        or summary.get("synthetic_input") is not True
        or summary.get("matrix_assignment") is not False
        or summary.get("benchmark_task_bytes_used") is not False
        or summary.get("prompt_protocol") != token_canary.PROMPT_PROTOCOL
    ):
        raise BenchmarkToolError(
            "token-control canary is not a root-only exact V8 gate crossing"
        )
    _sha256_value(
        summary.get("source_separation_audit_sha256"),
        "token-control canary source-separation audit SHA-256",
    )
    projection = _verify_token_canary_projection(
        summary.get("accounting_projection"), token_canary
    )
    release = _verify_token_canary_prompt_release(
        summary.get("prompt_release"), artifact_label_count=len(labels)
    )

    # The canonical verifier proves the synthetic runner freeze is derived from
    # this production freeze. Re-open the production artifact itself so matrix
    # startup also binds the stable production prompt and execution components.
    # The synthetic runner's prompt protocol intentionally differs and is not
    # compared with the production signposted-library protocol.
    production_freeze_path = _authenticated_token_canary_artifact(
        project, evidence, "freeze_check"
    )
    production_freeze = _mapping(
        read_json(production_freeze_path),
        "token-control canary production freeze check",
    )
    if production_freeze.get("prompt_protocol") != dict(prompt_protocol):
        raise BenchmarkToolError(
            "token-control canary production prompt protocol is stale"
        )
    if production_freeze.get("execution_components") != dict(execution_components):
        raise BenchmarkToolError(
            "token-control canary production execution components are stale"
        )

    checked = dict(summary)
    checked["accounting_projection"] = projection
    checked["prompt_release"] = release
    return {
        "path": FROZEN_TOKEN_CANARY_PATH,
        "sha256": expected_digest,
        **checked,
    }


def _verify_ultra_canary_prompt_release(
    value: Any,
    *,
    wall_time_seconds: int,
) -> dict[str, Any]:
    """Require the release-derived Ultra submission-publication clock."""

    release = _mapping(value, "Ultra orchestration canary prompt release")
    expected_fields = {
        "schema_version",
        "protocol_version",
        "authenticated",
        "timing_exact",
        "elapsed_clock",
        "startup_timeout_seconds",
        "artifact_count",
        "artifacts_reauthenticated",
        "released_at_monotonic_ns",
        "measurement_deadline_monotonic_ns",
        "request_published_at_monotonic_ns",
        "request_publication_timing_verified",
    }
    released = release.get("released_at_monotonic_ns")
    deadline = release.get("measurement_deadline_monotonic_ns")
    published = release.get("request_published_at_monotonic_ns")
    if (
        set(release) != expected_fields
        or release.get("schema_version") != 1
        or release.get("protocol_version") != "highambench-prompt-release-v1"
        or release.get("authenticated") is not True
        or release.get("timing_exact") is not True
        or release.get("elapsed_clock") != "CLOCK_MONOTONIC"
        or release.get("startup_timeout_seconds")
        != DEFAULT_PROMPT_STARTUP_TIMEOUT_SECONDS
        or release.get("artifact_count") != 3
        or release.get("artifacts_reauthenticated") is not True
        or type(released) is not int
        or type(deadline) is not int
        or type(published) is not int
        or released <= 0
        or deadline != released + wall_time_seconds * 1_000_000_000
        or not released <= published < deadline
        or release.get("request_publication_timing_verified") is not True
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary prompt release is unauthenticated"
        )
    return dict(release)


def _verify_ultra_orchestration_canary(
    project: Path,
    frozen: Mapping[str, Any],
    environment: Mapping[str, Any],
    *,
    benchmark_id: str,
    token_limit: int,
    agent_id: str,
    agent_version: str,
    model: str,
    reasoning_effort: str,
    agent_binary_sha256: str,
    prompt_protocol: Mapping[str, Any],
    execution_components: Mapping[str, Any],
) -> dict[str, Any]:
    """Authenticate the separate non-scored delegation/tree-ledger witness."""

    frozen_descriptor = _mapping(
        frozen.get("ultra_orchestration_canary"),
        "config.frozen_environment.ultra_orchestration_canary",
    )
    environment_descriptor = _mapping(
        environment.get("ultra_orchestration_canary"),
        "environment.ultra_orchestration_canary",
    )
    if dict(frozen_descriptor) != dict(environment_descriptor):
        raise BenchmarkToolError(
            "Ultra orchestration canary descriptor disagrees across frozen metadata"
        )
    expected_agent = {
        "id": agent_id,
        "version": agent_version,
        "binary_sha256": agent_binary_sha256,
        "model": model,
        "reasoning_effort": reasoning_effort,
        "ultra_orchestration": ultra_orchestration_record(),
    }
    summary = ultra_canary.verify_frozen_attestation(
        project,
        frozen_descriptor,
        expected_benchmark_id=benchmark_id,
        expected_agent=expected_agent,
        expected_token_limit=token_limit,
        expected_prompt_protocol=prompt_protocol,
        expected_execution_components=execution_components,
    )
    if (
        ultra_canary.CANARY_ID
        != "ULTRA-ORCHESTRATION-SUBMISSION-CANARY-V12"
        or ultra_canary.PROMPT_PROTOCOL
        != "synthetic-root-and-child-fork3-denial-fork-all-nested-submit-proof-v12"
    ):
        raise BenchmarkToolError("Ultra orchestration canary is not the V12 protocol")

    evidence_path = (project.resolve() / FROZEN_ULTRA_CANARY_PATH).resolve()
    try:
        evidence_path.relative_to(project.resolve())
    except ValueError as error:
        raise BenchmarkToolError(
            "Ultra orchestration canary evidence path escapes the project"
        ) from error
    evidence = _mapping(
        read_json(evidence_path), "Ultra orchestration canary evidence"
    )
    if (
        evidence.get("canary_id") != ultra_canary.CANARY_ID
        or evidence.get("prompt") != ultra_canary.prompt_record()
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary evidence does not use the V12 prompt protocol"
        )
    controls = _mapping(
        evidence.get("controls"), "Ultra orchestration canary controls"
    )
    wall_time_seconds = controls.get("canary_wall_time_seconds")
    if (
        not isinstance(wall_time_seconds, int)
        or isinstance(wall_time_seconds, bool)
        or wall_time_seconds <= 0
        or dict(controls)
        != ultra_canary.controls_record(token_limit, wall_time_seconds)
        or controls.get("authenticated_prompt_release_required") is not True
        or controls.get("prompt_release_protocol_version")
        != "highambench-prompt-release-v1"
        or controls.get("prompt_startup_timeout_seconds")
        != DEFAULT_PROMPT_STARTUP_TIMEOUT_SECONDS
        or controls.get("prompt_release_artifact_count") != 3
        or controls.get("release_based_deadline_required") is not True
        or controls.get("request_publication_endpoint_required") is not True
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary controls do not require projection-v6"
        )

    if (
        summary.get("path") != FROZEN_ULTRA_CANARY_PATH
        or summary.get("sha256") != frozen_descriptor.get("sha256")
        or summary.get("status") != "passed"
        or summary.get("drain_complete") is not False
        or summary.get("measurement_exact") is not True
        or summary.get("submission_boundary_exact") is not True
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary authenticated summary is incomplete"
        )
    prompt_release = _verify_ultra_canary_prompt_release(
        summary.get("prompt_release"), wall_time_seconds=wall_time_seconds
    )
    barrier = _mapping(
        summary.get("barrier"), "Ultra orchestration canary nested boundary"
    )
    dynamic_before = barrier.get(
        "dynamic_call_observed_before_raw_response_completed"
    )
    response_before = barrier.get(
        "raw_response_completed_before_dynamic_call_observed"
    )
    order = barrier.get("submission_event_order")
    captured_ns = barrier.get("captured_at_monotonic_ns")
    response_ns = barrier.get("raw_response_observed_at_monotonic_ns")
    published_ns = barrier.get("request_published_at_monotonic_ns")
    inner_started_ns = barrier.get("inner_dynamic_item_started_at_monotonic_ns")
    outer_observed_ns = barrier.get("outer_raw_item_observed_at_monotonic_ns")
    valid_order = (
        (
            dynamic_before is True
            and response_before is False
            and order
            == ultra_canary.codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
            and type(captured_ns) is int
            and type(response_ns) is int
            and captured_ns < response_ns
        )
        or (
            dynamic_before is False
            and response_before is True
            and order
            == ultra_canary.codex_isolated.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER
            and type(captured_ns) is int
            and type(response_ns) is int
            and response_ns < captured_ns
        )
    )
    if (
        barrier.get("schema_version")
        != ultra_canary.codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION
        or barrier.get("submission_transport")
        != ultra_canary.codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT
        or any(
            barrier.get(field) != expected
            for field, expected in (
                ultra_canary.codex_isolated.nested_submission_exec_yield_record().items()
            )
        )
        or not valid_order
        or type(published_ns) is not int
        or type(inner_started_ns) is not int
        or type(outer_observed_ns) is not int
        or min(captured_ns, response_ns, published_ns, inner_started_ns, outer_observed_ns)
        <= 0
        or not outer_observed_ns <= inner_started_ns <= captured_ns
        or captured_ns > published_ns
        or response_ns > published_ns
        or barrier.get("raw_response_completed_before_boundary_publication")
        is not True
        or outer_observed_ns
        < prompt_release["released_at_monotonic_ns"]
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary schema-v5 event order is inexact"
        )
    artifacts = _mapping(
        summary.get("artifacts"), "Ultra orchestration canary artifacts"
    )
    labels = tuple(ultra_canary.ARTIFACT_LABELS)
    if set(artifacts) != set(labels) or len(artifacts) != len(labels):
        raise BenchmarkToolError(
            "Ultra orchestration canary canonical artifact set is incomplete"
        )
    for label in labels:
        descriptor = _mapping(
            artifacts.get(label), f"authenticated Ultra canary artifact {label}"
        )
        if (
            set(descriptor) != {"path", "sha256", "bytes"}
            or not isinstance(descriptor.get("path"), str)
            or not descriptor["path"]
            or type(descriptor.get("bytes")) is not int
            or descriptor["bytes"] <= 0
        ):
            raise BenchmarkToolError(
                f"authenticated Ultra canary artifact {label} is invalid"
            )
        _sha256_value(
            descriptor.get("sha256"),
            f"authenticated Ultra canary artifact {label} SHA-256",
        )
    dependency_audit = _mapping(
        summary.get("dependency_audit"),
        "Ultra orchestration canary dependency audit",
    )
    if (
        set(dependency_audit)
        != {
            "complete",
            "helper_sha256",
            "command_sha256",
            "library_use",
            "library_declarations",
            "target_seen",
            "semantic_type_equal",
        }
        or dependency_audit.get("complete") is not True
        or dependency_audit.get("library_use") is not False
        or dependency_audit.get("library_declarations") != []
        or dependency_audit.get("target_seen") is not True
        or dependency_audit.get("semantic_type_equal") is not True
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary dependency audit is incomplete"
        )
    _sha256_value(
        dependency_audit.get("helper_sha256"),
        "Ultra orchestration canary dependency-audit helper SHA-256",
    )
    _sha256_value(
        dependency_audit.get("command_sha256"),
        "Ultra orchestration canary dependency-audit command SHA-256",
    )
    projection = _mapping(
        summary.get("accounting_projection"),
        "Ultra orchestration canary accounting projection",
    )
    outcome = _mapping(evidence.get("outcome"), "Ultra orchestration canary outcome")
    if (
        outcome.get("accounting_projection") != dict(projection)
        or outcome.get("prompt_release") != prompt_release
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary summary disagrees with evidence"
        )
    _verify_ultra_accounting_projection(summary, projection)
    checked = dict(summary)
    checked["prompt_release"] = prompt_release
    checked["dependency_audit"] = dict(dependency_audit)
    return checked


_ULTRA_ACCOUNTING_PROJECTION_FIELDS = {
    "accounting_projection_schema_version",
    "provider_gate_protocol",
    "provider_gate_record_sha256",
    "provider_gate_close_reason",
    "provider_gate_response_ids",
    "provider_gate_deliveries_reconciled",
    "provider_usage_reconciliation",
    "provider_gate_setup_requests_empty",
    "provider_requests_quiescent",
    "adapter_teardown_complete",
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
    "spawn_parent_response_ids",
    "pre_spawn_completed_root_response_counts",
    "raw_call_activity_id_match",
    "completed_root_response_before_spawn",
    "fork_turns_all_child_thread_count",
    "nonzero_inherited_baseline_child_thread_ids",
    "spawn_linkage_complete",
    "descendant_accounting_complete",
    "cumulative_projection_complete",
    "fork_policy_complete",
    "accounting_complete",
    "fork_policy",
    "thread_accounting",
    "projection_payload_sha256",
}
_ULTRA_FORK_POLICY_CALL_FIELDS = {
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


def _verify_ultra_fork_policy(
    projection: Mapping[str, Any],
    *,
    raw_ids: list[str],
    allowed_ids: list[str],
    blocked_ids: list[str],
) -> None:
    """Independently bind every synthetic spawn to one frozen hook decision."""

    policy = _mapping(
        projection.get("fork_policy"), "Ultra orchestration canary fork policy"
    )
    expected_static = ultra_canary.codex_isolated.ultra_fork_policy_static_record()
    if set(policy) != set(expected_static) | {"call_evidence", "complete"}:
        raise BenchmarkToolError(
            "Ultra orchestration canary fork-policy fields are not exact"
        )
    static = dict(policy)
    call_evidence = static.pop("call_evidence")
    complete = static.pop("complete")
    if static != expected_static or complete is not True:
        raise BenchmarkToolError(
            "Ultra orchestration canary fork-policy freeze is inconsistent"
        )
    if not isinstance(call_evidence, list):
        raise BenchmarkToolError(
            "Ultra orchestration canary fork policy lacks per-call evidence"
        )
    by_id: dict[str, Mapping[str, Any]] = {}
    for index, raw in enumerate(call_evidence):
        call = _mapping(raw, f"Ultra canary fork-policy call {index}")
        call_id = call.get("call_id")
        if (
            set(call) != _ULTRA_FORK_POLICY_CALL_FIELDS
            or not isinstance(call_id, str)
            or not call_id
            or call_id in by_id
        ):
            raise BenchmarkToolError(
                "Ultra orchestration canary fork-policy call is malformed"
            )
        by_id[call_id] = call
    if list(by_id) != sorted(by_id) or sorted(by_id) != raw_ids:
        raise BenchmarkToolError(
            "Ultra orchestration canary fork-policy calls are not canonical"
        )
    allowed = set(allowed_ids)
    blocked = set(blocked_ids)
    blocked_parents: set[str] = set()
    for call_id, call in by_id.items():
        if (
            not isinstance(call.get("parent_thread_id"), str)
            or not call["parent_thread_id"]
            or not isinstance(call.get("parent_turn_id"), str)
            or not call["parent_turn_id"]
            or not isinstance(call.get("parent_response_id"), str)
            or not call["parent_response_id"]
            or call.get("hook_source_path") != expected_static["source_path"]
            or call.get("hook_thread_id") != call.get("parent_thread_id")
            or call.get("hook_turn_id") != call.get("parent_turn_id")
            or not isinstance(call.get("hook_run_id"), str)
            or not call["hook_run_id"]
            or call.get("hook_started_observed") is not True
            or call.get("hook_started_count") != 1
            or call.get("hook_completed_observed") is not True
            or call.get("hook_completed_count") != 1
        ):
            raise BenchmarkToolError(
                "Ultra orchestration canary fork-policy hook binding is inexact"
            )
        if call_id in allowed:
            if (
                call.get("fork_turns") != "all"
                or call.get("fork_semantics")
                != "full_history_parent_pre_response"
                or call.get("hook_status")
                != ultra_canary.codex_isolated.ULTRA_FORK_POLICY_ALLOW_STATUS
                or call.get("decision")
                != ultra_canary.codex_isolated.ULTRA_FORK_POLICY_ALLOW_DECISION
                or call.get("feedback") not in (None, "")
                or call.get("resolution_status") != "resolved_child"
                or call.get("child_activity_observed") is not True
            ):
                raise BenchmarkToolError(
                    "Ultra orchestration canary allowed hook decision is invalid"
                )
        elif call_id in blocked:
            blocked_parents.add(str(call["parent_thread_id"]))
            if (
                call.get("fork_turns") != "3"
                or call.get("fork_semantics")
                != "unsupported_positive_turn_suffix"
                or call.get("hook_status")
                != ultra_canary.codex_isolated.ULTRA_FORK_POLICY_BLOCK_STATUS
                or call.get("decision")
                != ultra_canary.codex_isolated.ULTRA_FORK_POLICY_BLOCK_DECISION
                or call.get("feedback")
                != ultra_canary.codex_isolated.ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
                    call_id=call_id
                )
                or call.get("resolution_status")
                != ultra_canary.codex_isolated.ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS
                or call.get("child_activity_observed") is not False
            ):
                raise BenchmarkToolError(
                    "Ultra orchestration canary blocked hook decision is invalid"
                )
        else:
            raise BenchmarkToolError(
                "Ultra orchestration canary fork-policy call has no terminal decision"
            )
    if len(blocked_parents) < 2:
        raise BenchmarkToolError(
            "Ultra orchestration canary did not prove root and descendant hook denial"
        )


def _verify_ultra_accounting_projection(
    summary: Mapping[str, Any], projection: Mapping[str, Any]
) -> None:
    """Require the exact independently replayed projection-v6 gate/spawn ledger."""

    if set(projection) != _ULTRA_ACCOUNTING_PROJECTION_FIELDS:
        raise BenchmarkToolError(
            "Ultra orchestration canary projection-v6 fields are not exact"
        )
    digest = _sha256_value(
        projection.get("projection_payload_sha256"),
        "Ultra orchestration canary projection payload SHA-256",
    )
    digest_payload = dict(projection)
    digest_payload.pop("projection_payload_sha256")
    if canonical_document_digest(digest_payload) != digest:
        raise BenchmarkToolError(
            "Ultra orchestration canary projection payload SHA-256 is invalid"
        )
    if (
        projection.get("accounting_projection_schema_version")
        != ultra_canary.ACCOUNTING_PROJECTION_SCHEMA_VERSION
        or projection.get("provider_gate_protocol")
        != ultra_canary.runner.PROVIDER_GATE_PROTOCOL
        or re.fullmatch(
            r"[0-9a-f]{64}", str(projection.get("provider_gate_record_sha256"))
        )
        is None
        or projection.get("provider_gate_close_reason") != "accepted_submission"
        or not isinstance(projection.get("provider_gate_response_ids"), list)
        or not projection.get("provider_gate_response_ids")
        or projection.get("provider_gate_deliveries_reconciled") is not True
        or projection.get("provider_gate_setup_requests_empty") is not True
        or projection.get("provider_requests_quiescent") is not True
        or projection.get("adapter_teardown_complete") is not True
        or projection.get("spawn_binding_source")
        != ultra_canary.SPAWN_BINDING_SOURCE
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary has the wrong projection-v6 binding schema"
        )
    reconciliation = verify_provider_usage_reconciliation(
        projection.get("provider_usage_reconciliation"),
        expected_provider_response_ids=projection.get("provider_gate_response_ids"),
        expected_appserver_response_ledger=projection.get(
            "appserver_response_ledger"
        ),
        required_suppressed_wait_count=None,
        expected_thread_accounting=projection.get("thread_accounting"),
    )
    if reconciliation.get("provider_response_count") != summary.get("response_count"):
        raise BenchmarkToolError(
            "Ultra orchestration canary provider response count disagrees"
        )

    def sorted_unique_strings(field: str, *, nonempty: bool = False) -> list[str]:
        raw = projection.get(field)
        if (
            not isinstance(raw, list)
            or any(not isinstance(value, str) or not value for value in raw)
            or raw != sorted(set(raw))
            or (nonempty and not raw)
        ):
            raise BenchmarkToolError(
                f"Ultra orchestration canary has malformed {field}"
            )
        return raw

    raw_ids = sorted_unique_strings("raw_spawn_call_ids", nonempty=True)
    activity_ids = sorted_unique_strings("activity_spawn_call_ids", nonempty=True)
    collab_ids = sorted_unique_strings("collab_spawn_call_ids")
    resolved_ids = sorted_unique_strings("resolved_spawn_call_ids", nonempty=True)
    failed_ids = sorted_unique_strings("failed_spawn_call_ids", nonempty=True)
    blocked_ids = sorted_unique_strings(
        "policy_blocked_spawn_call_ids", nonempty=True
    )
    unresolved_ids = sorted_unique_strings("unresolved_spawn_call_ids")
    unsupported_ids = sorted_unique_strings("unsupported_spawn_call_ids")
    child_ids = sorted_unique_strings("inference_child_thread_ids", nonempty=True)
    hook_observed_ids = sorted_unique_strings(
        "hook_observed_spawn_call_ids", nonempty=True
    )
    hook_allowed_ids = sorted_unique_strings(
        "hook_allowed_spawn_call_ids", nonempty=True
    )
    hook_blocked_ids = sorted_unique_strings(
        "hook_blocked_spawn_call_ids", nonempty=True
    )
    hook_invalid_ids = sorted_unique_strings("hook_invalid_spawn_call_ids")
    inherited_child_ids = sorted_unique_strings(
        "nonzero_inherited_baseline_child_thread_ids", nonempty=True
    )
    if (
        raw_ids != sorted(set(resolved_ids) | set(failed_ids))
        or hook_observed_ids != raw_ids
        or hook_allowed_ids != resolved_ids
        or hook_blocked_ids != blocked_ids
        or blocked_ids != failed_ids
        or hook_invalid_ids != unsupported_ids
        or activity_ids != resolved_ids
        or set(collab_ids) - (set(resolved_ids) | set(failed_ids))
        or unresolved_ids
        or unsupported_ids
        or inherited_child_ids != child_ids
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary fork-policy identifier projections are incomplete"
        )
    _verify_ultra_fork_policy(
        projection,
        raw_ids=raw_ids,
        allowed_ids=resolved_ids,
        blocked_ids=blocked_ids,
    )

    spawn_parent_response_ids = _mapping(
        projection.get("spawn_parent_response_ids"),
        "Ultra canary spawn parent response ids",
    )
    pre_spawn_counts = _mapping(
        projection.get("pre_spawn_completed_root_response_counts"),
        "Ultra canary pre-spawn root response counts",
    )
    if (
        set(spawn_parent_response_ids) != set(resolved_ids)
        or set(pre_spawn_counts) != set(resolved_ids)
        or any(
            not isinstance(value, str) or not value
            for value in spawn_parent_response_ids.values()
        )
        or any(
            not isinstance(value, int)
            or isinstance(value, bool)
            or value <= 0
            for value in pre_spawn_counts.values()
        )
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary spawn parent-response projection is incomplete"
        )
    if (
        projection.get("raw_call_activity_id_match") is not True
        or projection.get("completed_root_response_before_spawn") is not True
        or projection.get("fork_turns_all_child_thread_count") != len(resolved_ids)
        or len(resolved_ids) < 1
        or projection.get("fork_policy_complete") is not True
        or any(
            projection.get(field) is not True
            for field in (
                "spawn_linkage_complete",
                "descendant_accounting_complete",
                "cumulative_projection_complete",
                "accounting_complete",
            )
        )
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary projection-v6 completeness claims are invalid"
        )

    raw_accounting = projection.get("thread_accounting")
    if not isinstance(raw_accounting, list) or not raw_accounting:
        raise BenchmarkToolError(
            "Ultra orchestration canary lacks full thread_accounting"
        )
    accounting: dict[str, Mapping[str, Any]] = {}
    for index, raw_thread in enumerate(raw_accounting):
        thread = _mapping(raw_thread, f"Ultra canary thread_accounting[{index}]")
        thread_id = thread.get("thread_id")
        if (
            not isinstance(thread_id, str)
            or not thread_id
            or thread_id in accounting
        ):
            raise BenchmarkToolError(
                "Ultra orchestration canary thread_accounting IDs are malformed"
            )
        accounting[thread_id] = thread
    if list(accounting) != sorted(accounting):
        raise BenchmarkToolError(
            "Ultra orchestration canary thread_accounting is not canonical"
        )
    if (
        set(child_ids) - set(accounting)
        or len(accounting) != len(child_ids) + 1
        or summary.get("thread_count") != len(accounting)
        or summary.get("observed_descendant_thread_count") != len(child_ids)
        or not isinstance(summary.get("positive_usage_descendant_thread_count"), int)
        or isinstance(summary.get("positive_usage_descendant_thread_count"), bool)
        or summary["positive_usage_descendant_thread_count"] < 1
    ):
        raise BenchmarkToolError(
            "Ultra orchestration canary thread_accounting does not cover its tree"
        )
    seen_spawn_ids: set[str] = set()
    for child_id in child_ids:
        child = accounting[child_id]
        spawn_call_id = child.get("spawn_call_id")
        baseline = _mapping(
            child.get("expected_cumulative_baseline"),
            f"Ultra canary child {child_id} inherited baseline",
        )
        if (
            spawn_call_id not in resolved_ids
            or not isinstance(spawn_call_id, str)
            or spawn_call_id in seen_spawn_ids
            or child.get("spawn_parent_response_id")
            != spawn_parent_response_ids[spawn_call_id]
            or child.get("spawn_fork_turns") != "all"
            or child.get("spawn_binding_status") != "resolved"
            or not isinstance(baseline.get("total_tokens"), int)
            or isinstance(baseline.get("total_tokens"), bool)
            or baseline["total_tokens"] <= 0
            or child.get("cumulative_projection_status")
            != "matched_full_projection"
            or child.get("cumulative_projection_match") is not True
            or child.get("last_cumulative")
            != child.get("expected_cumulative_projection")
            or child.get("accounting_complete") is not True
        ):
            raise BenchmarkToolError(
                "Ultra orchestration canary has invalid fork-all inherited accounting"
            )
        seen_spawn_ids.add(spawn_call_id)
    if seen_spawn_ids != set(resolved_ids):
        raise BenchmarkToolError(
            "Ultra orchestration canary thread_accounting omits a spawn"
        )


def _verify_agent_session_isolation(
    config: Mapping[str, Any], environment: Mapping[str, Any]
) -> dict[str, Any]:
    """Verify that no Codex history, proof, or writable state crosses runs."""

    configured = _mapping(config.get("isolation"), "config.isolation")
    implemented = _mapping(environment.get("isolation"), "environment.isolation")
    for field, expected in SESSION_ISOLATION_FIELDS.items():
        if configured.get(field) != expected or implemented.get(field) != expected:
            raise BenchmarkToolError(
                f"frozen agent-session isolation field {field!r} is not {expected!r}"
            )
    configured_cache = _mapping(
        configured.get("provider_prompt_prefix_cache"),
        "config.isolation.provider_prompt_prefix_cache",
    )
    implemented_cache = _mapping(
        implemented.get("provider_prompt_prefix_cache"),
        "environment.isolation.provider_prompt_prefix_cache",
    )
    if dict(configured_cache) != dict(implemented_cache):
        raise BenchmarkToolError(
            "provider prompt-prefix cache semantics disagree across frozen metadata"
        )
    for field, expected in PREFIX_CACHE_FIELDS.items():
        if configured_cache.get(field) != expected:
            raise BenchmarkToolError(
                f"frozen prompt-prefix cache field {field!r} is not {expected!r}"
            )
    return {
        "ephemeral_thread": False,
        "fresh_state_directory": True,
        "memories_disabled": True,
        "resume_or_fork_used": False,
        "prior_outputs_or_submissions_mounted": False,
        "state_directory_reused": False,
        "cached_input_charged_at_full_token_weight": True,
        "cached_input_replays_prior_output": False,
    }


def environment_bundle_digest(
    config: Mapping[str, Any], environment: Mapping[str, Any]
) -> str:
    """Compute the non-circular canonical environment/configuration digest."""

    config_copy = json.loads(json.dumps(config))
    environment_copy = json.loads(json.dumps(environment))
    frozen = config_copy.get("frozen_environment")
    if isinstance(frozen, dict):
        frozen.pop("environment_id", None)
        frozen.pop("environment_bundle_sha256", None)
    environment_copy.pop("environment_id", None)
    environment_copy.pop("environment_bundle_sha256", None)
    payload = {"config": config_copy, "environment": environment_copy}
    canonical = json.dumps(
        payload, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(canonical).hexdigest()


def canonical_document_digest(value: Mapping[str, Any]) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _validate_hardware_matching_policy(value: Any, label: str) -> dict[str, Any]:
    policy = _mapping(value, label)
    if dict(policy) != HARDWARE_MATCHING_POLICY:
        raise BenchmarkToolError(
            f"{label} does not exactly match the implemented paired-hardware policy"
        )
    return _json_copy(policy)


def _provider_gate_without_node_local_hosts(
    value: Mapping[str, Any], *, label: str
) -> dict[str, Any]:
    """Normalize only the policy-authorized node-local ``/etc/hosts`` record."""

    gate = _json_copy(value)
    try:
        transport = gate["transport_provenance"]
        ultra_canary.runner._validate_provider_transport_provenance(
            transport, field=f"{label}.transport_provenance"
        )
        resolver = transport["resolver"]
        hosts_file = resolver["hosts_file"]
    except (KeyError, TypeError) as error:
        raise BenchmarkToolError(
            f"{label} has no provider transport resolver hosts-file provenance"
        ) from error
    if not isinstance(hosts_file, dict) or hosts_file.get("logical_path") != "/etc/hosts":
        raise BenchmarkToolError(
            f"{label} provider transport hosts-file provenance is invalid"
        )
    resolver["hosts_file"] = {"policy_normalized_path": "/etc/hosts"}
    return gate


def _verify_host_against_pair_policy(
    reference: Mapping[str, Any], actual: Mapping[str, Any], *, label: str
) -> None:
    if set(reference) != _HOST_CLASS_FIELDS or set(actual) != _HOST_CLASS_FIELDS:
        raise BenchmarkToolError(
            f"{label} host-class fields do not exactly match the paired-hardware schema"
        )
    for field in _PAIR_POLICY_EXACT_HOST_FIELDS:
        if actual.get(field) != reference.get(field):
            raise BenchmarkToolError(
                f"{label} invariant host field {field}={actual.get(field)!r} "
                f"does not match frozen {reference.get(field)!r}"
            )


def verify_pair_policy_compatible_freeze_checks(
    reference: Mapping[str, Any], candidate: Mapping[str, Any]
) -> None:
    """Authenticate a historical allocation freeze under the pair-local policy.

    Everything remains byte-for-byte frozen except the explicitly enumerated
    CPU identity/visible-memory fields and the node-local ``/etc/hosts`` file
    descriptor.  Both values stay fully recorded in the candidate freeze.
    """

    for value, label in ((reference, "reference freeze"), (candidate, "candidate freeze")):
        if (
            value.get("schema_version") != 1
            or value.get("kind") != "highambench-frozen-run-verification"
            or value.get("ok") is not True
        ):
            raise BenchmarkToolError(f"{label} is not a successful frozen-run verification")
        _validate_hardware_matching_policy(
            value.get("hardware_matching_policy"),
            f"{label}.hardware_matching_policy",
        )
    reference_host = _mapping(reference.get("host_class"), "reference freeze host_class")
    candidate_host = _mapping(candidate.get("host_class"), "candidate freeze host_class")
    _verify_host_against_pair_policy(
        reference_host, candidate_host, label="candidate freeze"
    )
    reference_gate = _mapping(
        reference.get("provider_token_gate"), "reference freeze provider_token_gate"
    )
    candidate_gate = _mapping(
        candidate.get("provider_token_gate"), "candidate freeze provider_token_gate"
    )
    reference_copy = _json_copy(reference)
    candidate_copy = _json_copy(candidate)
    reference_copy["host_class"] = {
        field: reference_host[field] for field in sorted(_PAIR_POLICY_EXACT_HOST_FIELDS)
    }
    candidate_copy["host_class"] = {
        field: candidate_host[field] for field in sorted(_PAIR_POLICY_EXACT_HOST_FIELDS)
    }
    reference_copy["provider_token_gate"] = _provider_gate_without_node_local_hosts(
        reference_gate, label="reference freeze"
    )
    candidate_copy["provider_token_gate"] = _provider_gate_without_node_local_hosts(
        candidate_gate, label="candidate freeze"
    )
    if candidate_copy != reference_copy:
        raise BenchmarkToolError(
            "candidate freeze differs outside the paired-hardware policy allowlist"
        )


def _nonempty_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise BenchmarkToolError(f"{label} must be a nonempty string")
    return value


def _positive_int(value: Any, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value <= 0:
        raise BenchmarkToolError(f"{label} must be a positive integer")
    return value


def _sha256_value(value: Any, label: str) -> str:
    digest = _nonempty_string(value, label)
    if not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise BenchmarkToolError(f"{label} must be a lowercase SHA-256 digest")
    return digest


_HOST_CLASS_FIELDS = {
    "kernel",
    "virtualization",
    "cpu_vendor",
    "cpu_family",
    "cpu_model",
    "cpu_stepping",
    "processor",
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
}
_PAIR_POLICY_EXACT_HOST_FIELDS = {
    "kernel",
    "virtualization",
    "online_logical_cpus",
    "allocated_physical_cores",
    "allocated_sockets",
    "allocated_threads_per_core",
    "allocation_memory_limit_bytes",
    "slurm_num_nodes",
    "slurm_num_cpus",
    "slurm_num_tasks",
    "slurm_cpus_per_task",
    "slurm_allocated_memory_bytes",
}
_PAIR_POLICY_VARIABLE_HOST_FIELDS = _HOST_CLASS_FIELDS - _PAIR_POLICY_EXACT_HOST_FIELDS
HARDWARE_MATCHING_POLICY: dict[str, Any] = {
    "schema_version": 1,
    "kind": "highambench-paired-hardware-policy",
    "scope": "within_pair",
    "vetted_nodes": ["watgpu108", "watgpu508", "watgpu808"],
    "pair_identity": {
        "required_conditions": ["N", "L"],
        "same_authenticated_allocation_descriptor": True,
        "same_slurm_job_id": True,
        "checkpoint_unit": "complete_pair",
    },
    "cross_pair": {
        "allocation_may_differ": True,
        "host_class_may_differ": True,
    },
    "frozen_host_class": {
        "role": "reference_and_required_invariants",
        "exact_fields": sorted(_PAIR_POLICY_EXACT_HOST_FIELDS),
        "variable_fields": sorted(_PAIR_POLICY_VARIABLE_HOST_FIELDS),
    },
    "provider_transport": {
        "baseline_comparison": "exact_except_allowed_paths",
        "allowed_variable_paths": [
            "transport_provenance.resolver.hosts_file",
        ],
        "exact_within_pair": True,
    },
}
_ALLOCATION_HARDWARE_RECORD_FIELDS = {
    "schema_version",
    "kind",
    "job_id",
    "hostname",
    "measurement_environment",
    "hardware_matching_policy",
    "host_class",
    "host_class_sha256",
    "provider_transport_provenance",
    "provider_transport_provenance_sha256",
    "host",
    "allocation",
    "slurm",
    "scheduler_sharing",
    "record_sha256",
}
_ALLOCATION_HARDWARE_DESCRIPTOR_FIELDS = {
    "path",
    "sha256",
    "record_sha256",
    "job_id",
}


def _json_copy(value: Any) -> Any:
    """Return a JSON-only deep copy suitable for an authenticated record."""

    return json.loads(json.dumps(value, sort_keys=True, ensure_ascii=False))


def _allocation_hardware_record_payload(
    freeze_check: Mapping[str, Any],
    *,
    job_id: str,
    hostname: str,
    cpu_affinity_logical_cpus: Iterable[int],
    scheduler_sharing: Mapping[str, Any],
    slurm_gpu_provenance: Mapping[str, Any],
) -> dict[str, Any]:
    """Build the non-self-hashed portion of one deterministic allocation record."""

    if re.fullmatch(r"[0-9]+", job_id) is None:
        raise BenchmarkToolError(f"invalid {SLURM_JOB_ID_ENV}: {job_id!r}")
    hostname = _nonempty_string(hostname, "allocation hostname")
    if hostname not in HARDWARE_MATCHING_POLICY["vetted_nodes"]:
        raise BenchmarkToolError(
            f"allocation hostname {hostname!r} is not a vetted benchmark node"
        )
    if freeze_check.get("kind") != "highambench-frozen-run-verification":
        raise BenchmarkToolError("allocation hardware record requires a frozen run verification")
    if freeze_check.get("ok") is not True:
        raise BenchmarkToolError("allocation hardware record requires a successful freeze check")
    environment_id = _nonempty_string(
        freeze_check.get("environment_id"), "freeze-check environment_id"
    )
    environment_bundle_sha256 = _sha256_value(
        freeze_check.get("environment_bundle_sha256"),
        "freeze-check environment_bundle_sha256",
    )
    release = _mapping(
        freeze_check.get("release_manifest"), "freeze-check release_manifest"
    )
    release_manifest_sha256 = _sha256_value(
        release.get("sha256"), "freeze-check release manifest SHA-256"
    )
    host_class = _mapping(freeze_check.get("host_class"), "freeze-check host_class")
    if set(host_class) != _HOST_CLASS_FIELDS:
        raise BenchmarkToolError(
            "freeze-check host_class fields are not exact for an allocation record: "
            f"extra={sorted(set(host_class) - _HOST_CLASS_FIELDS)}, "
            f"missing={sorted(_HOST_CLASS_FIELDS - set(host_class))}"
        )
    host_class_copy = _json_copy(host_class)
    policy = _validate_hardware_matching_policy(
        freeze_check.get("hardware_matching_policy"),
        "freeze-check hardware_matching_policy",
    )
    provider_gate = _mapping(
        freeze_check.get("provider_token_gate"), "freeze-check provider_token_gate"
    )
    transport_provenance = _mapping(
        provider_gate.get("transport_provenance"),
        "freeze-check provider_token_gate.transport_provenance",
    )
    # This also requires an exact, factual /etc/hosts descriptor while retaining
    # the complete node-local value in the allocation record.
    _provider_gate_without_node_local_hosts(
        provider_gate, label="freeze-check provider-token-gate"
    )
    try:
        raw_cpu_affinity = list(cpu_affinity_logical_cpus)
    except TypeError as error:
        raise BenchmarkToolError("allocation CPU affinity is not a list of integers") from error
    if (
        not raw_cpu_affinity
        or any(
            isinstance(cpu, bool) or not isinstance(cpu, int) or cpu < 0
            for cpu in raw_cpu_affinity
        )
        or len(set(raw_cpu_affinity)) != len(raw_cpu_affinity)
        or len(raw_cpu_affinity) != host_class_copy["online_logical_cpus"]
    ):
        raise BenchmarkToolError(
            "allocation CPU affinity is not an exact logical-CPU set matching host_class"
        )
    cpu_affinity = sorted(raw_cpu_affinity)
    scheduler_copy = _json_copy(scheduler_sharing)
    required_scheduler_fields = {
        "partition",
        "job_oversubscribe",
        "partition_oversubscribe",
        "node_list",
        "exclusive",
        "sharing_policy",
        "dynamic_co_tenant_count_recorded",
    }
    if set(scheduler_copy) != required_scheduler_fields:
        raise BenchmarkToolError("scheduler-sharing provenance fields are not exact")
    if (
        scheduler_copy["exclusive"] is not False
        or scheduler_copy["sharing_policy"] != "partition_forced_oversubscription"
        or scheduler_copy["dynamic_co_tenant_count_recorded"] is not False
        or scheduler_copy["job_oversubscribe"] != "OK"
        or not str(scheduler_copy["partition_oversubscribe"]).startswith("FORCE:")
        or scheduler_copy["node_list"] != hostname
    ):
        raise BenchmarkToolError(
            "matched allocation must record factual forced sharing and exclusive=false"
        )
    gpu_provenance = _validated_slurm_gpu_provenance(slurm_gpu_provenance)
    return {
        "schema_version": 2,
        "kind": ALLOCATION_HARDWARE_KIND,
        "job_id": job_id,
        "hostname": hostname,
        "measurement_environment": {
            "environment_id": environment_id,
            "environment_bundle_sha256": environment_bundle_sha256,
            "release_manifest_sha256": release_manifest_sha256,
            "freeze_check_sha256": canonical_document_digest(freeze_check),
        },
        "hardware_matching_policy": policy,
        # Retaining the exact verified structure makes future schema changes
        # fail closed.  The three normalized views below make the host,
        # process allocation, and scheduler evidence explicit to renderers.
        "host_class": host_class_copy,
        "host_class_sha256": canonical_document_digest(host_class_copy),
        "provider_transport_provenance": _json_copy(transport_provenance),
        "provider_transport_provenance_sha256": canonical_document_digest(
            transport_provenance
        ),
        "host": {
            "hostname": hostname,
            "kernel": host_class_copy["kernel"],
            "virtualization": host_class_copy["virtualization"],
            "cpu_vendor": host_class_copy["cpu_vendor"],
            "processor": host_class_copy["processor"],
            "cpu_family": host_class_copy["cpu_family"],
            "cpu_model": host_class_copy["cpu_model"],
            "cpu_stepping": host_class_copy["cpu_stepping"],
            "benchmark_process_visible_memory_bytes": host_class_copy[
                "visible_memory_bytes"
            ],
        },
        "allocation": {
            "cpu_affinity_logical_cpus": cpu_affinity,
            "online_logical_cpus": host_class_copy["online_logical_cpus"],
            "allocated_physical_cores": host_class_copy[
                "allocated_physical_cores"
            ],
            "allocated_sockets": host_class_copy["allocated_sockets"],
            "allocated_threads_per_core": host_class_copy[
                "allocated_threads_per_core"
            ],
            "cgroup_memory_limit_bytes": host_class_copy[
                "allocation_memory_limit_bytes"
            ],
        },
        "slurm": {
            "job_id": job_id,
            "node_list": scheduler_copy["node_list"],
            "num_nodes": host_class_copy["slurm_num_nodes"],
            "num_cpus": host_class_copy["slurm_num_cpus"],
            "num_tasks": host_class_copy["slurm_num_tasks"],
            "cpus_per_task": host_class_copy["slurm_cpus_per_task"],
            "allocated_memory_bytes": host_class_copy[
                "slurm_allocated_memory_bytes"
            ],
            "alloc_tres": gpu_provenance["alloc_tres"],
            "allocated_gpu_count": gpu_provenance["allocated_gpu_count"],
            "gpu_environment": gpu_provenance["gpu_environment"],
        },
        "scheduler_sharing": scheduler_copy,
    }


def allocation_hardware_record_digest(record: Mapping[str, Any]) -> str:
    """Return the canonical self-hash after removing only ``record_sha256``."""

    payload = dict(record)
    payload.pop("record_sha256", None)
    return canonical_document_digest(payload)


def _validate_allocation_hardware_record(
    record: Mapping[str, Any],
    freeze_check: Mapping[str, Any],
    *,
    expected_job_id: str | None = None,
    expected_hostname: str | None = None,
    expected_cpu_affinity_logical_cpus: Iterable[int] | None = None,
    expected_scheduler_sharing: Mapping[str, Any] | None = None,
    expected_slurm_gpu_provenance: Mapping[str, Any] | None = None,
) -> None:
    """Strictly validate a current or historical matched-host allocation record."""

    if set(record) != _ALLOCATION_HARDWARE_RECORD_FIELDS:
        raise BenchmarkToolError(
            "allocation hardware record fields are not exact: "
            f"extra={sorted(set(record) - _ALLOCATION_HARDWARE_RECORD_FIELDS)}, "
            f"missing={sorted(_ALLOCATION_HARDWARE_RECORD_FIELDS - set(record))}"
        )
    job_id = _nonempty_string(record.get("job_id"), "hardware record job_id")
    hostname = _nonempty_string(record.get("hostname"), "hardware record hostname")
    if hostname not in HARDWARE_MATCHING_POLICY["vetted_nodes"]:
        raise BenchmarkToolError(
            f"hardware record hostname {hostname!r} is not a vetted benchmark node"
        )
    if expected_job_id is not None and job_id != expected_job_id:
        raise BenchmarkToolError(
            f"hardware record job_id {job_id!r} does not match current {expected_job_id!r}"
        )
    if expected_hostname is not None and hostname != expected_hostname:
        raise BenchmarkToolError(
            "hardware record hostname "
            f"{hostname!r} does not match current {expected_hostname!r}"
        )
    allocation = _mapping(record.get("allocation"), "hardware record allocation")
    raw_cpu_affinity = allocation.get("cpu_affinity_logical_cpus")
    if not isinstance(raw_cpu_affinity, list):
        raise BenchmarkToolError("hardware record has no exact CPU-affinity list")
    scheduler_sharing = _mapping(
        record.get("scheduler_sharing"), "hardware record scheduler_sharing"
    )
    slurm = _mapping(record.get("slurm"), "hardware record slurm provenance")
    slurm_gpu_provenance = {
        "alloc_tres": slurm.get("alloc_tres"),
        "allocated_gpu_count": slurm.get("allocated_gpu_count"),
        "gpu_environment": slurm.get("gpu_environment"),
    }
    if (
        expected_cpu_affinity_logical_cpus is not None
        and raw_cpu_affinity != sorted(set(expected_cpu_affinity_logical_cpus))
    ):
        raise BenchmarkToolError("hardware record CPU affinity is stale")
    if (
        expected_scheduler_sharing is not None
        and dict(scheduler_sharing) != dict(expected_scheduler_sharing)
    ):
        raise BenchmarkToolError("hardware record scheduler-sharing provenance is stale")
    if (
        expected_slurm_gpu_provenance is not None
        and slurm_gpu_provenance
        != _validated_slurm_gpu_provenance(expected_slurm_gpu_provenance)
    ):
        raise BenchmarkToolError("hardware record Slurm GPU provenance is stale")
    expected = _allocation_hardware_record_payload(
        freeze_check,
        job_id=job_id,
        hostname=hostname,
        cpu_affinity_logical_cpus=raw_cpu_affinity,
        scheduler_sharing=scheduler_sharing,
        slurm_gpu_provenance=slurm_gpu_provenance,
    )
    expected["record_sha256"] = canonical_document_digest(expected)
    stored_digest = _sha256_value(
        record.get("record_sha256"), "allocation hardware record self-hash"
    )
    if stored_digest != allocation_hardware_record_digest(record):
        raise BenchmarkToolError("allocation hardware record self-hash is invalid")
    if dict(record) != expected:
        raise BenchmarkToolError(
            "allocation hardware record is stale or differs from the verified allocation"
        )


def _allocation_hardware_descriptor(
    results_root: Path, path: Path, record: Mapping[str, Any]
) -> dict[str, str]:
    try:
        relative = path.resolve().relative_to(results_root.resolve()).as_posix()
    except ValueError as error:
        raise BenchmarkToolError("allocation hardware record escapes results root") from error
    return {
        "path": relative,
        "sha256": sha256_file(path),
        "record_sha256": _sha256_value(
            record.get("record_sha256"), "allocation hardware record self-hash"
        ),
        "job_id": _nonempty_string(record.get("job_id"), "hardware record job_id"),
    }


def verify_allocation_hardware_descriptor(
    results_root: Path,
    descriptor: Mapping[str, Any],
    freeze_check: Mapping[str, Any],
) -> dict[str, Any]:
    """Verify descriptor, file bytes, self-hash, and frozen provenance together."""

    if set(descriptor) != _ALLOCATION_HARDWARE_DESCRIPTOR_FIELDS:
        raise BenchmarkToolError("allocation hardware descriptor fields are not exact")
    job_id = _nonempty_string(descriptor.get("job_id"), "hardware descriptor job_id")
    if re.fullmatch(r"[0-9]+", job_id) is None:
        raise BenchmarkToolError("allocation hardware descriptor has an invalid job_id")
    relative = _nonempty_string(descriptor.get("path"), "hardware descriptor path")
    if relative != f"{ALLOCATION_HARDWARE_DIRECTORY}/slurm-{job_id}.json":
        raise BenchmarkToolError("allocation hardware descriptor path/job_id mismatch")
    relative_path = PurePosixPath(relative)
    if relative_path.is_absolute() or any(
        part in ("", ".", "..") for part in relative_path.parts
    ):
        raise BenchmarkToolError("allocation hardware descriptor path is unsafe")
    root = results_root.resolve()
    path = (root / Path(*relative_path.parts)).resolve()
    try:
        path.relative_to(root)
    except ValueError as error:
        raise BenchmarkToolError("allocation hardware descriptor escapes results root") from error
    if path.is_symlink() or not path.is_file():
        raise BenchmarkToolError(f"allocation hardware record is missing or a symlink: {path}")
    if sha256_file(path) != _sha256_value(
        descriptor.get("sha256"), "allocation hardware descriptor file SHA-256"
    ):
        raise BenchmarkToolError("allocation hardware descriptor file SHA-256 is invalid")
    record = _mapping(read_json(path), f"allocation hardware record {path}")
    _validate_allocation_hardware_record(record, freeze_check)
    if record.get("record_sha256") != _sha256_value(
        descriptor.get("record_sha256"), "allocation hardware descriptor record SHA-256"
    ):
        raise BenchmarkToolError("allocation hardware descriptor self-hash is stale")
    if record.get("job_id") != job_id:
        raise BenchmarkToolError("allocation hardware descriptor job_id is stale")
    return dict(record)


def create_or_verify_allocation_hardware_record(
    results_root: Path, freeze_check: Mapping[str, Any]
) -> dict[str, str]:
    """Create once, or strictly verify, this Slurm allocation's hardware record."""

    job_id = os.environ.get(SLURM_JOB_ID_ENV, "").strip()
    if re.fullmatch(r"[0-9]+", job_id) is None:
        raise BenchmarkToolError(
            f"{SLURM_JOB_ID_ENV} is required to authenticate the allocation hardware record"
        )
    hostname = _nonempty_string(platform.node().strip(), "allocation hostname")
    cpu_affinity = _current_cpu_affinity()
    scheduler_sharing = _slurm_scheduler_sharing(job_id)
    slurm_gpu_provenance = _slurm_gpu_provenance(job_id)
    expected = _allocation_hardware_record_payload(
        freeze_check,
        job_id=job_id,
        hostname=hostname,
        cpu_affinity_logical_cpus=cpu_affinity,
        scheduler_sharing=scheduler_sharing,
        slurm_gpu_provenance=slurm_gpu_provenance,
    )
    expected["record_sha256"] = canonical_document_digest(expected)

    root = results_root.resolve()
    directory = root / ALLOCATION_HARDWARE_DIRECTORY
    if directory.is_symlink():
        raise BenchmarkToolError("allocation_hardware directory must not be a symlink")
    directory.mkdir(parents=True, exist_ok=True)
    path = directory / f"slurm-{job_id}.json"
    if path.is_symlink():
        raise BenchmarkToolError("allocation hardware record must not be a symlink")
    if path.exists():
        if not path.is_file():
            raise BenchmarkToolError(f"allocation hardware record is not a file: {path}")
        existing = _mapping(read_json(path), f"allocation hardware record {path}")
        _validate_allocation_hardware_record(
            existing,
            freeze_check,
            expected_job_id=job_id,
            expected_hostname=hostname,
            expected_cpu_affinity_logical_cpus=cpu_affinity,
            expected_scheduler_sharing=scheduler_sharing,
            expected_slurm_gpu_provenance=slurm_gpu_provenance,
        )
        if dict(existing) != expected:
            raise BenchmarkToolError(
                "existing allocation hardware record is stale or non-idempotent"
            )
    else:
        write_json(path, expected)

    record = _mapping(read_json(path), f"allocation hardware record {path}")
    _validate_allocation_hardware_record(
        record,
        freeze_check,
        expected_job_id=job_id,
        expected_hostname=hostname,
        expected_cpu_affinity_logical_cpus=cpu_affinity,
        expected_scheduler_sharing=scheduler_sharing,
        expected_slurm_gpu_provenance=slurm_gpu_provenance,
    )
    descriptor = _allocation_hardware_descriptor(root, path, record)
    verify_allocation_hardware_descriptor(root, descriptor, freeze_check)
    return descriptor


def _bind_allocation_hardware(
    record: dict[str, Any], descriptor: Mapping[str, Any]
) -> None:
    """Attach one exact allocation descriptor without replacing prior provenance."""

    existing = record.get("allocation_hardware")
    descriptor_copy = _json_copy(descriptor)
    if existing is not None and existing != descriptor_copy:
        raise BenchmarkToolError(
            "runner record already contains a different allocation hardware descriptor"
        )
    record["allocation_hardware"] = descriptor_copy


def matrix_record_digest(record: Mapping[str, Any]) -> str:
    """Hash canonical JSON after removing only the matrix self-hash field."""

    payload = dict(record)
    payload.pop(MATRIX_RECORD_SHA256_FIELD, None)
    return canonical_document_digest(payload)


def _bind_matrix_attempt(record: dict[str, Any], attempt: int) -> None:
    """Bind the hosted-attempt number without replacing conflicting provenance."""

    if isinstance(attempt, bool) or attempt not in (1, 2):
        raise BenchmarkToolError("matrix attempt must be 1 or 2")
    if MATRIX_ATTEMPT_FIELD in record and record[MATRIX_ATTEMPT_FIELD] != attempt:
        raise BenchmarkToolError("runner record already contains a different matrix attempt")
    record[MATRIX_ATTEMPT_FIELD] = attempt


def _bind_matrix_record_sha256(record: dict[str, Any]) -> None:
    """Add the final-record self-hash, refusing to overwrite any conflict."""

    digest = matrix_record_digest(record)
    if MATRIX_RECORD_SHA256_FIELD in record:
        existing = _sha256_value(
            record[MATRIX_RECORD_SHA256_FIELD], "matrix final-record self-hash"
        )
        if existing != digest:
            raise BenchmarkToolError(
                "runner record already contains a conflicting matrix final-record self-hash"
            )
        return
    record[MATRIX_RECORD_SHA256_FIELD] = digest


def _manifest_papers(manifest: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    raw_papers = manifest.get("papers")
    if not isinstance(raw_papers, list) or not raw_papers:
        raise BenchmarkToolError("benchmark manifest must contain a nonempty papers list")
    papers = [_mapping(value, f"manifest.papers[{index}]") for index, value in enumerate(raw_papers)]
    paper_ids = [
        _nonempty_string(paper.get("paper_id"), f"manifest.papers[{index}].paper_id")
        for index, paper in enumerate(papers)
    ]
    if len(set(paper_ids)) != len(paper_ids):
        raise BenchmarkToolError("benchmark manifest repeats a paper_id")
    for paper_id in paper_ids:
        if re.fullmatch(r"P[0-9]+", paper_id) is None:
            raise BenchmarkToolError(f"invalid paper_id in benchmark manifest: {paper_id!r}")

    corpus = _mapping(manifest.get("corpus"), "manifest.corpus")
    corpus_ids = corpus.get("paper_ids")
    if corpus_ids != paper_ids:
        raise BenchmarkToolError(
            "manifest.corpus.paper_ids must equal the ordered manifest paper IDs"
        )
    if corpus.get("paper_count") != len(papers):
        raise BenchmarkToolError("manifest.corpus.paper_count disagrees with papers")
    return papers


def corpus_slug(manifest: Mapping[str, Any]) -> str:
    """Return the ordered, filesystem-safe corpus identity used in run metadata."""

    return "-".join(str(paper["paper_id"]).lower() for paper in _manifest_papers(manifest))


def _available_manifest_targets(
    manifest: Mapping[str, Any],
) -> list[tuple[Mapping[str, Any], Mapping[str, Any]]]:
    available: list[tuple[Mapping[str, Any], Mapping[str, Any]]] = []
    seen: set[str] = set()
    for paper in _manifest_papers(manifest):
        paper_id = str(paper["paper_id"])
        targets = paper.get("targets")
        if not isinstance(targets, list):
            raise BenchmarkToolError(f"manifest paper {paper_id} has no targets list")
        for index, raw_target in enumerate(targets):
            target = _mapping(raw_target, f"manifest target {paper_id}[{index}]")
            if target.get("availability") != "available":
                continue
            task_id = _nonempty_string(target.get("task_id"), "manifest target task_id")
            if task_id in seen:
                raise BenchmarkToolError(f"benchmark manifest repeats task {task_id}")
            seen.add(task_id)
            tier = _nonempty_string(target.get("tier"), f"manifest target {task_id} tier")
            if task_id != f"{paper_id}-{tier}":
                raise BenchmarkToolError(
                    f"manifest task {task_id} disagrees with paper {paper_id} and tier {tier}"
                )
            available.append((paper, target))
    if not available:
        raise BenchmarkToolError("benchmark manifest contains no available tasks")
    return available


def required_release_files(manifest: Mapping[str, Any]) -> set[str]:
    """Return runtime files plus every paper/task file named by the manifest."""

    required = set(REQUIRED_RUNTIME_RELEASE_FILES)
    required.update(relative for relative, _entry, _scope in _controlled_shared_entries(manifest))
    for paper in _manifest_papers(manifest):
        required.add(f"tasks/{paper['paper_id']}/paper.json")
    for paper, target in _available_manifest_targets(manifest):
        paper_id = str(paper["paper_id"])
        tier = str(target["tier"])
        task_id = str(target["task_id"])
        required.add(f"metadata/controlled/{task_id}.json")
        required.update(
            {
                f"tasks/{paper_id}/{tier}/Target.lean",
                f"tasks/{paper_id}/{tier}/context.md",
                f"tasks/{paper_id}/{tier}/task.json",
            }
        )
    return required


def _benchmark_relative_path(value: Any, label: str) -> str:
    declared = PurePosixPath(_nonempty_string(value, label))
    if declared.is_absolute() or ".." in declared.parts:
        raise BenchmarkToolError(f"{label} is not a safe benchmark path")
    project_prefix = PurePosixPath("paper_bencmark/highambench")
    try:
        declared = declared.relative_to(project_prefix)
    except ValueError:
        pass
    return declared.as_posix()


def _controlled_shared_entries(
    manifest: Mapping[str, Any],
) -> list[tuple[str, Mapping[str, Any], tuple[str, ...]]]:
    raw_entries = manifest.get("controlled_shared_files")
    if not isinstance(raw_entries, list) or not raw_entries:
        raise BenchmarkToolError("benchmark manifest has no controlled_shared_files")
    known_papers = {str(paper["paper_id"]) for paper in _manifest_papers(manifest)}
    entries: list[tuple[str, Mapping[str, Any], tuple[str, ...]]] = []
    seen: set[str] = set()
    for index, value in enumerate(raw_entries):
        entry = _mapping(value, f"manifest controlled_shared_files[{index}]")
        relative = _benchmark_relative_path(
            entry.get("path"), f"manifest controlled_shared_files[{index}].path"
        )
        path = PurePosixPath(relative)
        if (
            len(path.parts) < 3
            or path.parts[:2] != ("shared", "HighamBench")
            or path.suffix != ".lean"
        ):
            raise BenchmarkToolError(
                f"controlled shared file must be below shared/HighamBench: {relative}"
            )
        if relative in seen:
            raise BenchmarkToolError(f"controlled shared file is repeated: {relative}")
        seen.add(relative)
        _sha256_value(entry.get("sha256"), f"controlled shared file {relative} SHA-256")
        raw_scope = entry.get("paper_ids")
        if (
            not isinstance(raw_scope, list)
            or not raw_scope
            or any(not isinstance(paper_id, str) for paper_id in raw_scope)
            or len(set(raw_scope)) != len(raw_scope)
        ):
            raise BenchmarkToolError(
                f"controlled shared file {relative} must have unique paper_ids"
            )
        scope = tuple(raw_scope)
        unknown = sorted(set(scope) - known_papers)
        if unknown:
            raise BenchmarkToolError(
                f"controlled shared file {relative} names unknown papers: {', '.join(unknown)}"
            )
        entries.append((relative, entry, scope))
    return entries


def _shared_sources_for_paper(
    manifest: Mapping[str, Any], paper_id: str
) -> list[str]:
    return [
        relative
        for relative, _entry, scope in _controlled_shared_entries(manifest)
        if paper_id in scope
    ]


def _declared_benchmark_path(value: Any, expected: str, label: str) -> str:
    declared = PurePosixPath(_nonempty_string(value, label))
    if declared.is_absolute() or ".." in declared.parts:
        raise BenchmarkToolError(f"{label} is not a safe benchmark path")
    expected_path = PurePosixPath(expected)
    project_path = PurePosixPath("paper_bencmark/highambench") / expected_path
    if declared not in (expected_path, project_path):
        raise BenchmarkToolError(
            f"{label} must name {project_path.as_posix()}, not {declared.as_posix()}"
        )
    return expected_path.as_posix()


def load_task_catalog(
    root: Path, manifest: Mapping[str, Any] | None = None
) -> dict[str, dict[str, Any]]:
    """Load execution identities from mutually checked manifest and task records."""

    root = root.resolve()
    manifest = manifest or _mapping(
        read_json(root / "metadata" / "manifest.json"), "benchmark manifest"
    )
    catalog: dict[str, dict[str, Any]] = {}
    for paper, target in _available_manifest_targets(manifest):
        paper_id = str(paper["paper_id"])
        tier = str(target["tier"])
        task_id = str(target["task_id"])
        target_dir = f"tasks/{paper_id}/{tier}"
        target_file = f"{target_dir}/Target.lean"
        context_file = f"{target_dir}/context.md"
        task_file = f"{target_dir}/task.json"

        paper_source = _mapping(paper.get("source"), f"manifest paper {paper_id} source")
        paper_sha256 = _sha256_value(
            paper_source.get("sha256"), f"manifest paper {paper_id} source SHA-256"
        )
        paper_record = _mapping(
            read_json(_require_file(root / f"tasks/{paper_id}/paper.json", f"{paper_id} paper record")),
            f"{paper_id} paper record",
        )
        if paper_record.get("paper_id") != paper_id:
            raise BenchmarkToolError(f"{paper_id} paper record has the wrong paper_id")
        recorded_paper_source = _mapping(
            paper_record.get("source"), f"{paper_id} paper record source"
        )
        if recorded_paper_source.get("sha256") != paper_sha256:
            raise BenchmarkToolError(f"{paper_id} paper SHA-256 disagrees across metadata")

        task = _mapping(
            read_json(_require_file(root / task_file, f"{task_id} task record")),
            f"{task_id} task record",
        )
        for field, expected in (
            ("task_id", task_id),
            ("paper_id", paper_id),
            ("tier", tier),
        ):
            if task.get(field) != expected:
                raise BenchmarkToolError(
                    f"{task_id} task record {field}={task.get(field)!r}, expected {expected!r}"
                )
        tag_record = validate_task_source_tags(task, label=task_id)
        if tag_record["measurement_ready"] is not True:
            raise BenchmarkToolError(
                f"{task_id} is still under construction; create a measurement-ready "
                "snapshot before starting benchmark runs"
            )
        task_source = _mapping(task.get("paper_source"), f"{task_id}.paper_source")
        if task_source.get("sha256") != paper_sha256:
            raise BenchmarkToolError(f"{task_id} paper SHA-256 disagrees across metadata")
        _declared_benchmark_path(task.get("context_file"), context_file, f"{task_id} context_file")

        lean_target = _mapping(
            target.get("lean_target"), f"manifest target {task_id}.lean_target"
        )
        _declared_benchmark_path(
            lean_target.get("file"), target_file, f"manifest target {task_id} file"
        )
        raw_shared = lean_target.get("shared_files")
        if not isinstance(raw_shared, list) or not raw_shared:
            raise BenchmarkToolError(f"manifest target {task_id} has no shared_files")
        declared_shared = [
            _benchmark_relative_path(value, f"manifest target {task_id} shared_files")
            for value in raw_shared
        ]
        expected_shared = _shared_sources_for_paper(manifest, paper_id)
        if declared_shared != expected_shared:
            raise BenchmarkToolError(
                f"manifest target {task_id} shared_files disagrees with its paper scope"
            )
        validation = _mapping(task.get("validation"), f"{task_id}.validation")
        _declared_benchmark_path(
            validation.get("controlled_target_file"),
            target_file,
            f"{task_id} controlled target_file",
        )

        if tier == "T4":
            raw_required = validation.get("required_declarations")
            if not isinstance(raw_required, list) or not raw_required or any(
                not isinstance(value, str) or not value for value in raw_required
            ):
                raise BenchmarkToolError(
                    f"{task_id}.validation.required_declarations is invalid"
                )
            required_declarations = list(raw_required)
            declaration_records = task.get("declarations")
            declaration_names = (
                [
                    declaration.get("lean_name")
                    for declaration in declaration_records
                    if isinstance(declaration, Mapping)
                ]
                if isinstance(declaration_records, list)
                else []
            )
            if declaration_names != required_declarations:
                raise BenchmarkToolError(
                    f"{task_id} required_declarations disagrees with declaration records"
                )
            if lean_target.get("required_declarations") != required_declarations:
                raise BenchmarkToolError(
                    f"manifest target {task_id} required_declarations disagrees"
                )
            if "declaration" in lean_target:
                raise BenchmarkToolError(
                    f"manifest target {task_id} must use plural required_declarations"
                )
            raw_holes = validation.get("controlled_sorries")
            if not isinstance(raw_holes, list) or not raw_holes or any(
                not isinstance(value, Mapping) for value in raw_holes
            ):
                raise BenchmarkToolError(
                    f"{task_id}.validation.controlled_sorries is invalid"
                )
            controlled_sorries = [dict(value) for value in raw_holes]
            proof_declarations = [
                value.get("lean_name") for value in controlled_sorries
            ]
            if any(
                not isinstance(value, str) or value not in required_declarations
                for value in proof_declarations
            ):
                raise BenchmarkToolError(
                    f"{task_id} controlled proof declarations are invalid"
                )
            required_declaration = str(proof_declarations[0])
            theorem_name = required_declaration.rsplit(".", 1)[-1]
            catalog[task_id] = {
                "task_id": task_id,
                "paper_id": paper_id,
                "paper_sha256": paper_sha256,
                "tier": tier,
                "theorem_name": theorem_name,
                "required_declaration": required_declaration,
                "required_declarations": required_declarations,
                "proof_declarations": proof_declarations,
                "controlled_sorries": controlled_sorries,
                "target_dir": target_dir,
                "target_file": target_file,
                "context_file": context_file,
            }
        else:
            formal = _mapping(
                task.get("formal_statement"), f"{task_id}.formal_statement"
            )
            namespace = _nonempty_string(
                formal.get("namespace"), f"{task_id} namespace"
            )
            theorem_name = _nonempty_string(
                formal.get("theorem_name"), f"{task_id} theorem_name"
            )
            _declared_benchmark_path(
                formal.get("target_file"),
                target_file,
                f"{task_id} formal target_file",
            )
            if lean_target.get("declaration") != theorem_name:
                raise BenchmarkToolError(
                    f"{task_id} theorem name disagrees across metadata"
                )
            if "required_declarations" in lean_target:
                raise BenchmarkToolError(
                    f"manifest target {task_id} plural declarations are only valid for T4"
                )
            required_declaration = f"{namespace}.{theorem_name}"
            if validation.get("required_declaration") != required_declaration:
                raise BenchmarkToolError(
                    f"{task_id} validation declaration disagrees"
                )
            catalog[task_id] = {
                "task_id": task_id,
                "paper_id": paper_id,
                "paper_sha256": paper_sha256,
                "tier": tier,
                "theorem_name": theorem_name,
                "required_declaration": required_declaration,
                "target_dir": target_dir,
                "target_file": target_file,
                "context_file": context_file,
            }

    for paper in _manifest_papers(manifest):
        paper_id = str(paper["paper_id"])
        paper_record = _mapping(
            read_json(root / f"tasks/{paper_id}/paper.json"), f"{paper_id} paper record"
        )
        expected = [
            task_id for task_id, task in catalog.items() if task["paper_id"] == paper_id
        ]
        if paper_record.get("included_tasks") != expected:
            raise BenchmarkToolError(
                f"{paper_id} paper record included_tasks disagrees with the manifest"
            )
    return catalog


def _command_output(command: list[str], label: str) -> str:
    try:
        completed = subprocess.run(
            command,
            check=False,
            capture_output=True,
            text=True,
            timeout=30,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise BenchmarkToolError(f"cannot inspect {label}: {error}") from error
    if completed.returncode != 0:
        detail = (completed.stderr or completed.stdout).strip()
        raise BenchmarkToolError(
            f"cannot inspect {label} (exit {completed.returncode}): {detail}"
        )
    return (completed.stdout or completed.stderr).strip()


def _git_head(repository: Path, label: str) -> str:
    value = _command_output(
        ["git", "-C", str(repository.resolve()), "rev-parse", "HEAD"], label
    ).splitlines()[-1]
    if not re.fullmatch(r"[0-9a-f]{40}", value):
        raise BenchmarkToolError(f"{label} returned an invalid Git commit: {value!r}")
    return value


def _require_git_commit(repository: Path, commit: str, label: str) -> None:
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise BenchmarkToolError(f"{label} is not a valid Git commit: {commit!r}")
    _command_output(
        [
            "git",
            "-C",
            str(repository.resolve()),
            "cat-file",
            "-e",
            f"{commit}^{{commit}}",
        ],
        label,
    )


def _require_git_paths_equal(
    repository: Path,
    older: str,
    newer: str,
    paths: list[str],
    label: str,
) -> None:
    compared = subprocess.run(
        [
            "git",
            "-C",
            str(repository.resolve()),
            "diff",
            "--quiet",
            older,
            newer,
            "--",
            *paths,
        ],
        check=False,
        capture_output=True,
        text=True,
    )
    if compared.returncode not in (0, 1):
        raise BenchmarkToolError(
            f"cannot compare {label}: {(compared.stderr or compared.stdout).strip()}"
        )
    if compared.returncode == 1:
        raise BenchmarkToolError(
            f"{label} differs between frozen baseline {older} and {newer}"
        )


def _require_git_sources_clean(repository: Path, paths: list[str], label: str) -> None:
    tracked = subprocess.run(
        ["git", "-C", str(repository.resolve()), "diff", "--quiet", "HEAD", "--", *paths],
        check=False,
        capture_output=True,
        text=True,
    )
    if tracked.returncode not in (0, 1):
        raise BenchmarkToolError(f"cannot check {label} tracked files: {tracked.stderr.strip()}")
    if tracked.returncode == 1:
        raise BenchmarkToolError(f"{label} has tracked changes relative to its frozen commit")
    untracked = _command_output(
        [
            "git",
            "-C",
            str(repository.resolve()),
            "ls-files",
            "--others",
            "--exclude-standard",
            "--",
            *paths,
        ],
        f"{label} untracked files",
    )
    if untracked:
        raise BenchmarkToolError(f"{label} has untracked files: {untracked.splitlines()[:5]}")


def _in_release_scope(relative: str) -> bool:
    if relative == "agent_prompt.md" or relative == CONDITION_L_PROMPT_RELATIVE:
        return True
    if relative.startswith(("shared/", "tasks/", "tools/", "metadata/controlled/")):
        return True
    return relative in {
        "metadata/manifest.json",
        "metadata/run_order.json",
        "metadata/library_olean.json",
        "metadata/library_source.json",
        "metadata/packages_olean.json",
        "metadata/packages_runtime.json",
        "metadata/evidence/token_control_live_canary.json",
        "metadata/evidence/ultra_orchestration_live_canary.json",
    }


def _release_tree_files(root: Path) -> set[str]:
    files: set[str] = set()
    for path in root.rglob("*"):
        if not path.is_file():
            continue
        relative = path.relative_to(root).as_posix()
        if relative == RELEASE_MANIFEST_RELATIVE:
            continue
        if "__pycache__" in path.parts or path.suffix == ".pyc":
            continue
        if _in_release_scope(relative):
            files.add(relative)
    return files


def evaluation_release_tree_files(root: Path) -> set[str]:
    """Return the exact manifest-covered evaluation tree."""

    return _release_tree_files(root)


def _verify_release_manifest(root: Path, raw_path: Path | None) -> dict[str, Any]:
    path = (raw_path or (root / RELEASE_MANIFEST_RELATIVE)).resolve()
    if path != (root / RELEASE_MANIFEST_RELATIVE).resolve():
        raise BenchmarkToolError(
            f"release manifest must be {RELEASE_MANIFEST_RELATIVE}, not {path}"
        )
    _require_file(path, "global release manifest")
    release = load_manifest(path)
    listed = {entry["path"] for entry in release["files"]}
    actual = evaluation_release_tree_files(root)
    benchmark_manifest = _mapping(
        read_json(root / "metadata" / "manifest.json"), "benchmark manifest"
    )
    missing_required = sorted(required_release_files(benchmark_manifest) - listed)
    if missing_required:
        raise BenchmarkToolError(
            "global release manifest omits required runtime files: "
            + ", ".join(missing_required)
        )
    if listed != actual:
        omitted = sorted(actual - listed)
        nonexistent = sorted(listed - actual)
        raise BenchmarkToolError(
            "global release manifest is not an exact evaluation-package snapshot "
            f"(omitted={omitted[:8]}, nonexistent={nonexistent[:8]})"
        )
    verification = verify_manifest(root, release)
    if not verification["ok"]:
        raise BenchmarkToolError(
            f"global release files changed after freezing: {verification}"
        )
    return {
        "path": RELEASE_MANIFEST_RELATIVE,
        "sha256": sha256_file(path),
        "file_count": len(listed),
        "verification": verification,
    }


def exact_tree_digest(root: Path) -> dict[str, Any]:
    """Hash every regular file and internal symbolic link in a tree.

    Lean toolchains contain a small number of normal relative symbolic links
    between shared libraries.  Their link text is part of the frozen tree.  A
    link that resolves outside the mounted root is rejected because its final
    bytes would otherwise be outside this fingerprint.
    """

    root = _require_dir(root, "compiled tree")
    entries: list[tuple[str, str, int, str]] = []
    regular_file_count = 0
    symlink_count = 0
    for path in root.rglob("*"):
        if path.is_symlink():
            try:
                path.resolve(strict=True).relative_to(root)
            except (OSError, ValueError) as error:
                raise BenchmarkToolError(
                    f"frozen tree contains a broken or external symlink: {path}"
                ) from error
            link_text = os.readlink(path)
            link_bytes = os.fsencode(link_text)
            relative = path.relative_to(root).as_posix()
            entries.append(
                ("L", relative, len(link_bytes), hashlib.sha256(link_bytes).hexdigest())
            )
            symlink_count += 1
            continue
        if path.is_dir():
            continue
        if not path.is_file():
            raise BenchmarkToolError(f"frozen tree contains a special file: {path}")
        relative = path.relative_to(root).as_posix()
        entries.append(("F", relative, path.stat().st_size, sha256_file(path)))
        regular_file_count += 1
    digest = hashlib.sha256()
    total_bytes = 0
    for entry_type, relative, byte_count, entry_digest in sorted(entries):
        digest.update(entry_type.encode("ascii"))
        digest.update(b"\0")
        digest.update(relative.encode("utf-8"))
        digest.update(b"\0")
        digest.update(str(byte_count).encode("ascii"))
        digest.update(b"\0")
        digest.update(entry_digest.encode("ascii"))
        digest.update(b"\n")
        total_bytes += byte_count
    return {
        "algorithm": (
            "sha256(entry-type NUL relative-path NUL byte-count NUL "
            "content-or-link-text-sha256 newline)"
        ),
        "file_count": len(entries),
        "regular_file_count": regular_file_count,
        "symlink_count": symlink_count,
        "total_bytes": total_bytes,
        "tree_sha256": digest.hexdigest(),
    }


def compiled_environment_summary(
    toolchain_root: Path, packages_root: Path
) -> dict[str, Any]:
    """Return exact digests for the mounted toolchain and package build trees."""

    toolchain_tree = _require_dir(toolchain_root, "Lean toolchain tree")
    package_rows: list[dict[str, Any]] = []
    for package in sorted(packages_root.iterdir(), key=lambda item: item.name):
        if package.is_symlink():
            raise BenchmarkToolError(f"packages root contains a symlinked package: {package}")
        compiled = package / ".lake" / "build" / "lib" / "lean"
        if not compiled.is_dir():
            continue
        commit = _git_head(package, f"{package.name} package commit")
        _require_git_sources_clean(package, ["."], f"{package.name} package")
        package_rows.append(
            {
                "package": package.name,
                "relative_root": f"{package.name}/.lake/build/lib/lean",
                "git_commit": commit,
                **exact_tree_digest(compiled),
            }
        )
    if not any(row["package"] == "mathlib" for row in package_rows):
        raise BenchmarkToolError("compiled package trees do not contain mathlib")
    return {
        "schema_version": 1,
        "kind": "highambench-compiled-environment-summary",
        # The adapters mount all of toolchain_root, not only lib/lean.  Hash the
        # complete visible tree so executables and auxiliary runtime files are
        # covered by the same exact snapshot.
        "toolchain": {"relative_root": ".", **exact_tree_digest(toolchain_tree)},
        "packages": package_rows,
    }


def _verify_compiled_environment_summary(
    args: argparse.Namespace,
    project: Path,
    frozen: Mapping[str, Any],
    lean: Mapping[str, Any],
) -> dict[str, Any]:
    relative = _fixed_value(
        "compiled environment summary path",
        frozen.get("compiled_environment_summary"),
        lean.get("compiled_environment_summary"),
    )
    expected_digest = _fixed_value(
        "compiled environment summary SHA-256",
        frozen.get("compiled_environment_summary_sha256"),
        lean.get("compiled_environment_summary_sha256"),
    )
    summary_path = (project / str(relative)).resolve()
    try:
        summary_path.relative_to(project)
    except ValueError as error:
        raise BenchmarkToolError("compiled environment summary escapes project root") from error
    _require_file(summary_path, "compiled environment summary")
    if sha256_file(summary_path) != expected_digest:
        raise BenchmarkToolError("compiled environment summary has the wrong SHA-256")
    expected = read_json(summary_path)
    if not isinstance(expected, Mapping):
        raise BenchmarkToolError("compiled environment summary must be an object")
    actual = compiled_environment_summary(args.toolchain_root.resolve(), args.packages_root.resolve())
    if expected != actual:
        raise BenchmarkToolError("actual compiled Lean/package trees differ from the frozen summary")
    return {
        "path": str(relative),
        "sha256": expected_digest,
        "toolchain_file_count": actual["toolchain"]["file_count"],
        "package_count": len(actual["packages"]),
        "package_file_count": sum(row["file_count"] for row in actual["packages"]),
    }


def expected_packages_runtime_files(packages_root: Path) -> set[str]:
    """Return the exact files permitted in the package runtime mount.

    The evaluated process needs each package's base compiled modules and Lean
    4.29's split compiled support files (``.olean.server``,
    ``.olean.private``, and ``.ir``), together with readable mathlib sources.
    It does not need Git metadata, build traces, caches, package sources other
    than mathlib, or any other file from the original package checkouts.
    """

    packages_root = _require_dir(packages_root, "original Lake packages")
    expected: set[str] = set()
    for package in sorted(packages_root.iterdir(), key=lambda item: item.name):
        if package.is_symlink():
            raise BenchmarkToolError(
                f"packages root contains a symlinked package: {package}"
            )
        if not package.is_dir():
            raise BenchmarkToolError(
                f"packages root contains a non-directory entry: {package}"
            )
        compiled = package / ".lake" / "build" / "lib" / "lean"
        if not compiled.is_dir():
            continue
        for path in compiled.rglob("*"):
            if path.is_symlink():
                raise BenchmarkToolError(
                    f"compiled package tree contains a symlink: {path}"
                )
            if path.is_file() and path.name.endswith(
                (PACKAGE_BASE_COMPILED_SUFFIX, *PACKAGE_COMPILED_SUPPORT_SUFFIXES)
            ):
                expected.add(path.relative_to(packages_root).as_posix())

    mathlib = _require_dir(packages_root / "mathlib", "mathlib package")
    mathlib_root = mathlib / "Mathlib.lean"
    if not mathlib_root.is_file() or mathlib_root.is_symlink():
        raise BenchmarkToolError("mathlib runtime source Mathlib.lean is missing")
    expected.add(mathlib_root.relative_to(packages_root).as_posix())
    mathlib_sources = _require_dir(mathlib / "Mathlib", "mathlib source tree")
    for path in mathlib_sources.rglob("*"):
        if path.is_symlink():
            raise BenchmarkToolError(f"mathlib source tree contains a symlink: {path}")
        if path.is_file() and path.suffix == ".lean":
            expected.add(path.relative_to(packages_root).as_posix())
    if not any(path.endswith(PACKAGE_BASE_COMPILED_SUFFIX) for path in expected):
        raise BenchmarkToolError("package runtime contains no compiled Lean modules")
    if not any(path.endswith(PACKAGE_COMPILED_SUPPORT_SUFFIXES) for path in expected):
        raise BenchmarkToolError(
            "package runtime contains no split compiled support files"
        )
    return expected


def _verify_packages_runtime(
    args: argparse.Namespace,
    project: Path,
    frozen: Mapping[str, Any],
    runtime: Mapping[str, Any],
) -> dict[str, Any]:
    relative = _fixed_value(
        "packages runtime manifest path",
        frozen.get("packages_runtime_manifest"),
        runtime.get("packages_runtime_manifest"),
    )
    if relative != FROZEN_PACKAGES_RUNTIME_MANIFEST_PATH:
        raise BenchmarkToolError(
            "frozen packages runtime manifest path must be "
            f"{FROZEN_PACKAGES_RUNTIME_MANIFEST_PATH}"
        )
    expected_digest = _fixed_value(
        "packages runtime manifest SHA-256",
        frozen.get("packages_runtime_manifest_sha256"),
        runtime.get("packages_runtime_manifest_sha256"),
    )
    if not isinstance(expected_digest, str) or not re.fullmatch(
        r"[0-9a-f]{64}", expected_digest
    ):
        raise BenchmarkToolError("packages runtime manifest SHA-256 is invalid")
    manifest_path = (project / str(relative)).resolve()
    try:
        manifest_path.relative_to(project)
    except ValueError as error:
        raise BenchmarkToolError("packages runtime manifest escapes project root") from error
    _require_file(manifest_path, "packages runtime manifest")
    if sha256_file(manifest_path) != expected_digest:
        raise BenchmarkToolError("packages runtime manifest has the wrong SHA-256")
    manifest = load_manifest(manifest_path)
    listed = {entry["path"] for entry in manifest["files"]}
    expected = expected_packages_runtime_files(args.packages_root.resolve())
    if listed != expected:
        raise BenchmarkToolError(
            "packages runtime manifest is not the exact permitted projection "
            f"(omitted={sorted(expected - listed)[:8]}, "
            f"unexpected={sorted(listed - expected)[:8]})"
        )

    runtime_root = _require_dir(
        args.packages_runtime_root, "pruned packages runtime root"
    )
    if runtime_root == args.packages_root.resolve():
        raise BenchmarkToolError(
            "packages runtime root must be a separate pruned tree, not the original package checkout"
        )
    verification = verify_manifest(runtime_root, manifest)
    if not verification["ok"]:
        raise BenchmarkToolError(
            f"pruned packages runtime tree is not frozen: {verification}"
        )
    actual: set[str] = set()
    for path in runtime_root.rglob("*"):
        if path.is_symlink():
            raise BenchmarkToolError(f"packages runtime tree contains a symlink: {path}")
        if path.is_dir():
            continue
        if not path.is_file():
            raise BenchmarkToolError(
                f"packages runtime tree contains a special file: {path}"
            )
        actual.add(path.relative_to(runtime_root).as_posix())
    if actual != listed:
        raise BenchmarkToolError(
            "packages runtime root is not the exact frozen manifest tree "
            f"(extra={sorted(actual - listed)[:8]}, "
            f"missing={sorted(listed - actual)[:8]})"
        )
    return {
        "path": str(relative),
        "sha256": expected_digest,
        "file_count": len(listed),
        "source_file_count": sum(path.endswith(".lean") for path in listed),
        "olean_file_count": sum(
            path.endswith(PACKAGE_BASE_COMPILED_SUFFIX) for path in listed
        ),
        "compiled_support_file_count": sum(
            path.endswith(PACKAGE_COMPILED_SUPPORT_SUFFIXES) for path in listed
        ),
        "verification": verification,
    }


def _visible_memory_bytes() -> int:
    try:
        first = Path("/proc/meminfo").read_text(encoding="utf-8").splitlines()[0]
        key, value, unit = first.split()
        if key != "MemTotal:" or unit != "kB":
            raise ValueError(first)
        return int(value) * 1024
    except (OSError, ValueError, IndexError) as error:
        raise BenchmarkToolError(f"cannot read visible memory size: {error}") from error


def _cpu_identity() -> dict[str, Any]:
    wanted = {
        "vendor_id": "cpu_vendor",
        "cpu family": "cpu_family",
        "model": "cpu_model",
        "stepping": "cpu_stepping",
        "model name": "processor",
    }
    found: dict[str, str] = {}
    try:
        for line in Path("/proc/cpuinfo").read_text(encoding="utf-8").splitlines():
            if not line.strip():
                break
            if ":" not in line:
                continue
            key, value = (part.strip() for part in line.split(":", 1))
            if key in wanted:
                found[wanted[key]] = value
    except OSError as error:
        raise BenchmarkToolError(f"cannot inspect CPU identity: {error}") from error
    missing = [field for field in wanted.values() if not found.get(field)]
    if missing:
        raise BenchmarkToolError(f"cannot inspect CPU identity fields: {missing}")
    try:
        return {
            "cpu_vendor": found["cpu_vendor"],
            "cpu_family": int(found["cpu_family"]),
            "cpu_model": int(found["cpu_model"]),
            "cpu_stepping": int(found["cpu_stepping"]),
            "processor": found["processor"],
        }
    except ValueError as error:
        raise BenchmarkToolError(f"CPU identity has a nonnumeric field: {error}") from error


def _allocated_cpu_topology(
    cpu_ids: Iterable[int] | None = None,
    *,
    sysfs_root: Path = Path("/sys/devices/system/cpu"),
) -> dict[str, Any]:
    if cpu_ids is None:
        if hasattr(os, "sched_getaffinity"):
            cpu_ids = os.sched_getaffinity(0)
        else:
            count = os.cpu_count()
            if count is None:
                raise BenchmarkToolError("cannot inspect allocated CPU affinity")
            cpu_ids = range(count)
    logical_cpus = sorted(set(cpu_ids))
    if not logical_cpus:
        raise BenchmarkToolError("allocated CPU affinity is empty")
    core_counts: dict[tuple[int, int], int] = {}
    try:
        for cpu_id in logical_cpus:
            topology = sysfs_root / f"cpu{cpu_id}" / "topology"
            package_id = int(
                (topology / "physical_package_id").read_text(encoding="utf-8").strip()
            )
            core_id = int((topology / "core_id").read_text(encoding="utf-8").strip())
            key = (package_id, core_id)
            core_counts[key] = core_counts.get(key, 0) + 1
    except (OSError, ValueError) as error:
        raise BenchmarkToolError(f"cannot inspect allocated CPU topology: {error}") from error
    return {
        "online_logical_cpus": len(logical_cpus),
        "allocated_physical_cores": len(core_counts),
        "allocated_sockets": len({package_id for package_id, _core_id in core_counts}),
        "allocated_threads_per_core": sorted(core_counts.values()),
    }


def _cgroup_memory_limit_bytes(
    *,
    proc_cgroup: Path = Path("/proc/self/cgroup"),
    cgroup_root: Path = Path("/sys/fs/cgroup"),
) -> int:
    """Return the tightest finite memory limit on this process's cgroup path."""

    try:
        lines = proc_cgroup.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        raise BenchmarkToolError(f"cannot inspect process cgroup: {error}") from error
    candidates: list[Path] = []
    for line in lines:
        parts = line.split(":", 2)
        if len(parts) != 3:
            continue
        hierarchy, controllers, relative = parts
        relative_path = Path(relative.lstrip("/"))
        if hierarchy == "0" and controllers == "":
            candidates.append(cgroup_root / relative_path / "memory.max")
        elif "memory" in controllers.split(","):
            candidates.append(cgroup_root / "memory" / relative_path / "memory.limit_in_bytes")
    limits: list[int] = []
    for candidate in candidates:
        boundary = cgroup_root.resolve()
        current = candidate
        while True:
            if current.is_file():
                try:
                    raw = current.read_text(encoding="utf-8").strip()
                    if raw != "max":
                        value = int(raw)
                        # Linux v1 uses a value near INT64_MAX to mean unlimited.
                        if 0 < value < (1 << 60):
                            limits.append(value)
                except (OSError, ValueError) as error:
                    raise BenchmarkToolError(
                        f"cannot inspect cgroup memory limit {current}: {error}"
                    ) from error
            parent = current.parent.parent
            if current.parent.resolve() == boundary or not current.parent.resolve().is_relative_to(boundary):
                break
            next_name = "memory.max" if current.name == "memory.max" else "memory.limit_in_bytes"
            current = parent / next_name
    if not limits:
        raise BenchmarkToolError("cannot find a finite cgroup memory limit")
    return min(limits)


def _slurm_memory_bytes(raw: str) -> int:
    matched = re.fullmatch(r"([0-9]+)([KMGTP]?)", raw)
    if matched is None:
        raise BenchmarkToolError(f"cannot parse Slurm memory quantity {raw!r}")
    exponent = {"": 0, "K": 1, "M": 2, "G": 3, "T": 4, "P": 5}[matched.group(2)]
    return int(matched.group(1)) * (1024 ** exponent)


def _slurm_allocated_gpu_count(raw_alloc_tres: Any) -> int:
    """Parse one raw AllocTRES value and fail closed unless its GPU count is zero."""

    raw = _nonempty_string(raw_alloc_tres, "Slurm AllocTRES")
    if any(character.isspace() for character in raw):
        raise BenchmarkToolError("Slurm AllocTRES must not contain whitespace")
    entries = raw.split(",")
    if any(not entry for entry in entries):
        raise BenchmarkToolError("Slurm AllocTRES contains an empty TRES entry")
    seen: set[str] = set()
    allocated_gpu_count = 0
    for entry in entries:
        if entry.count("=") != 1:
            raise BenchmarkToolError(
                f"Slurm AllocTRES entry is malformed: {entry!r}"
            )
        name, count = entry.split("=", 1)
        if not name or not count:
            raise BenchmarkToolError(
                f"Slurm AllocTRES entry is malformed: {entry!r}"
            )
        if name in seen:
            raise BenchmarkToolError(
                f"Slurm AllocTRES repeats TRES name {name!r}"
            )
        seen.add(name)
        lowered_name = name.lower()
        if lowered_name.startswith("gres/gpu") and not name.startswith("gres/gpu"):
            raise BenchmarkToolError(f"Slurm GPU TRES name is malformed: {name!r}")
        if not name.startswith("gres/gpu"):
            continue
        if re.fullmatch(r"gres/gpu(?::[A-Za-z0-9][A-Za-z0-9_.+-]*)?", name) is None:
            raise BenchmarkToolError(f"Slurm GPU TRES name is malformed: {name!r}")
        if re.fullmatch(r"(?:0|[1-9][0-9]*)", count) is None:
            raise BenchmarkToolError(
                f"Slurm GPU TRES count is malformed: {entry!r}"
            )
        parsed_count = int(count)
        if parsed_count != 0:
            raise BenchmarkToolError(
                f"Slurm allocation has nonzero GPU TRES {entry!r}"
            )
        allocated_gpu_count += parsed_count
    return allocated_gpu_count


def _validated_gpu_environment(value: Any) -> dict[str, str | None]:
    """Validate and return the exact three-variable no-GPU environment snapshot."""

    snapshot = _mapping(value, "Slurm GPU environment snapshot")
    if set(snapshot) != set(GPU_ENVIRONMENT_VARIABLES):
        raise BenchmarkToolError(
            "Slurm GPU environment snapshot fields are not exact"
        )
    normalized: dict[str, str | None] = {}
    for name in GPU_ENVIRONMENT_VARIABLES:
        raw = snapshot.get(name)
        if raw is not None and not isinstance(raw, str):
            raise BenchmarkToolError(
                f"Slurm GPU environment variable {name} is not a string or null"
            )
        normalized[name] = raw
    if normalized["SLURM_GPUS_ON_NODE"] not in (None, "", "0"):
        raise BenchmarkToolError(
            "SLURM_GPUS_ON_NODE must be unset, empty, or exactly '0'"
        )
    for name in ("SLURM_JOB_GPUS", "CUDA_VISIBLE_DEVICES"):
        if normalized[name] not in (None, ""):
            raise BenchmarkToolError(f"{name} must be unset or empty")
    return normalized


def _validated_slurm_gpu_provenance(value: Any) -> dict[str, Any]:
    """Validate the exact raw, normalized, and environment GPU provenance."""

    provenance = _mapping(value, "Slurm GPU provenance")
    expected_fields = {"alloc_tres", "allocated_gpu_count", "gpu_environment"}
    if set(provenance) != expected_fields:
        raise BenchmarkToolError("Slurm GPU provenance fields are not exact")
    alloc_tres = _nonempty_string(
        provenance.get("alloc_tres"), "Slurm GPU provenance AllocTRES"
    )
    parsed_count = _slurm_allocated_gpu_count(alloc_tres)
    normalized_count = provenance.get("allocated_gpu_count")
    if (
        isinstance(normalized_count, bool)
        or not isinstance(normalized_count, int)
        or normalized_count != 0
        or normalized_count != parsed_count
    ):
        raise BenchmarkToolError(
            "Slurm normalized allocated GPU count must be the integer zero"
        )
    return {
        "alloc_tres": alloc_tres,
        "allocated_gpu_count": normalized_count,
        "gpu_environment": _validated_gpu_environment(
            provenance.get("gpu_environment")
        ),
    }


def _slurm_gpu_provenance(
    job_id: str,
    *,
    job_output: str | None = None,
    environ: Mapping[str, str] | None = None,
) -> dict[str, Any]:
    """Authenticate GPU=0 from raw Slurm state and the process environment."""

    if re.fullmatch(r"[0-9]+", job_id) is None:
        raise BenchmarkToolError(f"invalid {SLURM_JOB_ID_ENV}: {job_id!r}")
    if job_output is None:
        job_output = _command_output(
            ["scontrol", "show", "job", "-o", job_id],
            "Slurm GPU allocation",
        )

    def exact_field(name: str) -> str:
        matches = re.findall(
            rf"(?:^|\s){re.escape(name)}=([^\s]+)(?=\s|$)", job_output
        )
        if len(matches) != 1:
            raise BenchmarkToolError(
                f"Slurm allocation must contain exactly one nonempty {name} field"
            )
        return matches[0]

    if exact_field("JobId") != job_id:
        raise BenchmarkToolError("requested and reported Slurm GPU job IDs disagree")
    raw_alloc_tres = exact_field("AllocTRES")
    allocated_gpu_count = _slurm_allocated_gpu_count(raw_alloc_tres)
    source = os.environ if environ is None else environ
    snapshot = {
        name: source[name] if name in source else None
        for name in GPU_ENVIRONMENT_VARIABLES
    }
    return _validated_slurm_gpu_provenance(
        {
            "alloc_tres": raw_alloc_tres,
            "allocated_gpu_count": allocated_gpu_count,
            "gpu_environment": snapshot,
        }
    )


def _slurm_allocation_shape(output: str | None = None) -> dict[str, int]:
    if output is None:
        job_id = os.environ.get(SLURM_JOB_ID_ENV, "").strip()
        if not job_id:
            raise BenchmarkToolError(
                f"{SLURM_JOB_ID_ENV} is required to verify the frozen allocation"
            )
        if not re.fullmatch(r"[0-9]+", job_id):
            raise BenchmarkToolError(f"invalid {SLURM_JOB_ID_ENV}: {job_id!r}")
        output = _command_output(
            ["scontrol", "show", "job", "-o", job_id], "Slurm allocation"
        )

    def integer_field(name: str) -> int:
        matched = re.search(rf"(?:^| ){re.escape(name)}=([0-9]+)(?: |$)", output)
        if matched is None:
            raise BenchmarkToolError(f"Slurm allocation has no integer {name} field")
        return int(matched.group(1))

    tres = re.search(r"(?:^| )AllocTRES=([^ ]+)(?: |$)", output)
    if tres is None:
        raise BenchmarkToolError("Slurm allocation has no AllocTRES field")
    memory = re.search(r"(?:^|,)mem=([0-9]+[KMGTP]?)(?:,|$)", tres.group(1))
    if memory is None:
        raise BenchmarkToolError("Slurm AllocTRES has no memory quantity")
    return {
        "slurm_num_nodes": integer_field("NumNodes"),
        "slurm_num_cpus": integer_field("NumCPUs"),
        "slurm_num_tasks": integer_field("NumTasks"),
        "slurm_cpus_per_task": integer_field("CPUs/Task"),
        "slurm_allocated_memory_bytes": _slurm_memory_bytes(memory.group(1)),
    }


def _current_cpu_affinity() -> list[int]:
    """Return the exact logical CPU set used by the verified topology check."""

    if not hasattr(os, "sched_getaffinity"):
        raise BenchmarkToolError("cannot record an exact process CPU affinity on this host")
    affinity = sorted(os.sched_getaffinity(0))
    if not affinity:
        raise BenchmarkToolError("allocation CPU affinity is empty")
    return affinity


def _slurm_scheduler_sharing(
    job_id: str,
    *,
    job_output: str | None = None,
    partition_output: str | None = None,
) -> dict[str, Any]:
    """Record stable scheduler policy without sampling transient co-tenants."""

    if re.fullmatch(r"[0-9]+", job_id) is None:
        raise BenchmarkToolError(f"invalid {SLURM_JOB_ID_ENV}: {job_id!r}")
    if job_output is None:
        job_output = _command_output(
            ["scontrol", "show", "job", "-o", job_id],
            "Slurm job sharing policy",
        )

    def text_field(output: str, name: str, label: str) -> str:
        matched = re.search(rf"(?:^| ){re.escape(name)}=([^ ]+)(?: |$)", output)
        if matched is None:
            raise BenchmarkToolError(f"{label} has no {name} field")
        return matched.group(1)

    reported_job_id = text_field(job_output, "JobId", "Slurm allocation")
    if reported_job_id != job_id:
        raise BenchmarkToolError("requested and reported Slurm job IDs disagree")
    partition = text_field(job_output, "Partition", "Slurm allocation")
    node_list = text_field(job_output, "NodeList", "Slurm allocation")
    job_sharing_match = re.search(
        r"(?:^| )(?:OverSubscribe|Shared)=([^ ]+)(?: |$)", job_output
    )
    if job_sharing_match is None:
        raise BenchmarkToolError(
            "Slurm allocation has no OverSubscribe/Shared policy field"
        )
    job_oversubscribe = job_sharing_match.group(1)
    if partition_output is None:
        partition_output = _command_output(
            ["scontrol", "show", "partition", "-o", partition],
            "Slurm partition sharing policy",
        )
    partition_name = text_field(
        partition_output, "PartitionName", "Slurm partition"
    )
    partition_oversubscribe = text_field(
        partition_output, "OverSubscribe", "Slurm partition"
    )
    if partition_name != partition:
        raise BenchmarkToolError("Slurm job and partition policy name disagree")
    if not partition_oversubscribe.startswith("FORCE:"):
        raise BenchmarkToolError(
            "matched allocation partition does not force the recorded sharing policy"
        )
    if job_oversubscribe != "OK":
        raise BenchmarkToolError(
            "matched allocation does not expose the expected non-exclusive sharing state"
        )
    return {
        "partition": partition,
        "job_oversubscribe": job_oversubscribe,
        "partition_oversubscribe": partition_oversubscribe,
        "node_list": node_list,
        "exclusive": False,
        "sharing_policy": "partition_forced_oversubscription",
        "dynamic_co_tenant_count_recorded": False,
    }


def _verify_host_class(environment: Mapping[str, Any], frozen: Mapping[str, Any]) -> dict[str, Any]:
    host = _mapping(environment.get("host_class"), "environment.host_class")
    _validate_hardware_matching_policy(
        environment.get("hardware_matching_policy"),
        "environment.hardware_matching_policy",
    )
    actual_kernel = f"{platform.system()} {platform.release()} {platform.machine()}"
    actual_virtualization = _command_output(
        ["systemd-detect-virt", "--container"], "container virtualization"
    ).splitlines()[-1]
    actual = {
        "kernel": actual_kernel,
        "virtualization": actual_virtualization.upper(),
        **_cpu_identity(),
        **_allocated_cpu_topology(),
        "visible_memory_bytes": _visible_memory_bytes(),
        "allocation_memory_limit_bytes": _cgroup_memory_limit_bytes(),
        **_slurm_allocation_shape(),
    }
    if actual["allocation_memory_limit_bytes"] != actual["slurm_allocated_memory_bytes"]:
        raise BenchmarkToolError(
            "Slurm allocated memory disagrees with the effective cgroup memory limit"
        )
    _verify_host_against_pair_policy(host, actual, label="current allocation")
    if frozen.get("operating_system") != actual_kernel:
        raise BenchmarkToolError("config operating_system does not match the current host")
    hardware = frozen.get("hardware_class")
    if not isinstance(hardware, str) or not hardware:
        raise BenchmarkToolError("config has no frozen hardware class")
    hostname = _nonempty_string(platform.node().strip(), "allocation hostname")
    if hostname not in HARDWARE_MATCHING_POLICY["vetted_nodes"]:
        raise BenchmarkToolError(
            f"allocation host {hostname!r} is not in the paired-hardware vetted-node set"
        )
    return actual


def _match_optional_claim(args: argparse.Namespace, field: str, frozen: Any) -> None:
    claimed = getattr(args, field, None)
    if claimed is not None and claimed != frozen:
        raise BenchmarkToolError(
            f"command-line {field.replace('_', '-')}={claimed!r} disagrees with frozen {frozen!r}"
        )
    setattr(args, field, frozen)


def verify_frozen_run_environment(
    args: argparse.Namespace,
    root: Path,
    *,
    regenerating_token_control_canary: bool = False,
    regenerating_ultra_orchestration_canary: bool = False,
) -> dict[str, Any]:
    """Verify the complete frozen execution bundle before any attempt starts.

    The returned identity and limits come from the checked metadata.  Caller
    arguments can only assert matching values; they cannot redefine a run.
    """

    project = args.project_root.resolve()
    if args.packages_root.resolve() != (project / ".lake" / "packages").resolve():
        raise BenchmarkToolError("packages_root is not the project .lake/packages tree")
    if args.library_source.resolve() != (project / "NumStability").resolve():
        raise BenchmarkToolError("library_source is not project_root/NumStability")
    if args.library_root_file.resolve() != (project / "NumStability.lean").resolve():
        raise BenchmarkToolError("library_root_file is not project_root/NumStability.lean")
    config = _mapping(read_json(root / "metadata" / "config.json"), "config")
    environment = _mapping(
        read_json(root / "metadata" / "environment.json"), "environment record"
    )
    manifest = _mapping(read_json(root / "metadata" / "manifest.json"), "manifest")
    run_order = _mapping(read_json(root / "metadata" / "run_order.json"), "run order")
    benchmark_id = _fixed_value(
        "benchmark id",
        config.get("benchmark_id"),
        manifest.get("benchmark_id"),
        run_order.get("benchmark_id"),
    )
    frozen = _mapping(config.get("frozen_environment"), "config.frozen_environment")
    lean = _mapping(environment.get("lean"), "environment.lean")
    agent = _mapping(environment.get("agent"), "environment.agent")
    isolation = _mapping(environment.get("isolation"), "environment.isolation")
    runtime = _mapping(environment.get("runtime"), "environment.runtime")
    python_record = _mapping(runtime.get("python"), "environment.runtime.python")
    session_isolation_check = _verify_agent_session_isolation(config, environment)
    frozen_prompt_protocol, execution_components = production_freeze_bindings(
        config, environment
    )
    configured_provider_gate = environment.get("provider_token_gate")
    if not isinstance(configured_provider_gate, Mapping):
        raise BenchmarkToolError(
            "frozen provider-token-gate environment record must be an object"
        )
    configured_provider_gate_sha256 = _sha256_value(
        frozen.get("provider_token_gate_sha256"),
        "frozen provider-token-gate environment-record SHA-256",
    )
    if canonical_document_digest(configured_provider_gate) != (
        configured_provider_gate_sha256
    ):
        raise BenchmarkToolError(
            "provider-token-gate environment-record SHA-256 is invalid"
        )
    policy = _validate_hardware_matching_policy(
        environment.get("hardware_matching_policy"),
        "environment.hardware_matching_policy",
    )
    frozen_policy = _validate_hardware_matching_policy(
        frozen.get("hardware_matching_policy"),
        "config.frozen_environment.hardware_matching_policy",
    )
    if frozen_policy != policy:
        raise BenchmarkToolError(
            "paired-hardware policy disagrees across frozen metadata"
        )
    actual_provider_gate = provider_token_gate_environment_record(root)
    if _provider_gate_without_node_local_hosts(
        configured_provider_gate, label="frozen provider-token-gate"
    ) != _provider_gate_without_node_local_hosts(
        actual_provider_gate, label="actual provider-token-gate"
    ):
        raise BenchmarkToolError(
            "actual provider-token-gate source/catalog/transport differs from the "
            "freeze outside the node-local hosts-file allowance"
        )
    configured_gate_implementation = _mapping(
        configured_provider_gate.get("implementation"),
        "frozen provider-token-gate implementation",
    )
    if (
        configured_gate_implementation.get("source_sha256")
        != execution_components.get("provider_token_gate_sha256")
    ):
        raise BenchmarkToolError(
            "provider-token-gate source disagrees with execution components"
        )

    if config.get("failure_reason_priority") != list(
        EXPECTED_FAILURE_REASON_PRIORITY
    ):
        raise BenchmarkToolError(
            "failure-reason priority does not match the HighamBench specification"
        )

    environment_id = _fixed_value(
        "environment id", frozen.get("environment_id"), environment.get("environment_id")
    )
    bundle_digest = _fixed_value(
        "environment bundle SHA-256",
        frozen.get("environment_bundle_sha256"),
        environment.get("environment_bundle_sha256"),
    )
    if not isinstance(bundle_digest, str) or not re.fullmatch(r"[0-9a-f]{64}", bundle_digest):
        raise BenchmarkToolError("environment bundle SHA-256 is invalid")
    if environment.get("environment_bundle_definition") != ENVIRONMENT_BUNDLE_DEFINITION:
        raise BenchmarkToolError("environment bundle definition does not name the implemented algorithm")
    actual_bundle_digest = environment_bundle_digest(config, environment)
    if bundle_digest != actual_bundle_digest:
        raise BenchmarkToolError(
            "environment_bundle_sha256 does not match the canonical config/environment payload"
        )
    expected_environment_id = f"highambench-{corpus_slug(manifest)}-{bundle_digest[:16]}"
    if environment_id != expected_environment_id:
        raise BenchmarkToolError("environment_id is not derived from the frozen bundle SHA-256")

    agent_id = _fixed_value("agent id", frozen.get("agent_id"), agent.get("id"))
    agent_version = _fixed_value(
        "agent version", frozen.get("agent_version"), agent.get("version")
    )
    model = _fixed_value("model", frozen.get("model_version"), agent.get("model"))
    reasoning_effort = _fixed_value(
        "model reasoning effort",
        frozen.get("model_reasoning_effort"),
        agent.get("reasoning_effort"),
    )
    if model != FROZEN_MODEL_VERSION:
        raise BenchmarkToolError(
            f"frozen model must be {FROZEN_MODEL_VERSION!r} for this snapshot"
        )
    if reasoning_effort != FROZEN_REASONING_EFFORT:
        raise BenchmarkToolError(
            "frozen reasoning effort must be full Ultra for this snapshot"
        )
    frozen_ultra = _mapping(
        frozen.get("ultra_orchestration"),
        "config.frozen_environment.ultra_orchestration",
    )
    agent_ultra = _mapping(
        agent.get("ultra_orchestration"),
        "environment.agent.ultra_orchestration",
    )
    expected_ultra = ultra_orchestration_record()
    if dict(frozen_ultra) != expected_ultra or dict(agent_ultra) != expected_ultra:
        raise BenchmarkToolError(
            "frozen full-Ultra projection-v6 orchestration metadata is missing or inconsistent"
        )
    prompt_digest = _fixed_value(
        "prompt SHA-256", frozen.get("prompt_sha256"), agent.get("prompt_sha256")
    )
    binary_digest = _fixed_value(
        "Codex binary SHA-256",
        frozen.get("agent_binary_sha256"),
        agent.get("binary_sha256"),
    )
    for label, digest in (
        ("prompt SHA-256", prompt_digest),
        ("Codex binary SHA-256", binary_digest),
    ):
        if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise BenchmarkToolError(f"{label} is invalid")
    prompt_protocol = _verify_prompt_protocol(
        root,
        frozen,
        agent,
        common_prompt_sha256=prompt_digest,
    )
    if prompt_protocol != frozen_prompt_protocol:
        raise BenchmarkToolError("verified production prompt protocol is inconsistent")

    limits = _mapping(config.get("limits"), "config.limits")
    wall_limit = limits.get("wall_clock_seconds")
    token_limit = limits.get("total_model_tokens")
    prompt_startup_timeout = _fixed_value(
        "prompt startup timeout",
        limits.get("prompt_startup_timeout_seconds"),
        runtime.get("prompt_startup_timeout_seconds"),
    )
    post_submission_validation_reserve = _fixed_value(
        "post-submission validation reserve",
        limits.get("post_submission_validation_reserve_seconds"),
        runtime.get("post_submission_validation_reserve_seconds"),
    )
    if not isinstance(wall_limit, int) or isinstance(wall_limit, bool) or wall_limit <= 0:
        raise BenchmarkToolError("frozen wall-clock limit is not a positive integer")
    if not isinstance(token_limit, int) or isinstance(token_limit, bool) or token_limit <= 0:
        raise BenchmarkToolError("frozen model-token limit is not a positive integer")
    if (
        isinstance(prompt_startup_timeout, bool)
        or not isinstance(prompt_startup_timeout, (int, float))
        or float(prompt_startup_timeout) != DEFAULT_PROMPT_STARTUP_TIMEOUT_SECONDS
    ):
        raise BenchmarkToolError(
            "frozen prompt startup timeout must be exactly 120 seconds"
        )
    if (
        isinstance(post_submission_validation_reserve, bool)
        or not isinstance(post_submission_validation_reserve, (int, float))
        or float(post_submission_validation_reserve)
        != DEFAULT_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS
    ):
        raise BenchmarkToolError(
            "frozen post-submission validation reserve must be exactly 369 seconds"
        )
    if limits.get("failure_scored_time_seconds") != wall_limit:
        raise BenchmarkToolError("failure scored time must equal the frozen wall-clock limit")
    submission_barrier = _mapping(
        expected_ultra.get("submission_barrier"),
        "frozen Ultra submission barrier",
    )
    barrier_wall_seconds = submission_barrier.get(
        "outer_exec_yield_attempt_wall_seconds"
    )
    barrier_reserve_seconds = submission_barrier.get(
        "outer_exec_yield_post_submission_validation_reserve_seconds"
    )
    barrier_envelope_ms = submission_barrier.get("outer_exec_yield_envelope_ms")
    barrier_yield_ms = submission_barrier.get("outer_exec_yield_time_ms")
    barrier_margin_ms = submission_barrier.get("outer_exec_yield_margin_ms")
    if (
        wall_limit != 1_800
        or wall_limit != barrier_wall_seconds
        or float(post_submission_validation_reserve) != 369.0
        or barrier_reserve_seconds != 369
        or type(barrier_envelope_ms) is not int
        or type(barrier_yield_ms) is not int
        or type(barrier_margin_ms) is not int
        or barrier_envelope_ms
        != 1_000 * (barrier_wall_seconds + barrier_reserve_seconds)
        or barrier_margin_ms != barrier_yield_ms - barrier_envelope_ms
        or barrier_margin_ms != 231_000
        or barrier_yield_ms <= barrier_envelope_ms
        or submission_barrier.get(
            "outer_exec_timer_starts_at_or_after_prompt_release"
        )
        is not True
        or submission_barrier.get("outer_exec_yield_exceeds_envelope") is not True
    ):
        raise BenchmarkToolError(
            "frozen limits and submission-barrier yield envelope disagree"
        )

    config_token_control = _mapping(
        config.get("token_control"), "config.token_control"
    )
    environment_token_control = _mapping(
        environment.get("token_control"), "environment.token_control"
    )
    if dict(config_token_control) != dict(environment_token_control):
        raise BenchmarkToolError(
            "frozen token-control metadata disagrees between config and environment"
        )
    expected_live_control = {
        "control": "loopback_provider_response_admission_gate",
        "measurement_source": "codex_app_server_rawResponse/completed",
        "notification": "rawResponse/completed",
        "live_cumulative": True,
        "usage_scope": "rooted_attempt_thread_tree_completed_responses",
        "input_includes_cached": True,
        "cached_input_counted_once": True,
        "outer_runner_polling": True,
        "checked_before_submission_validation": True,
        "comparison": ">=",
        "limit_tokens": token_limit,
        "concurrent_inflight_overshoot_possible": False,
        "one_response_overshoot_possible": True,
        "over_limit_pass_allowed": False,
        "all_descendant_threads_included": True,
        "response_ids_deduplicated": True,
        "measurement_exact_required": True,
        "root_completion_is_tree_barrier": False,
        "trusted_adapter_freezes_first_threshold": True,
        "trusted_adapter_latches_first_threshold": True,
        "trusted_usage_path_outside_workspace": True,
        "live_update_sequence": True,
        "provider_gate_protocol": ultra_canary.runner.PROVIDER_GATE_PROTOCOL,
        "provider_response_bound_tokens": 272_000,
        "strict_admission_inequality": (
            "completed_tokens + (open_request_count + 1) * "
            "response_bound < token_limit"
        ),
        "crossing_response_release": (
            ultra_canary.runner.PROVIDER_GATE_CROSSING_RELEASE_POLICY
        ),
        "crossing_response_actions_released": False,
        "provider_requests_quiescent_at_scored_endpoint": True,
        "tree_quiescence_distinct_from_provider_quiescence": True,
        "outcome_exactness": {
            "accepted_proof": {
                "required_evidence": "exact_authenticated_submission_boundary",
                "provider_gate_close_reason": "accepted_submission",
                "provider_requests_quiescent": True,
                "drain_complete": False,
                "measurement_exact": True,
                "submission_boundary_exact": True,
                "root_turn_active": True,
                "descendants_quiescent": True,
                "later_model_response_possible": False,
            },
            "token_limit": {
                "required_evidence": "sealed_sanitized_sole_inflight_crossing",
                "provider_gate_close_reason": "token_limit",
                "provider_requests_quiescent": True,
                "tree_quiescent": False,
                "drain_complete": False,
                "measurement_exact": True,
                "crossing_response_actions_released": False,
            },
            "scored_failure": {
                "required_evidence": "exact_natural_drain",
                "provider_gate_close_reason": "natural_end",
                "provider_requests_quiescent": True,
                "drain_complete": True,
                "measurement_exact": True,
                "tree_quiescent": True,
            },
            "unscorable_useful_work": {
                "trigger": (
                    "no_exact_authenticated_provider_gate_endpoint_for_outcome"
                ),
                "matrix_action": "abort_and_preserve_incident",
                "retry_allowed": False,
                "scored": False,
            },
        },
    }
    for field, expected in expected_live_control.items():
        if config_token_control.get(field) != expected:
            raise BenchmarkToolError(
                f"frozen token-control field {field!r} is not {expected!r}"
            )
    advisory_rollout = _mapping(
        config_token_control.get("advisory_rollout_budget"),
        "config.token_control.advisory_rollout_budget",
    )
    expected_advisory = {
        "enabled": True,
        "feature": "rollout_budget",
        "strict_config": True,
        "limit_tokens": token_limit,
        "prefill_token_weight": 1,
        "sampling_token_weight": 1,
        "role": "advisory_only",
    }
    for field, expected in expected_advisory.items():
        if advisory_rollout.get(field) != expected:
            raise BenchmarkToolError(
                f"frozen advisory rollout-budget field {field!r} is not {expected!r}"
            )
    frozen_rollout_row = advisory_rollout.get("feature_row")
    if not isinstance(frozen_rollout_row, str) or not frozen_rollout_row.startswith(
        "rollout_budget "
    ):
        raise BenchmarkToolError("frozen advisory rollout-budget feature row is invalid")
    _match_optional_claim(args, "agent_id", agent_id)
    _match_optional_claim(args, "agent_version", agent_version)
    _match_optional_claim(args, "model", model)
    _match_optional_claim(args, "reasoning_effort", reasoning_effort)
    _match_optional_claim(args, "time_limit_seconds", wall_limit)
    _match_optional_claim(args, "token_limit", token_limit)
    _match_optional_claim(
        args, "prompt_startup_timeout_seconds", prompt_startup_timeout
    )
    _match_optional_claim(
        args,
        "post_submission_validation_reserve_seconds",
        post_submission_validation_reserve,
    )
    # There is intentionally no --environment-id input.  This is the only
    # assignment of the value used by runner_command.
    args.environment_id = environment_id

    release_relative = _fixed_value(
        "release manifest path",
        frozen.get("release_manifest"),
        environment.get("release_manifest"),
    )
    if release_relative != FROZEN_RELEASE_MANIFEST_PATH:
        raise BenchmarkToolError(
            f"frozen release manifest path must be {FROZEN_RELEASE_MANIFEST_PATH}"
        )
    release_digest = _fixed_value(
        "release manifest SHA-256",
        frozen.get("release_manifest_sha256"),
        environment.get("release_manifest_sha256"),
    )
    release_check = _verify_release_manifest(root, getattr(args, "release_manifest", None))
    if release_check["sha256"] != release_digest:
        raise BenchmarkToolError("global release manifest does not match its frozen SHA-256")
    host_check = _verify_host_class(environment, frozen)

    python_version = _fixed_value(
        "Python version", frozen.get("python_version"), python_record.get("version")
    )
    python_binary_digest = _fixed_value(
        "Python binary SHA-256",
        frozen.get("python_binary_sha256"),
        python_record.get("binary_sha256"),
    )
    if platform.python_version() != python_version:
        raise BenchmarkToolError(
            f"actual Python version {platform.python_version()!r} does not match "
            f"frozen {python_version!r}"
        )
    python_executable = _require_file(Path(sys.executable), "Python executable")
    if not isinstance(python_binary_digest, str) or not re.fullmatch(
        r"[0-9a-f]{64}", python_binary_digest
    ):
        raise BenchmarkToolError("Python binary SHA-256 is invalid")
    if sha256_file(python_executable) != python_binary_digest:
        raise BenchmarkToolError(
            "actual Python executable does not match its frozen SHA-256"
        )

    actual_binary_digest = sha256_file(args.codex.resolve())
    if actual_binary_digest != binary_digest:
        raise BenchmarkToolError("actual Codex binary does not match its frozen SHA-256")
    codex_output = _command_output([str(args.codex.resolve()), "--version"], "Codex version")
    version_match = re.search(r"(?:codex(?:-cli)?\s+)(\S+)", codex_output)
    if version_match is None or version_match.group(1) != agent_version:
        raise BenchmarkToolError(
            f"actual Codex version {codex_output!r} does not match {agent_version!r}"
        )
    feature_output = _command_output(
        [str(args.codex.resolve()), "features", "list"], "Codex feature list"
    )
    rollout_row = next(
        (
            " ".join(line.split())
            for line in feature_output.splitlines()
            if line.split() and line.split()[0] == "rollout_budget"
        ),
        None,
    )
    if rollout_row is None:
        raise BenchmarkToolError(
            "frozen Codex binary does not expose the advisory rollout_budget feature"
        )
    if rollout_row != frozen_rollout_row:
        raise BenchmarkToolError(
            "actual Codex advisory rollout_budget feature row does not match metadata"
        )
    # The scored ceiling is enforced by the outer runner from live cumulative
    # app-server notifications.  rollout_budget remains enabled as a secondary,
    # explicitly advisory guard; it is not the cached-inclusive measurement.
    args.token_control_verified = True
    if regenerating_token_control_canary:
        # The replacement canary cannot require itself as an input. The global
        # release manifest above still authenticates the complete pre-canary
        # tree, including the superseded evidence. Only this dedicated canary
        # path may bypass semantic validation of that one evidence record;
        # ordinary matrix startup never sets this keyword.
        token_control_canary_check = {
            "status": "replacement_canary_regeneration",
            "semantic_verification_skipped": True,
            "reason": "the authenticated live canary is the replacement evidence being generated",
        }
    else:
        token_control_canary_check = _verify_token_control_canary(
            project,
            frozen,
            environment,
            benchmark_id=benchmark_id,
            token_limit=token_limit,
            agent_id=agent_id,
            agent_version=agent_version,
            model=model,
            reasoning_effort=reasoning_effort,
            agent_binary_sha256=actual_binary_digest,
            prompt_protocol=prompt_protocol,
            execution_components=execution_components,
        )

    if regenerating_ultra_orchestration_canary:
        ultra_orchestration_canary_check = {
            "status": "replacement_canary_regeneration",
            "semantic_verification_skipped": True,
            "reason": (
                "the authenticated synthetic Ultra orchestration canary is the "
                "replacement evidence being generated"
            ),
        }
    else:
        ultra_orchestration_canary_check = _verify_ultra_orchestration_canary(
            project,
            frozen,
            environment,
            benchmark_id=benchmark_id,
            token_limit=token_limit,
            agent_id=agent_id,
            agent_version=agent_version,
            model=model,
            reasoning_effort=reasoning_effort,
            agent_binary_sha256=actual_binary_digest,
            prompt_protocol=prompt_protocol,
            execution_components=execution_components,
        )

    expected_lean_commit = _fixed_value(
        "Lean commit", frozen.get("lean_commit"), lean.get("commit")
    )
    lean_executable = _require_file(args.toolchain_root / "bin" / "lean", "Lean executable")
    expected_lean_binary = _fixed_value(
        "Lean binary SHA-256",
        frozen.get("lean_binary_sha256"),
        lean.get("binary_sha256"),
    )
    if sha256_file(lean_executable) != expected_lean_binary:
        raise BenchmarkToolError("actual Lean executable does not match frozen SHA-256")
    lean_output = _command_output([str(lean_executable), "--version"], "Lean version")
    lean_match = re.search(
        r"Lean \(version ([^,]+),.*?commit ([0-9a-f]{40}),", lean_output
    )
    if lean_match is None:
        raise BenchmarkToolError(f"cannot parse Lean version output: {lean_output!r}")
    expected_lean_version = lean.get("version")
    if lean_match.group(1) != expected_lean_version or lean_match.group(2) != expected_lean_commit:
        raise BenchmarkToolError("actual Lean version or commit does not match frozen metadata")
    toolchain = frozen.get("lean_toolchain")
    if not isinstance(toolchain, str) or toolchain.rsplit(":v", 1)[-1] != expected_lean_version:
        raise BenchmarkToolError("Lean toolchain name disagrees with the environment record")

    expected_mathlib = _fixed_value(
        "mathlib commit", frozen.get("mathlib_commit"), lean.get("mathlib_commit")
    )
    expected_numstability = _fixed_value(
        "NumStability commit",
        frozen.get("numstability_commit"),
        lean.get("numstability_commit"),
    )
    mathlib_repository = _require_dir(args.packages_root / "mathlib", "mathlib repository")
    if _git_head(mathlib_repository, "mathlib commit") != expected_mathlib:
        raise BenchmarkToolError("actual mathlib commit does not match frozen metadata")
    _require_git_commit(project, expected_numstability, "NumStability baseline commit")
    _require_git_paths_equal(
        project,
        expected_numstability,
        "HEAD",
        ["NumStability", "NumStability.lean"],
        "NumStability source tree",
    )
    _require_git_sources_clean(mathlib_repository, ["Mathlib", "Mathlib.lean"], "mathlib")
    _require_git_sources_clean(project, ["NumStability", "NumStability.lean"], "NumStability")

    source_manifest_relative = _fixed_value(
        "NumStability source manifest path",
        frozen.get("numstability_source_manifest"),
        lean.get("numstability_source_manifest"),
    )
    source_manifest_digest = _fixed_value(
        "NumStability source manifest SHA-256",
        frozen.get("numstability_source_manifest_sha256"),
        lean.get("numstability_source_manifest_sha256"),
    )
    source_manifest_path = (project / str(source_manifest_relative)).resolve()
    try:
        source_manifest_path.relative_to(project)
    except ValueError as error:
        raise BenchmarkToolError("NumStability source manifest path escapes project root") from error
    _require_file(source_manifest_path, "NumStability source manifest")
    if sha256_file(source_manifest_path) != source_manifest_digest:
        raise BenchmarkToolError("NumStability source manifest has the wrong SHA-256")
    source_manifest = load_manifest(source_manifest_path)
    source_check = verify_manifest(project, source_manifest)
    if not source_check["ok"]:
        raise BenchmarkToolError(f"NumStability source tree is not frozen: {source_check}")
    listed_source = {entry["path"] for entry in source_manifest["files"]}
    actual_source = {"NumStability.lean"}
    for path in (project / "NumStability").rglob("*"):
        if path.is_symlink():
            raise BenchmarkToolError(f"NumStability source tree contains a symlink: {path}")
        if path.is_file():
            actual_source.add(path.relative_to(project).as_posix())
    if listed_source != actual_source:
        raise BenchmarkToolError(
            "NumStability source manifest is not exact "
            f"(extra={sorted(actual_source - listed_source)[:8]}, "
            f"missing={sorted(listed_source - actual_source)[:8]})"
        )

    compiled_environment_check = _verify_compiled_environment_summary(
        args, project, frozen, lean
    )
    packages_runtime_check = _verify_packages_runtime(
        args, project, frozen, runtime
    )

    actual_prompt = _require_file(root / "agent_prompt.md", "agent prompt")
    if sha256_file(actual_prompt) != prompt_digest:
        raise BenchmarkToolError("agent prompt does not match frozen SHA-256")
    shared_entries = _controlled_shared_entries(manifest)
    expected_shared_sources = {
        PurePosixPath(relative).relative_to("shared").as_posix(): entry["sha256"]
        for relative, entry, _scope in shared_entries
    }
    frozen_shared_sources = _mapping(
        lean.get("shared_sources"), "environment.lean.shared_sources"
    )
    if dict(frozen_shared_sources) != expected_shared_sources:
        raise BenchmarkToolError(
            "frozen shared source hashes disagree with the controlled shared manifest"
        )
    for relative, expected in expected_shared_sources.items():
        shared_source = _require_file(root / "shared" / relative, f"shared source {relative}")
        if sha256_file(shared_source) != expected:
            raise BenchmarkToolError(f"shared source {relative} does not match frozen SHA-256")

    paper_ids = [str(paper["paper_id"]) for paper in _manifest_papers(manifest)]
    frozen_shared_bundles = _mapping(
        lean.get("shared_olean_bundles"),
        "environment.lean.shared_olean_bundles",
    )
    if set(frozen_shared_bundles) != set(paper_ids):
        raise BenchmarkToolError(
            "frozen shared olean bundles do not exactly cover the manifest papers"
        )
    expected_shared_olean_files: set[str] = set()
    for paper_id in paper_ids:
        bundle = _mapping(
            frozen_shared_bundles[paper_id], f"shared olean bundle {paper_id}"
        )
        expected_modules = {
            PurePosixPath(relative)
            .relative_to("shared")
            .with_suffix(".olean")
            .as_posix()
            for relative, _entry, scope in shared_entries
            if paper_id in scope
        }
        if set(bundle) != expected_modules:
            raise BenchmarkToolError(
                f"shared olean bundle {paper_id} does not match its paper-scoped sources"
            )
        for relative, raw_digest in bundle.items():
            expected = _sha256_value(
                raw_digest, f"shared olean {paper_id}/{relative} SHA-256"
            )
            shared_olean = _require_file(
                args.shared_olean_root / paper_id / relative,
                f"shared olean {paper_id}/{relative}",
            )
            if sha256_file(shared_olean) != expected:
                raise BenchmarkToolError(
                    f"shared olean {paper_id}/{relative} does not match frozen SHA-256"
                )
            expected_shared_olean_files.add(f"{paper_id}/{relative}")
    shared_files: set[str] = set()
    for path in args.shared_olean_root.resolve().rglob("*"):
        if path.is_symlink():
            raise BenchmarkToolError(f"shared olean root contains a symlink: {path}")
        if path.is_file():
            shared_files.add(path.relative_to(args.shared_olean_root.resolve()).as_posix())
    if shared_files != expected_shared_olean_files:
        raise BenchmarkToolError(
            f"shared olean root is not exact; found importable files {sorted(shared_files)}"
        )

    explicit_hashes = {
        root / "tools" / "codex_isolated.py": execution_components["filesystem_adapter_sha256"],
        root / "tools" / "provider_token_gate.py": execution_components["provider_token_gate_sha256"],
        root / "tools" / "lean_isolated.py": execution_components["lean_adapter_sha256"],
        root / "tools" / "offline_shell.c": execution_components["offline_shell_source_sha256"],
        root / "tools" / "runner.py": execution_components["runner_sha256"],
        root / "tools" / "validator.py": execution_components["validator_sha256"],
        root / "tools" / "dependency_audit.lean": execution_components["dependency_audit_sha256"],
        args.offline_shell.resolve(): execution_components["offline_shell_binary_sha256"],
    }
    for path, expected in explicit_hashes.items():
        _require_file(path, f"frozen component {path.name}")
        if not isinstance(expected, str) or sha256_file(path) != expected:
            raise BenchmarkToolError(f"{path.name} does not match its frozen SHA-256")

    bwrap = _require_file(Path("/bin/bwrap"), "bubblewrap executable")
    bwrap_digest = _fixed_value(
        "bubblewrap binary SHA-256",
        frozen.get("bubblewrap_binary_sha256"),
        isolation.get("bubblewrap_binary_sha256"),
    )
    if sha256_file(bwrap) != bwrap_digest:
        raise BenchmarkToolError("actual bubblewrap executable does not match frozen SHA-256")
    bwrap_version = _fixed_value(
        "bubblewrap version",
        frozen.get("bubblewrap_version"),
        isolation.get("bubblewrap_version"),
    )
    actual_bwrap_version = _command_output([str(bwrap), "--version"], "bubblewrap version")
    if actual_bwrap_version != bwrap_version:
        raise BenchmarkToolError("actual bubblewrap version does not match frozen metadata")

    compiled_path = _fixed_value(
        "NumStability compiled manifest path",
        frozen.get("numstability_compiled_manifest"),
        lean.get("numstability_compiled_manifest"),
    )
    compiled_digest = _fixed_value(
        "NumStability compiled manifest SHA-256",
        frozen.get("numstability_compiled_manifest_sha256"),
        lean.get("numstability_compiled_manifest_sha256"),
    )
    compiled_manifest_path = (project / str(compiled_path)).resolve()
    try:
        compiled_manifest_path.relative_to(project)
    except ValueError as error:
        raise BenchmarkToolError("compiled-library manifest path escapes project root") from error
    _require_file(compiled_manifest_path, "NumStability compiled manifest")
    if sha256_file(compiled_manifest_path) != compiled_digest:
        raise BenchmarkToolError("compiled-library manifest file has the wrong SHA-256")
    compiled_manifest = load_manifest(compiled_manifest_path)
    compiled_check = verify_manifest(args.library_olean.resolve(), compiled_manifest)
    if not compiled_check["ok"]:
        raise BenchmarkToolError(f"compiled NumStability tree is not frozen: {compiled_check}")
    listed_compiled = {entry["path"] for entry in compiled_manifest["files"]}
    actual_compiled: set[str] = set()
    for path in args.library_olean.resolve().rglob("*"):
        if path.is_symlink():
            raise BenchmarkToolError(f"compiled NumStability tree contains a symlink: {path}")
        if path.is_file():
            actual_compiled.add(path.relative_to(args.library_olean.resolve()).as_posix())
    if actual_compiled != listed_compiled:
        raise BenchmarkToolError(
            "compiled NumStability mount is not the exact pruned manifest tree "
            f"(extra={sorted(actual_compiled - listed_compiled)[:8]}, "
            f"missing={sorted(listed_compiled - actual_compiled)[:8]})"
        )

    return {
        "schema_version": 1,
        "kind": "highambench-frozen-run-verification",
        "ok": True,
        "benchmark_id": benchmark_id,
        "environment_id": environment_id,
        "environment_bundle_sha256": bundle_digest,
        "agent": {
            "id": agent_id,
            "version": agent_version,
            "binary_sha256": actual_binary_digest,
            "model": model,
            "reasoning_effort": reasoning_effort,
            "ultra_orchestration": expected_ultra,
        },
        "python": {
            "version": python_version,
            "binary_sha256": python_binary_digest,
        },
        "token_control": json.loads(
            json.dumps(config_token_control, sort_keys=True)
        ),
        "token_control_canary": token_control_canary_check,
        "ultra_orchestration_canary": ultra_orchestration_canary_check,
        "agent_session_isolation": session_isolation_check,
        "prompt_protocol": prompt_protocol,
        "execution_components": json.loads(
            json.dumps(execution_components, sort_keys=True)
        ),
        "provider_token_gate": json.loads(
            json.dumps(actual_provider_gate, sort_keys=True)
        ),
        "hardware_matching_policy": policy,
        "lean": {
            "version": lean_match.group(1),
            "commit": lean_match.group(2),
            "binary_sha256": expected_lean_binary,
            "mathlib_commit": expected_mathlib,
            "numstability_commit": expected_numstability,
            "compiled_files_verified": compiled_check["verified"],
            "source_files_verified": source_check["verified"],
            "shared_source_files_verified": len(expected_shared_sources),
            "shared_olean_files_verified": len(expected_shared_olean_files),
        },
        "host_class": host_check,
        "limits": {
            "wall_clock_seconds": wall_limit,
            "total_model_tokens": token_limit,
            "prompt_startup_timeout_seconds": float(prompt_startup_timeout),
            "post_submission_validation_reserve_seconds": float(
                post_submission_validation_reserve
            ),
        },
        "release_manifest": release_check,
        "packages_runtime": packages_runtime_check,
        "compiled_environment_summary": compiled_environment_check,
        "bubblewrap": {"version": bwrap_version, "binary_sha256": bwrap_digest},
        "metadata_document_sha256": {
            "config": canonical_document_digest(config),
            "environment": canonical_document_digest(environment),
            "manifest": canonical_document_digest(manifest),
            "run_order": canonical_document_digest(run_order),
        },
    }


def _result_artifact_path(results_root: Path, raw: Any, label: str) -> Path:
    """Resolve one authenticated result artifact below the results root."""

    if isinstance(raw, Path):
        candidate = raw
    elif isinstance(raw, str) and raw:
        candidate = Path(raw)
    else:
        raise BenchmarkToolError(f"{label} path is missing")
    root = results_root.resolve()
    if not candidate.is_absolute():
        candidate = root / candidate
    if candidate.is_symlink() or not candidate.is_file():
        raise BenchmarkToolError(f"{label} is not a regular non-symlink file")
    candidate = candidate.resolve()
    try:
        candidate.relative_to(root)
    except ValueError as error:
        raise BenchmarkToolError(f"{label} escapes the results root") from error
    return candidate


def _result_artifact_descriptor(
    results_root: Path, raw: Any, label: str, *, nonempty: bool = False
) -> dict[str, str]:
    path = _result_artifact_path(results_root, raw, label)
    if nonempty and path.stat().st_size <= 0:
        raise BenchmarkToolError(f"{label} is empty")
    return {
        "path": path.relative_to(results_root.resolve()).as_posix(),
        "sha256": sha256_file(path),
    }


def _copy_incident_logs(
    record: dict[str, Any],
    incidents: Path,
    suffix: str,
    *,
    results_root: Path,
) -> None:
    incidents.mkdir(parents=True, exist_ok=True)
    for field in ("agent_log", "validation_log"):
        raw = record.get(field)
        if raw is None:
            continue
        source = _result_artifact_path(
            results_root, raw, f"matrix incident source {field}"
        )
        destination = incidents / f"{record.get('run_id')}.{suffix}.{source.name}"
        if destination.is_symlink():
            raise BenchmarkToolError(f"matrix incident {field} destination is a symlink")
        shutil.copy2(source, destination)
        copied = _result_artifact_descriptor(
            results_root, destination, f"matrix incident copied {field}"
        )
        if copied["sha256"] != sha256_file(source):
            raise BenchmarkToolError(f"matrix incident copied {field} is corrupt")
        record[field] = copied["path"]


def _retained_request_matches_boundary(
    record: Mapping[str, Any], boundary: Mapping[str, Any]
) -> bool:
    """Reauthenticate the sealed request and derive its schema-v5 event order."""

    retained = record.get("ultra_submission_boundary")
    artifacts = retained.get("artifacts") if isinstance(retained, Mapping) else None
    descriptor = artifacts.get("request") if isinstance(artifacts, Mapping) else None
    if not isinstance(descriptor, Mapping):
        return False
    path_raw = descriptor.get("path")
    if not isinstance(path_raw, str) or not path_raw:
        return False
    path = Path(path_raw)
    try:
        if (
            not path.is_absolute()
            or not path.is_file()
            or path.is_symlink()
            or path.stat().st_mode & 0o777 != 0o444
            or sha256_file(path) != descriptor.get("file_sha256")
        ):
            return False
        request = ultra_canary.codex_isolated.verify_authenticated_record(
            read_json(path), "request_sha256"
        )
    except (OSError, RuntimeError, BenchmarkToolError):
        return False
    if (
        request.get("schema_version")
        != ultra_canary.codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION
        or request.get("kind") != "highambench_submission_request"
        or request.get("request_sha256") != descriptor.get("record_sha256")
    ):
        return False
    captured_ns = request.get("captured_at_monotonic_ns")
    response_ns = request.get("raw_response_observed_at_monotonic_ns")
    published_ns = request.get("request_published_at_monotonic_ns")
    if any(
        type(value) is not int or value <= 0
        for value in (captured_ns, response_ns, published_ns)
    ):
        return False
    assert isinstance(captured_ns, int)
    assert isinstance(response_ns, int)
    assert isinstance(published_ns, int)
    dynamic_before = request.get(
        "dynamic_call_observed_before_raw_response_completed"
    )
    response_before = request.get(
        "raw_response_completed_before_dynamic_call_observed"
    )
    order = request.get("submission_event_order")
    valid_order = (
        (
            dynamic_before is True
            and response_before is False
            and order
            == ultra_canary.codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
            and captured_ns < response_ns
        )
        or (
            dynamic_before is False
            and response_before is True
            and order
            == ultra_canary.codex_isolated.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER
            and response_ns < captured_ns
        )
    )
    if (
        not valid_order
        or request.get("raw_response_completed_before_boundary_publication")
        is not True
        or response_ns > published_ns
        or captured_ns > published_ns
    ):
        return False
    bound_fields = (
        "schema_version",
        "sequence",
        "request_sha256",
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
        "thread_id",
        "turn_id",
        "response_id",
        "raw_response_notification_sequence",
        "candidate_path",
        "candidate_sha256",
        "candidate_size_bytes",
        "request_published_at_monotonic_ns",
        "submission_event_order",
        "dynamic_call_observed_before_raw_response_completed",
        "raw_response_completed_before_dynamic_call_observed",
        "raw_response_completed_before_boundary_publication",
    )
    return all(request.get(field) == boundary.get(field) for field in bound_fields)


def _accepted_pass_has_exact_boundary(record: Mapping[str, Any]) -> bool:
    usage = record.get("token_usage")
    if not isinstance(usage, Mapping):
        return False
    boundary = usage.get("submission_boundary")
    retained = record.get("ultra_submission_boundary")
    root_thread_id = usage.get("root_thread_id")
    inner_call_id = boundary.get("call_id") if isinstance(boundary, Mapping) else None
    outer_call_id = (
        boundary.get("outer_exec_call_id") if isinstance(boundary, Mapping) else None
    )
    outer_raw_item_id = (
        boundary.get("outer_raw_item_id") if isinstance(boundary, Mapping) else None
    )
    outer_observed_ns = (
        boundary.get("outer_raw_item_observed_at_monotonic_ns")
        if isinstance(boundary, Mapping)
        else None
    )
    inner_started_ns = (
        boundary.get("inner_dynamic_item_started_at_monotonic_ns")
        if isinstance(boundary, Mapping)
        else None
    )
    dynamic_before_response = (
        boundary.get("dynamic_call_observed_before_raw_response_completed")
        if isinstance(boundary, Mapping)
        else None
    )
    response_before_dynamic = (
        boundary.get("raw_response_completed_before_dynamic_call_observed")
        if isinstance(boundary, Mapping)
        else None
    )
    event_order = (
        boundary.get("submission_event_order")
        if isinstance(boundary, Mapping)
        else None
    )
    gate_close = (
        boundary.get("provider_gate_close")
        if isinstance(boundary, Mapping)
        else None
    )
    valid_event_order = (
        (
            dynamic_before_response is True
            and response_before_dynamic is False
            and event_order
            == ultra_canary.codex_isolated.SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
        )
        or (
            dynamic_before_response is False
            and response_before_dynamic is True
            and event_order
            == ultra_canary.codex_isolated.SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER
        )
    )
    return (
        record.get("pass") is True
        and record.get("scored") is True
        and type(record.get("agent_exit_code")) is int
        and record.get("agent_exit_code") == 0
        and record.get("failure_code") is None
        and usage.get("usage_scope")
        == "rooted_attempt_thread_tree_completed_responses"
        and usage.get("measurement_exact") is True
        and usage.get("submission_boundary_exact") is True
        and usage.get("drain_complete") is False
        and usage.get("tree_quiescent") is False
        and usage.get("stop_reason") == "first_valid_proof"
        and isinstance(root_thread_id, str)
        and bool(root_thread_id)
        and usage.get("active_thread_ids") == [root_thread_id]
        and usage.get("unresolved_thread_ids") == []
        and usage.get("invalid_reasons") == []
        and isinstance(boundary, Mapping)
        and boundary.get("authenticated") is True
        and boundary.get("status") == "accepted"
        and boundary.get("exact") is True
        and boundary.get("schema_version")
        == ultra_canary.codex_isolated.SUBMISSION_BARRIER_SCHEMA_VERSION
        and boundary.get("submission_transport")
        == ultra_canary.codex_isolated.NESTED_SUBMISSION_WIRE_FORMAT
        and boundary.get("outer_raw_item_type") == "custom_tool_call"
        and boundary.get("outer_exec_name") == "exec"
        and ultra_canary.codex_isolated.is_canonical_nested_submit_exec_input(
            boundary.get("outer_exec_program"), candidate_path="Candidate.lean"
        )
        and boundary.get("outer_exec_program_bytes")
        == ultra_canary.codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_BYTES
        and boundary.get("outer_exec_program_sha256")
        == ultra_canary.codex_isolated.NESTED_SUBMISSION_EXEC_SOURCE_SHA256
        and all(
            boundary.get(field) == expected
            for field, expected in (
                ultra_canary.codex_isolated.nested_submission_exec_yield_record().items()
            )
        )
        and isinstance(inner_call_id, str)
        and bool(inner_call_id)
        and boundary.get("inner_dynamic_call_id") == inner_call_id
        and boundary.get("inner_dynamic_tool_name") == "submit_proof"
        and boundary.get("inner_dynamic_arguments")
        == {"candidate_path": "Candidate.lean"}
        and isinstance(outer_call_id, str)
        and bool(outer_call_id)
        and isinstance(outer_raw_item_id, str)
        and bool(outer_raw_item_id)
        and len({outer_raw_item_id, outer_call_id, inner_call_id}) == 3
        and type(outer_observed_ns) is int
        and type(inner_started_ns) is int
        and 0 < outer_observed_ns <= inner_started_ns
        and boundary.get("root_only") is True
        and boundary.get("descendants_quiescent") is True
        and boundary.get("sole_model_tool_call_in_response") is True
        and boundary.get("outer_exec_final_raw_item") is True
        and boundary.get("inner_dynamic_call_observed") is True
        and boundary.get("inner_submit_invocation_exact") is True
        and boundary.get("outer_raw_item_observed_before_inner_dynamic_call") is True
        and valid_event_order
        and boundary.get("raw_response_completed_before_boundary_publication") is True
        and boundary.get("inner_dynamic_call_left_blocked") is True
        and boundary.get("inner_dynamic_tool_response_sent") is False
        and boundary.get("outer_exec_output_emitted") is False
        and boundary.get("later_model_response_possible") is False
        and isinstance(gate_close, Mapping)
        and set(gate_close)
        == {"won", "requested_reason", "effective_reason", "phase", "sequence"}
        and gate_close.get("won") is True
        and gate_close.get("requested_reason") == "accepted_submission"
        and gate_close.get("effective_reason") == "accepted_submission"
        and gate_close.get("phase") == "CLOSED"
        and type(gate_close.get("sequence")) is int
        and gate_close["sequence"] > 0
        and isinstance(retained, Mapping)
        and retained.get("verified") is True
        and _retained_request_matches_boundary(record, boundary)
    )


def _failed_attempt_has_exact_provider_gate_crossing(
    record: Mapping[str, Any],
) -> bool:
    """Recognize the one scoreable non-drained Ultra failure endpoint."""

    usage = record.get("token_usage")
    gate = usage.get("provider_token_gate") if isinstance(usage, Mapping) else None
    terminal = gate.get("terminal") if isinstance(gate, Mapping) else None
    first_crossing = usage.get("first_crossing") if isinstance(usage, Mapping) else None
    gate_crossing = terminal.get("crossing") if isinstance(terminal, Mapping) else None
    teardown = usage.get("adapter_teardown") if isinstance(usage, Mapping) else None
    return (
        record.get("pass") is False
        and record.get("scored") is True
        and type(record.get("agent_exit_code")) is int
        and record.get("agent_exit_code") == 0
        and record.get("failure_code") == "TOKEN_LIMIT"
        and isinstance(usage, Mapping)
        and usage.get("usage_scope")
        == "rooted_attempt_thread_tree_completed_responses"
        and usage.get("measurement_exact") is True
        and usage.get("submission_boundary_exact") is False
        and usage.get("submission_boundary") is None
        and usage.get("drain_complete") is False
        and usage.get("tree_quiescent") is False
        and usage.get("stop_reason") == "token_limit"
        and usage.get("invalid_reasons") == []
        and isinstance(first_crossing, Mapping)
        and isinstance(gate, Mapping)
        and gate.get("enabled") is True
        and gate.get("final_attached") is True
        and gate.get("exact_for_usage") is True
        and isinstance(terminal, Mapping)
        and terminal.get("phase") == "CLOSED"
        and terminal.get("close_reason") == "token_limit"
        and terminal.get("open_request_ids") == []
        and terminal.get("all_complete") is True
        and terminal.get("poisoned") is False
        and isinstance(gate_crossing, Mapping)
        and gate_crossing.get("response_id") == first_crossing.get("response_id")
        and gate_crossing.get("completed_tokens") == first_crossing.get("tokens")
        and gate_crossing.get("sole_inflight") is True
        and gate_crossing.get("release_kind")
        == (
            ultra_canary.runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE
            if gate_crossing.get("request_kind") == "compaction"
            else ultra_canary.runner.PROVIDER_GATE_ORDINARY_CROSSING_RELEASE
        )
        and isinstance(teardown, Mapping)
        and teardown.get("process_group_isolated") is True
        and teardown.get("immediate") is True
        and teardown.get("stdin_closed") is True
        and teardown.get("completed") is True
    )


def _failed_attempt_has_exact_natural_drain(record: Mapping[str, Any]) -> bool:
    usage = record.get("token_usage")
    return (
        record.get("pass") is False
        and record.get("scored") is True
        and type(record.get("agent_exit_code")) is int
        and record.get("agent_exit_code") == 0
        # The frozen app-server has no exact partial-response usage at an
        # interrupting wall endpoint.  A TIME_LIMIT record cannot become final
        # merely by hand-asserting a natural drain and clean exit.
        and record.get("failure_code") not in ("TIME_LIMIT", "TOKEN_LIMIT")
        and isinstance(usage, Mapping)
        and usage.get("usage_scope")
        == "rooted_attempt_thread_tree_completed_responses"
        and usage.get("measurement_exact") is True
        and usage.get("submission_boundary_exact") is False
        and usage.get("submission_boundary") is None
        and usage.get("drain_complete") is True
        and usage.get("tree_quiescent") is True
        and usage.get("active_thread_ids") == []
        and usage.get("unresolved_thread_ids") == []
        and usage.get("invalid_reasons") == []
    )


def _useful_work_attempt_requires_abort(record: Mapping[str, Any]) -> bool:
    """Fail closed unless useful Ultra work ended at one exact allowed boundary."""

    return record.get("useful_work_started") is True and not (
        _accepted_pass_has_exact_boundary(record)
        or _failed_attempt_has_exact_provider_gate_crossing(record)
        or _failed_attempt_has_exact_natural_drain(record)
    )


def matrix_incident_digest(record: Mapping[str, Any]) -> str:
    """Hash canonical JSON after removing only the incident self-hash field."""

    payload = dict(record)
    payload.pop(MATRIX_INCIDENT_SHA256_FIELD, None)
    return canonical_document_digest(payload)


def _bind_matrix_incident_sha256(record: dict[str, Any]) -> None:
    digest = matrix_incident_digest(record)
    if MATRIX_INCIDENT_SHA256_FIELD in record:
        existing = _sha256_value(
            record[MATRIX_INCIDENT_SHA256_FIELD], "matrix incident self-hash"
        )
        if existing != digest:
            raise BenchmarkToolError(
                "runner record already contains a conflicting matrix incident self-hash"
            )
        return
    record[MATRIX_INCIDENT_SHA256_FIELD] = digest


def _matrix_incident_control(status: str, retry_allowed: bool) -> dict[str, Any]:
    expected_retry = {
        "retryable_pre_prompt_system_error": True,
        "terminal_pre_prompt_system_error": False,
        "aborted_after_unscorable_useful_work": False,
    }
    if status not in expected_retry or retry_allowed is not expected_retry[status]:
        raise BenchmarkToolError("matrix incident status/retry policy is invalid")
    return {
        "status": status,
        "retry_allowed": retry_allowed,
        "scored": False,
        "final_assignment_record_written": False,
    }


def _freeze_incident_source_attempt_logs(
    record: Mapping[str, Any],
    *,
    results_root: Path,
    attempt_output: Path,
    planned_run_id: str,
    attempt: int,
) -> dict[str, Any]:
    """Rewrite an incident source to attempt-specific immutable log artifacts."""

    on_disk = read_json(attempt_output)
    if not isinstance(on_disk, dict) or on_disk != dict(record):
        raise BenchmarkToolError(
            "matrix incident source attempt disagrees with its normalized runner record"
        )
    frozen = _json_copy(record)
    for field in ("agent_log", "validation_log"):
        raw = frozen.get(field)
        digest_field = f"{field}_sha256"
        if raw is None:
            if frozen.get(digest_field) is not None:
                raise BenchmarkToolError(
                    f"matrix incident source has {digest_field} without {field}"
                )
            continue
        source = _result_artifact_path(
            results_root, raw, f"matrix incident live source {field}"
        )
        # Deliberately avoid .json/.jsonl suffixes: attempt ledger globs must
        # continue to name only the normalized attempt record and transcript.
        destination = (
            attempt_output.parent
            / f"{planned_run_id}.attempt-{attempt}.{field}.artifact"
        )
        if destination.is_symlink():
            raise BenchmarkToolError(
                f"matrix incident immutable {field} destination is a symlink"
            )
        shutil.copy2(source, destination)
        descriptor = _result_artifact_descriptor(
            results_root, destination, f"matrix incident immutable {field}"
        )
        if descriptor["sha256"] != sha256_file(source):
            raise BenchmarkToolError(
                f"matrix incident immutable {field} copy is corrupt"
            )
        existing_digest = frozen.get(digest_field)
        if existing_digest is not None and existing_digest != descriptor["sha256"]:
            raise BenchmarkToolError(
                f"matrix incident source {digest_field} disagrees with {field}"
            )
        frozen[field] = descriptor["path"]
        frozen[digest_field] = descriptor["sha256"]
    write_json(attempt_output, frozen)
    return frozen


def _authenticate_embedded_freeze_check(
    value: Mapping[str, Any],
    reference_freeze: Mapping[str, Any],
    *,
    label: str,
) -> dict[str, Any]:
    wrapper = _mapping(
        value.get("frozen_run_verification"), f"{label} frozen-run verification"
    )
    if set(wrapper) != {"freeze_check_sha256", "freeze_check"}:
        raise BenchmarkToolError(
            f"{label} has stale release/environment/freeze provenance (malformed wrapper)"
        )
    owning_freeze = _mapping(wrapper.get("freeze_check"), f"{label} embedded freeze")
    digest = _sha256_value(
        wrapper.get("freeze_check_sha256"), f"{label} embedded freeze SHA-256"
    )
    if digest != canonical_document_digest(owning_freeze):
        raise BenchmarkToolError(
            f"{label} has stale release/environment/freeze provenance"
        )
    verify_pair_policy_compatible_freeze_checks(reference_freeze, owning_freeze)
    return dict(owning_freeze)


def _authenticate_matrix_record_provenance(
    results_root: Path,
    value: Mapping[str, Any],
    assignment: Mapping[str, Any],
    freeze_check: Mapping[str, Any],
    *,
    attempt: int,
    label: str,
) -> None:
    if value.get("schema_version") != 1 or value.get("kind") != "highambench-run":
        raise BenchmarkToolError(f"{label} header is invalid")
    for field, expected in _planned_assignment_record_identity(assignment).items():
        if value.get(field) != expected:
            raise BenchmarkToolError(
                f"{label} has wrong planned {field}: {value.get(field)!r} != {expected!r}"
            )
    if value.get(MATRIX_ATTEMPT_FIELD) != attempt:
        raise BenchmarkToolError(f"{label} has the wrong matrix attempt")
    if (
        freeze_check.get("schema_version") != 1
        or freeze_check.get("kind") != "highambench-frozen-run-verification"
        or freeze_check.get("ok") is not True
    ):
        raise BenchmarkToolError("cannot authenticate an incident against an invalid freeze")
    freeze_agent = _mapping(freeze_check.get("agent"), "freeze-check agent")
    expected_agent = {
        field: freeze_agent.get(field)
        for field in ("id", "version", "model", "reasoning_effort")
    }
    if value.get("agent") != expected_agent:
        raise BenchmarkToolError(f"{label} has stale agent provenance")
    if value.get("environment_id") != freeze_check.get("environment_id"):
        raise BenchmarkToolError(f"{label} has a stale environment identity")
    owning_freeze = _authenticate_embedded_freeze_check(value, freeze_check, label=label)
    frozen_limits = _mapping(freeze_check.get("limits"), "freeze-check limits")
    record_limits = _mapping(value.get("limits"), f"{label} limits")
    if (
        record_limits.get("time_seconds") != frozen_limits.get("wall_clock_seconds")
        or record_limits.get("model_tokens") != frozen_limits.get("total_model_tokens")
        or record_limits.get("prompt_startup_seconds")
        != frozen_limits.get("prompt_startup_timeout_seconds")
    ):
        raise BenchmarkToolError(f"{label} has stale frozen limits")
    allocation = value.get("allocation_hardware")
    if not isinstance(allocation, Mapping):
        raise BenchmarkToolError(f"{label} has no allocation hardware descriptor")
    verify_allocation_hardware_descriptor(results_root, allocation, owning_freeze)


def _preserve_matrix_incident(
    record: Mapping[str, Any],
    incidents: Path,
    *,
    results_root: Path,
    assignment: Mapping[str, Any],
    attempt: int,
    attempt_output: Path,
    attempt_jsonl: Path,
    status: str,
    retry_allowed: bool,
    freeze_check: Mapping[str, Any],
) -> Path:
    """Persist and authenticate an incident without manufacturing a result."""

    reserved = {
        MATRIX_RECORD_SHA256_FIELD,
        MATRIX_INCIDENT_SHA256_FIELD,
        "planned_run_id",
        "matrix_incident",
        "incident_provenance",
    }
    if reserved.intersection(record):
        raise BenchmarkToolError("runner attempt contains reserved matrix incident fields")
    planned = _planned_assignment_record_identity(assignment)
    planned_run_id = planned["run_id"]
    source_record = _freeze_incident_source_attempt_logs(
        record,
        results_root=results_root,
        attempt_output=attempt_output,
        planned_run_id=planned_run_id,
        attempt=attempt,
    )
    incident = _json_copy(source_record)
    incident["planned_run_id"] = planned_run_id
    suffix = "unscorable" if status == "aborted_after_unscorable_useful_work" else "system"
    incident["run_id"] = f"{planned_run_id}-{suffix}-attempt-{attempt}"
    incident["scored"] = False
    incident["matrix_incident"] = _matrix_incident_control(status, retry_allowed)
    _copy_incident_logs(
        incident,
        incidents,
        f"attempt-{attempt}",
        results_root=results_root,
    )
    incident["incident_provenance"] = {
        "schema_version": 1,
        "planned_assignment": planned,
        "matrix_attempt": attempt,
        "source_attempt": _result_artifact_descriptor(
            results_root, attempt_output, "matrix incident source attempt"
        ),
        "transcript": _result_artifact_descriptor(
            results_root,
            attempt_jsonl,
            "matrix incident raw transcript",
            nonempty=True,
        ),
    }
    _bind_matrix_incident_sha256(incident)
    path = incidents / f"{planned_run_id}.attempt-{attempt}.json"
    write_json(path, incident)
    _authenticate_matrix_incident(
        results_root, path, assignment, freeze_check, expected_attempt=attempt
    )
    return path


def _incident_record_paths(incidents_dir: Path, planned_run_id: str) -> list[Path]:
    pattern = re.compile(rf"^{re.escape(planned_run_id)}\.attempt-([0-9]+)\.json$")
    found: list[tuple[int, Path]] = []
    if incidents_dir.is_dir():
        for path in incidents_dir.iterdir():
            match = pattern.fullmatch(path.name)
            if match and path.is_file():
                found.append((int(match.group(1)), path))
    return [path for _, path in sorted(found)]


def _authenticate_matrix_incident(
    results_root: Path,
    incident_path: Path,
    assignment: Mapping[str, Any],
    freeze_check: Mapping[str, Any],
    *,
    expected_attempt: int | None = None,
) -> dict[str, Any]:
    """Authenticate one incident and its exact source attempt/transcript chain."""

    if incident_path.is_symlink() or not incident_path.is_file():
        raise BenchmarkToolError(
            f"matrix incident is missing or not a regular non-symlink file: {incident_path}"
        )
    value = read_json(incident_path)
    if not isinstance(value, dict):
        raise BenchmarkToolError(f"matrix incident is not a JSON object: {incident_path}")
    stored_digest = _sha256_value(
        value.get(MATRIX_INCIDENT_SHA256_FIELD), "matrix incident self-hash"
    )
    if stored_digest != matrix_incident_digest(value):
        raise BenchmarkToolError(f"matrix incident self-hash is invalid: {incident_path}")

    control = _mapping(value.get("matrix_incident"), "matrix incident control")
    if set(control) != {
        "status",
        "retry_allowed",
        "scored",
        "final_assignment_record_written",
    }:
        raise BenchmarkToolError("matrix incident control schema is invalid")
    status = control.get("status")
    retry_allowed = control.get("retry_allowed")
    expected_control = _matrix_incident_control(str(status), retry_allowed)
    if dict(control) != expected_control:
        raise BenchmarkToolError("matrix incident control is inconsistent")
    attempt = value.get(MATRIX_ATTEMPT_FIELD)
    if isinstance(attempt, bool) or attempt not in (1, 2):
        raise BenchmarkToolError("matrix incident has an invalid matrix attempt")
    if expected_attempt is not None and attempt != expected_attempt:
        raise BenchmarkToolError("matrix incident attempt does not match its path")
    if status == "retryable_pre_prompt_system_error" and attempt != 1:
        raise BenchmarkToolError("retryable matrix incident must be attempt 1")
    if status == "terminal_pre_prompt_system_error" and attempt != 2:
        raise BenchmarkToolError("terminal matrix incident must be attempt 2")

    planned = _planned_assignment_record_identity(assignment)
    planned_run_id = planned["run_id"]
    suffix = "unscorable" if status == "aborted_after_unscorable_useful_work" else "system"
    if value.get("planned_run_id") != planned_run_id or value.get("run_id") != (
        f"{planned_run_id}-{suffix}-attempt-{attempt}"
    ):
        raise BenchmarkToolError("matrix incident run identity is invalid")

    provenance = _mapping(value.get("incident_provenance"), "incident provenance")
    if set(provenance) != {
        "schema_version",
        "planned_assignment",
        "matrix_attempt",
        "source_attempt",
        "transcript",
    } or provenance.get("schema_version") != 1:
        raise BenchmarkToolError("matrix incident provenance schema is invalid")
    if (
        provenance.get("planned_assignment") != planned
        or provenance.get("matrix_attempt") != attempt
    ):
        raise BenchmarkToolError("matrix incident planned identity provenance is invalid")

    expected_source_relative = f"attempts/{planned_run_id}.attempt-{attempt}.json"
    expected_transcript_relative = f"attempts/{planned_run_id}.attempt-{attempt}.jsonl"
    source_descriptor = _mapping(
        provenance.get("source_attempt"), "incident source-attempt descriptor"
    )
    transcript_descriptor = _mapping(
        provenance.get("transcript"), "incident transcript descriptor"
    )
    if set(source_descriptor) != {"path", "sha256"} or set(
        transcript_descriptor
    ) != {"path", "sha256"}:
        raise BenchmarkToolError("matrix incident source descriptor schema is invalid")
    if (
        source_descriptor.get("path") != expected_source_relative
        or transcript_descriptor.get("path") != expected_transcript_relative
    ):
        raise BenchmarkToolError("matrix incident source paths are not exact")
    source_path = _result_artifact_path(
        results_root, expected_source_relative, "matrix incident source attempt"
    )
    transcript_path = _result_artifact_path(
        results_root, expected_transcript_relative, "matrix incident transcript"
    )
    if transcript_path.stat().st_size <= 0:
        raise BenchmarkToolError("matrix incident transcript is empty")
    if (
        _sha256_value(source_descriptor.get("sha256"), "incident source SHA-256")
        != sha256_file(source_path)
        or _sha256_value(
            transcript_descriptor.get("sha256"), "incident transcript SHA-256"
        )
        != sha256_file(transcript_path)
    ):
        raise BenchmarkToolError("matrix incident source or transcript digest is invalid")
    source = read_json(source_path)
    if not isinstance(source, dict):
        raise BenchmarkToolError("matrix incident source attempt is not a JSON object")
    reserved = {
        MATRIX_RECORD_SHA256_FIELD,
        MATRIX_INCIDENT_SHA256_FIELD,
        "planned_run_id",
        "matrix_incident",
        "incident_provenance",
    }
    if reserved.intersection(source):
        raise BenchmarkToolError("matrix incident source contains reserved matrix fields")
    _authenticate_matrix_record_provenance(
        results_root,
        source,
        assignment,
        freeze_check,
        attempt=attempt,
        label="matrix incident source attempt",
    )

    if status in {
        "retryable_pre_prompt_system_error",
        "terminal_pre_prompt_system_error",
    }:
        if not (
            source.get("pass") is False
            and source.get("scored") is False
            and source.get("failure_code") == "SYSTEM_ERROR"
            and source.get("useful_work_started") is False
        ):
            raise BenchmarkToolError("matrix incident is not a pre-prompt SYSTEM_ERROR")
    elif not _useful_work_attempt_requires_abort(source):
        raise BenchmarkToolError("matrix incident is not unscorable useful work")

    expected = _json_copy(source)
    expected["planned_run_id"] = planned_run_id
    expected["run_id"] = f"{planned_run_id}-{suffix}-attempt-{attempt}"
    expected["scored"] = False
    expected["matrix_incident"] = expected_control
    expected["incident_provenance"] = _json_copy(provenance)
    for field in ("agent_log", "validation_log"):
        raw = source.get(field)
        digest_field = f"{field}_sha256"
        if raw is None:
            if source.get(digest_field) is not None:
                raise BenchmarkToolError(
                    f"matrix incident source has {digest_field} without {field}"
                )
            continue
        source_log = _result_artifact_path(
            results_root, raw, f"matrix incident source {field}"
        )
        source_log_digest = sha256_file(source_log)
        if (
            _sha256_value(
                source.get(digest_field), f"matrix incident source {digest_field}"
            )
            != source_log_digest
        ):
            raise BenchmarkToolError(
                f"matrix incident source {field} digest is invalid"
            )
        expected_destination = (
            incident_path.parent
            / f"{expected['run_id']}.attempt-{attempt}.{source_log.name}"
        )
        copied = _result_artifact_descriptor(
            results_root, expected_destination, f"matrix incident copied {field}"
        )
        if copied["sha256"] != source_log_digest:
            raise BenchmarkToolError(f"matrix incident copied {field} digest is invalid")
        expected[field] = copied["path"]
    _bind_matrix_incident_sha256(expected)
    if value != expected:
        raise BenchmarkToolError("matrix incident is not exactly derived from its source attempt")
    return value


def _rebuild_jsonl(
    records_dir: Path,
    incidents_dir: Path,
    assignments: list[dict[str, Any]],
    output: Path,
    *,
    results_root: Path,
    freeze_check: Mapping[str, Any],
) -> None:
    lines: list[str] = []
    run_ids: set[str] = set()
    for assignment in assignments:
        for incident_path in _incident_record_paths(incidents_dir, assignment["run_id"]):
            incident = _authenticate_matrix_incident(
                results_root, incident_path, assignment, freeze_check
            )
            run_id = incident["run_id"]
            if run_id in run_ids:
                raise BenchmarkToolError(f"saved result repeats run_id {run_id}")
            run_ids.add(run_id)
            lines.append(json.dumps(incident, sort_keys=True, separators=(",", ":")))
        record_path = records_dir / f"{assignment['run_id']}.json"
        if record_path.exists() or record_path.is_symlink():
            value = _authenticate_final_assignment_record(
                results_root, record_path, assignment, freeze_check
            )
            run_id = value["run_id"]
            if run_id in run_ids:
                raise BenchmarkToolError(f"saved result repeats run_id {run_id}")
            run_ids.add(run_id)
            lines.append(json.dumps(value, sort_keys=True, separators=(",", ":")))
    output.parent.mkdir(parents=True, exist_ok=True)
    temporary = output.with_suffix(output.suffix + ".tmp")
    temporary.write_text("\n".join(lines) + ("\n" if lines else ""), encoding="utf-8")
    temporary.replace(output)


def configured_repetition_ids(config: Mapping[str, Any]) -> list[str]:
    repetitions = config.get("repetitions")
    if not isinstance(repetitions, list) or not repetitions:
        raise BenchmarkToolError("config must contain a nonempty repetitions list")
    result: list[str] = []
    for index, raw in enumerate(repetitions):
        repetition = _mapping(raw, f"config.repetitions[{index}]")
        repetition_id = _nonempty_string(
            repetition.get("id"), f"config.repetitions[{index}].id"
        )
        if repetition_id in result:
            raise BenchmarkToolError(f"config repeats repetition {repetition_id}")
        result.append(repetition_id)
    return result


def _validate_planned_counts(
    config: Mapping[str, Any],
    task_catalog: Mapping[str, Mapping[str, str]],
    repetition_ids: list[str],
) -> None:
    planned = config.get("planned_counts_per_agent")
    if planned is None:
        return
    planned = _mapping(planned, "config.planned_counts_per_agent")
    paper_count = len({task["paper_id"] for task in task_catalog.values()})
    expected = {
        "papers": paper_count,
        "tasks": len(task_catalog),
        "repetitions_per_task": len(repetition_ids),
        "conditions": 2,
        "paired_assignments": len(task_catalog) * len(repetition_ids),
        "runs": len(task_catalog) * len(repetition_ids) * 2,
    }
    for field, value in expected.items():
        if planned.get(field) != value:
            raise BenchmarkToolError(
                f"planned count {field}={planned.get(field)!r}, expected {value}"
            )


def assignments_from_order(
    order: Mapping[str, Any],
    task_catalog: Mapping[str, Mapping[str, str]] | None = None,
    repetition_ids: Iterable[str] | None = None,
) -> list[dict[str, Any]]:
    """Expand paired run order and, when supplied, prove exact task coverage."""

    assignments: list[dict[str, Any]] = []
    raw_pairs = order.get("pairs")
    if not isinstance(raw_pairs, list):
        raise BenchmarkToolError("run order must contain a pairs list")
    seen_pairs: set[str] = set()
    seen_runs: set[str] = set()
    seen_task_repetitions: set[tuple[str, str]] = set()
    configured_repetitions = (
        list(repetition_ids) if repetition_ids is not None else None
    )
    if configured_repetitions is not None and len(set(configured_repetitions)) != len(
        configured_repetitions
    ):
        raise BenchmarkToolError("configured repetition IDs are not unique")

    for raw_pair in raw_pairs:
        if not isinstance(raw_pair, Mapping):
            raise BenchmarkToolError("run-order pairs must be objects")
        pair = raw_pair
        pair_id = _nonempty_string(pair.get("pair_id"), "run-order pair_id")
        task_id = _nonempty_string(
            pair.get("task_id"), f"run-order pair {pair_id} task_id"
        )
        repetition_id = _nonempty_string(
            pair.get("repetition_id"), f"run-order pair {pair_id} repetition_id"
        )
        if pair_id != f"{task_id}-{repetition_id}":
            raise BenchmarkToolError(
                f"run-order pair_id {pair_id!r} does not match task and repetition"
            )
        if pair_id in seen_pairs:
            raise BenchmarkToolError(f"run order repeats pair_id {pair_id}")
        seen_pairs.add(pair_id)
        task_repetition = (task_id, repetition_id)
        if task_repetition in seen_task_repetitions:
            raise BenchmarkToolError(
                f"run order repeats task/repetition pair {task_id}/{repetition_id}"
            )
        seen_task_repetitions.add(task_repetition)

        if task_catalog is not None:
            task = task_catalog.get(task_id)
            if task is None:
                raise BenchmarkToolError(f"unknown task in run order: {task_id}")
            task_identity = dict(task)
        else:
            match = re.fullmatch(r"(P[0-9]+)-(T[1234])", task_id)
            if match is None:
                raise BenchmarkToolError(f"malformed task in run order: {task_id}")
            task_identity = {
                "task_id": task_id,
                "paper_id": match.group(1),
                "tier": match.group(2),
            }
        if configured_repetitions is not None and repetition_id not in configured_repetitions:
            raise BenchmarkToolError(
                f"run-order pair {pair_id} names unknown repetition {repetition_id}"
            )

        condition_order = pair.get("condition_order")
        run_ids = pair.get("run_ids")
        if condition_order not in (["N", "L"], ["L", "N"]):
            raise BenchmarkToolError(f"bad condition order for {pair_id}")
        if not isinstance(run_ids, list) or len(run_ids) != 2:
            raise BenchmarkToolError(f"bad run IDs for {pair_id}")
        for index, condition in enumerate(condition_order):
            expected = f"{pair_id}-{condition}"
            if run_ids[index] != expected:
                raise BenchmarkToolError(
                    f"run ID/order mismatch for {pair_id}: {run_ids[index]} != {expected}"
                )
            if expected in seen_runs:
                raise BenchmarkToolError(f"run order repeats run_id {expected}")
            seen_runs.add(expected)
            assignments.append(
                {
                    **task_identity,
                    "pair_id": pair_id,
                    "repetition_id": repetition_id,
                    "condition": condition,
                    "condition_order": list(condition_order),
                    "order_index": index + 1,
                    "run_id": run_ids[index],
                }
            )

    if task_catalog is not None and configured_repetitions is not None:
        expected_pairs = {
            (task_id, repetition_id)
            for task_id in task_catalog
            for repetition_id in configured_repetitions
        }
        if seen_task_repetitions != expected_pairs:
            missing = sorted(expected_pairs - seen_task_repetitions)
            unexpected = sorted(seen_task_repetitions - expected_pairs)
            raise BenchmarkToolError(
                "run order is not the exact task/repetition matrix "
                f"(missing={missing[:8]}, unexpected={unexpected[:8]})"
            )
    return assignments


def _paper_boundary_index(
    assignments: list[dict[str, Any]], stop_after_paper: str | None
) -> int | None:
    """Return the exclusive assignment index for a requested paper boundary."""

    if stop_after_paper is None:
        return None
    if not isinstance(stop_after_paper, str) or not stop_after_paper:
        raise BenchmarkToolError("--stop-after-paper must be a nonempty paper ID")
    paper_blocks: list[str] = []
    for assignment in assignments:
        paper_id = _nonempty_string(assignment.get("paper_id"), "assignment paper_id")
        if not paper_blocks or paper_blocks[-1] != paper_id:
            if paper_id in paper_blocks:
                raise BenchmarkToolError(
                    f"run order revisits paper {paper_id}; no clean paper boundary exists"
                )
            paper_blocks.append(paper_id)
    if stop_after_paper not in paper_blocks:
        raise BenchmarkToolError(
            f"--stop-after-paper names unknown paper {stop_after_paper!r}"
        )
    return 1 + max(
        index
        for index, assignment in enumerate(assignments)
        if assignment["paper_id"] == stop_after_paper
    )


def _assignments_for_only_pair(
    assignments: list[dict[str, Any]], only_pair_id: str | None
) -> list[dict[str, Any]]:
    if only_pair_id is None:
        return assignments
    pair_id = _nonempty_string(only_pair_id, "--only-pair-id")
    selected = [item for item in assignments if item.get("pair_id") == pair_id]
    if len(selected) != 2:
        known = sorted({str(item.get("pair_id")) for item in assignments})
        raise BenchmarkToolError(
            f"--only-pair-id names no exact canonical N/L pair: {pair_id!r}; "
            f"known={known}"
        )
    if {item.get("condition") for item in selected} != {"N", "L"}:
        raise BenchmarkToolError(
            f"canonical pair {pair_id!r} does not contain exactly N and L"
        )
    if any(item.get("pair_id") != pair_id for item in selected):
        raise BenchmarkToolError("pair selector produced a foreign assignment")
    return selected


def _reject_foreign_pair_records(
    results_root: Path, assignments: Sequence[Mapping[str, Any]]
) -> None:
    expected = {f"{item['run_id']}.json" for item in assignments}
    for directory_name in ("records", "incidents"):
        directory = results_root / directory_name
        if not directory.exists():
            continue
        if directory.is_symlink() or not directory.is_dir():
            raise BenchmarkToolError(
                f"pair-root {directory_name} is not a regular non-symlink directory"
            )
        for path in directory.glob("*.json"):
            if directory_name == "records":
                allowed = path.name in expected
            else:
                allowed = any(path.name.startswith(f"{item['run_id']}.attempt-") for item in assignments)
            if not allowed:
                raise BenchmarkToolError(
                    f"--only-pair-id root contains a foreign {directory_name} record: {path.name}"
                )


def _write_pair_complete_status(
    results_root: Path,
    pair_id: str,
    commit: Mapping[str, Any],
) -> None:
    write_json(
        results_root / "last_chunk_status.json",
        {
            "schema_version": 1,
            "kind": "highambench-matrix-chunk-status",
            "status": "stopped_after_requested_pair",
            "pair_id": pair_id,
            "completed_runs": 2,
            "planned_runs": 2,
            "pair_commit": pair_commit_descriptor(results_root, commit),
        },
    )


def _planned_assignment_record_identity(
    assignment: Mapping[str, Any],
) -> dict[str, Any]:
    """Return the exact planned identity/order projection stored in a run record."""

    condition_order = assignment.get("condition_order")
    if condition_order not in (["N", "L"], ["L", "N"]):
        raise BenchmarkToolError("assignment has an invalid condition order")
    return {
        "run_id": _nonempty_string(assignment.get("run_id"), "assignment run_id"),
        "pair_id": _nonempty_string(assignment.get("pair_id"), "assignment pair_id"),
        "task_id": _nonempty_string(assignment.get("task_id"), "assignment task_id"),
        "paper_id": _nonempty_string(
            assignment.get("paper_id"), "assignment paper_id"
        ),
        "paper_sha256": _sha256_value(
            assignment.get("paper_sha256"), "assignment paper SHA-256"
        ),
        "tier": _nonempty_string(assignment.get("tier"), "assignment tier"),
        "condition": _nonempty_string(
            assignment.get("condition"), "assignment condition"
        ),
        "repetition_id": _nonempty_string(
            assignment.get("repetition_id"), "assignment repetition_id"
        ),
        "backend_seed": assignment.get("backend_seed"),
        "pair_order": "N-first" if condition_order[0] == "N" else "L-first",
        "order_index": assignment.get("order_index"),
    }


_PROVIDER_GATE_RUN_RECORD_FIELDS = {
    "required",
    "status",
    "protocol",
    "cleanup_grace_seconds",
    "implementation_source_sha256",
    "model_catalog",
    "transport_provenance",
    "live",
    "final",
    "error",
}
_PROVIDER_GATE_FILE_FIELDS = {
    "path",
    "absolute",
    "exists",
    "regular_non_symlink",
    "mode",
    "size_bytes",
    "file_sha256",
}
def _provider_gate_sse_content_type_allowed(value: Any) -> bool:
    """Recognize only the frozen SSE media type and optional UTF-8 charset."""

    return isinstance(value, str) and re.fullmatch(
        r'[ \t]*text/event-stream(?:[ \t]*;[ \t]*charset[ \t]*=[ \t]*'
        r'(?:utf-8|"utf-8"))?[ \t]*',
        value,
        re.IGNORECASE,
    ) is not None


def _validate_provider_gate_call_sse_authentication(
    call: Mapping[str, Any], *, label: str
) -> dict[str, Any]:
    """Independently validate one gate-v4 header/parser authentication receipt."""

    runner = ultra_canary.runner
    contract = runner.PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT
    if set(contract) != set(runner.PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_KEYS):
        raise BenchmarkToolError(f"{label} provider-gate SSE contract schema changed")

    content_type_occurrences = call.get("upstream_content_type_occurrences")
    content_encoding_occurrences = call.get("upstream_content_encoding_occurrences")
    if type(content_type_occurrences) is not int or content_type_occurrences not in {0, 1}:
        raise BenchmarkToolError(
            f"{label} provider-gate Content-Type occurrence count is invalid"
        )
    if (
        type(content_encoding_occurrences) is not int
        or content_encoding_occurrences not in {0, 1}
    ):
        raise BenchmarkToolError(
            f"{label} provider-gate Content-Encoding occurrence count is invalid"
        )

    raw_content_type = call.get("upstream_content_type")
    if content_type_occurrences == 0:
        if raw_content_type is not None:
            raise BenchmarkToolError(
                f"{label} provider-gate invented an absent Content-Type"
            )
        content_type_basis = "authenticated_stream_request_header_absent"
        synthesized = True
    else:
        if not _provider_gate_sse_content_type_allowed(raw_content_type):
            raise BenchmarkToolError(
                f"{label} provider-gate Content-Type is outside the frozen policy"
            )
        content_type_basis = "declared_text_event_stream"
        synthesized = False

    raw_content_encoding = call.get("upstream_content_encoding")
    if content_encoding_occurrences == 0:
        if raw_content_encoding is not None:
            raise BenchmarkToolError(
                f"{label} provider-gate invented an absent Content-Encoding"
            )
        content_encoding_basis = "implicit_identity_header_absent"
    else:
        if (
            not isinstance(raw_content_encoding, str)
            or re.fullmatch(
                r"[ \t]*identity[ \t]*",
                raw_content_encoding,
                re.IGNORECASE,
            )
            is None
        ):
            raise BenchmarkToolError(
                f"{label} provider-gate Content-Encoding is outside the frozen policy"
            )
        content_encoding_basis = "declared_identity"

    authentication = call.get("upstream_sse_authentication")
    if (
        not isinstance(authentication, Mapping)
        or set(authentication) != set(runner.PROVIDER_GATE_SSE_AUTHENTICATION_KEYS)
    ):
        raise BenchmarkToolError(
            f"{label} provider-gate SSE authentication fields are not exact"
        )
    json_event_count = authentication.get("json_event_count")
    completed_event_index = authentication.get("completed_event_index")
    done_count = authentication.get("done_count")
    body_bytes = authentication.get("body_bytes")
    response_id = call.get("response_id")
    if (
        type(call.get("upstream_status")) is not int
        or call.get("upstream_status") != contract.get("success_status")
        or type(authentication.get("schema_version")) is not int
        or authentication.get("schema_version") != contract.get("schema_version")
        or authentication.get("protocol") != contract.get("protocol")
        or authentication.get("parser") != contract.get("parser")
        or authentication.get("complete") is not True
        or authentication.get("content_type_basis") != content_type_basis
        or authentication.get("content_type_basis")
        not in runner.PROVIDER_GATE_SSE_CONTENT_TYPE_BASES
        or authentication.get("content_encoding_basis") != content_encoding_basis
        or authentication.get("content_encoding_basis")
        not in runner.PROVIDER_GATE_SSE_CONTENT_ENCODING_BASES
        or type(json_event_count) is not int
        or json_event_count <= 0
        or type(completed_event_index) is not int
        or completed_event_index != json_event_count - 1
        or type(done_count) is not int
        or done_count not in {0, 1}
        or type(body_bytes) is not int
        or body_bytes <= 0
        or authentication.get("body_sha256") != call.get("upstream_body_sha256")
        or type(call.get("upstream_body_bytes")) is not int
        or body_bytes != call.get("upstream_body_bytes")
        or not isinstance(authentication.get("body_sha256"), str)
        or re.fullmatch(r"[0-9a-f]{64}", authentication["body_sha256"]) is None
        or not isinstance(response_id, str)
        or not response_id
        or authentication.get("response_id") != response_id
        or authentication.get("downstream_content_type_synthesized")
        is not synthesized
    ):
        raise BenchmarkToolError(
            f"{label} provider-gate strict SSE authentication is inconsistent"
        )
    return dict(authentication)


def _argv_unique_value(command: Sequence[str], option: str) -> tuple[int, str | None]:
    positions = [index for index, item in enumerate(command) if item == option]
    if len(positions) != 1 or positions[0] + 1 >= len(command):
        return len(positions), None
    return 1, command[positions[0] + 1]


def authenticate_runner_provider_gate_summary(
    record: Mapping[str, Any],
) -> dict[str, Any]:
    """Reauthenticate the runner's sealed Ultra provider-gate endpoint.

    The embedded summary is convenient indexing data, not an authority.  This
    consumer derives the artifact path from the trusted usage-output argv,
    invokes the runner's independent replay verifier on the mode-0444 file,
    and then requires byte-for-byte agreement with the retained summary.
    """

    label = str(record.get("run_id") or "<unknown>")
    summary = _mapping(
        record.get("provider_token_gate"),
        f"run {label} provider-token-gate summary",
    )
    if set(summary) != _PROVIDER_GATE_RUN_RECORD_FIELDS:
        raise BenchmarkToolError(
            f"run {label} provider-token-gate summary fields are not exact"
        )
    if (
        summary.get("required") is not True
        or summary.get("status") != "final_artifact_authenticated"
        or summary.get("protocol")
        != ultra_canary.runner.PROVIDER_GATE_PROTOCOL
        or type(summary.get("cleanup_grace_seconds")) is not float
        or summary.get("cleanup_grace_seconds")
        != ultra_canary.runner.PROVIDER_GATE_CLEANUP_GRACE_SECONDS
        or summary.get("error") is not None
    ):
        raise BenchmarkToolError(
            f"run {label} lacks an authenticated final provider-token-gate endpoint"
        )
    source_sha256 = _sha256_value(
        summary.get("implementation_source_sha256"),
        f"run {label} provider-gate implementation source",
    )
    catalog = _mapping(
        summary.get("model_catalog"), f"run {label} provider-gate model catalog"
    )
    if set(catalog) != {"catalog_sha256", "entry_sha256", "response_bound"}:
        raise BenchmarkToolError(f"run {label} provider-gate model catalog is not exact")
    catalog_sha256 = _sha256_value(
        catalog.get("catalog_sha256"), f"run {label} model catalog SHA-256"
    )
    entry_sha256 = _sha256_value(
        catalog.get("entry_sha256"), f"run {label} model entry SHA-256"
    )
    if (
        type(catalog.get("response_bound")) is not int
        or catalog.get("response_bound")
        != ultra_canary.runner.PROVIDER_RESPONSE_TOKEN_BOUND
    ):
        raise BenchmarkToolError(f"run {label} provider response bound changed")
    transport_provenance = ultra_canary.runner._validate_provider_transport_provenance(
        summary.get("transport_provenance"),
        field=f"run {label}.provider_token_gate.transport_provenance",
    )
    if transport_provenance.get("connection_factory_mode") != "explicit_tls":
        raise BenchmarkToolError(
            f"run {label} provider transport did not use explicit TLS"
        )

    command = record.get("agent_command")
    if not isinstance(command, list) or not all(isinstance(item, str) for item in command):
        raise BenchmarkToolError(f"run {label} lacks its exact provider argv")
    usage_count, usage_raw = _argv_unique_value(command, "--usage-output")
    if usage_count != 1 or not isinstance(usage_raw, str) or not Path(usage_raw).is_absolute():
        raise BenchmarkToolError(f"run {label} has invalid --usage-output")
    usage_path = Path(usage_raw).resolve()
    paths = ultra_canary.runner.provider_gate_paths(usage_path)
    expected_options = {
        "--provider-gate-live-output": str(paths["live"]),
        "--provider-gate-output": str(paths["final"]),
        "--model-catalog-sha256": catalog_sha256,
        "--model-entry-sha256": entry_sha256,
        "--provider-response-bound": str(catalog["response_bound"]),
    }
    for option, wanted in expected_options.items():
        count, value = _argv_unique_value(command, option)
        if count != 1 or value != wanted:
            raise BenchmarkToolError(
                f"run {label} agent command has invalid {option}"
            )

    live = _mapping(summary.get("live"), f"run {label} live gate summary")
    final = _mapping(summary.get("final"), f"run {label} final gate summary")
    if set(live) != {"scoreable", "file", "authenticated_crossing"} or set(final) != {
        "scoreable",
        "file",
        "authentication",
    }:
        raise BenchmarkToolError(f"run {label} provider-gate endpoint schema changed")
    if live.get("scoreable") is not False or final.get("scoreable") is not True:
        raise BenchmarkToolError(f"run {label} conflates live and sealed gate evidence")
    for endpoint, path in ((live, paths["live"]), (final, paths["final"])):
        descriptor = _mapping(endpoint.get("file"), f"run {label} gate file")
        if set(descriptor) != _PROVIDER_GATE_FILE_FIELDS:
            raise BenchmarkToolError(f"run {label} gate file descriptor is not exact")
        if dict(descriptor) != ultra_canary.runner._provider_gate_file_status(path):
            raise BenchmarkToolError(f"run {label} gate file descriptor is stale")
    final_descriptor = _mapping(final.get("file"), f"run {label} final gate file")
    if (
        final_descriptor.get("path") != str(paths["final"])
        or final_descriptor.get("absolute") is not True
        or final_descriptor.get("exists") is not True
        or final_descriptor.get("regular_non_symlink") is not True
        or final_descriptor.get("mode") != "0444"
    ):
        raise BenchmarkToolError(f"run {label} final gate is not a sealed mode-0444 file")

    prompt_release = _mapping(
        record.get("prompt_release"), f"run {label} prompt-release summary"
    )
    released_descriptor = _mapping(
        prompt_release.get("released"), f"run {label} RELEASED descriptor"
    )
    released_record = _mapping(
        released_descriptor.get("record"), f"run {label} RELEASED record"
    )
    usage = _mapping(record.get("token_usage"), f"run {label} token usage")
    agent = _mapping(record.get("agent"), f"run {label} agent")
    limits = _mapping(record.get("limits"), f"run {label} limits")
    authenticated = ultra_canary.runner.authenticate_provider_gate_artifact(
        paths["final"],
        token_limit=_positive_int(
            limits.get("model_tokens"), f"run {label} token limit"
        ),
        run_id=_nonempty_string(record.get("run_id"), f"run {label} run_id"),
        model=_nonempty_string(agent.get("model"), f"run {label} model"),
        reasoning_effort=_nonempty_string(
            agent.get("reasoning_effort"), f"run {label} reasoning effort"
        ),
        root_thread_id=_nonempty_string(
            usage.get("root_thread_id"), f"run {label} root thread"
        ),
        prompt_release_sha256=(
            ultra_canary.runner._provider_gate_prompt_release_sha256(
                released_record
            )
        ),
        prompt_release_protocol=_nonempty_string(
            released_record.get("protocol_version"),
            f"run {label} prompt-release protocol",
        ),
        prompt_sha256=_sha256_value(
            prompt_release.get("effective_prompt_sha256"),
            f"run {label} effective prompt SHA-256",
        ),
        model_catalog_sha256=catalog_sha256,
        model_entry_sha256=entry_sha256,
        expected_transport_provenance=transport_provenance,
        usage=usage,
        expected_source_sha256=source_sha256,
    )
    if final.get("authentication") != authenticated:
        raise BenchmarkToolError(
            f"run {label} retained provider-gate authentication is stale"
        )
    derived = _mapping(authenticated.get("derived"), f"run {label} gate derivation")
    state = _mapping(
        _mapping(authenticated.get("record"), f"run {label} gate record").get("state"),
        f"run {label} gate state",
    )
    gate_record = _mapping(authenticated.get("record"), f"run {label} gate record")
    gate_invariants = _mapping(
        gate_record.get("invariants"), f"run {label} gate invariants"
    )
    calls = gate_record.get("calls")
    if not isinstance(calls, list) or not calls:
        raise BenchmarkToolError(f"run {label} provider gate has no authenticated calls")
    for index, call in enumerate(calls):
        if not isinstance(call, Mapping):
            raise BenchmarkToolError(
                f"run {label} provider-gate call {index} is not an object"
            )
        _validate_provider_gate_call_sse_authentication(
            call,
            label=f"run {label} provider-gate call {index}",
        )
    if (
        authenticated.get("authenticated") is not True
        or derived.get("appserver_deliveries_reconciled") is not True
        or gate_invariants.get("all_appserver_deliveries_reconciled") is not True
        or derived.get("appserver_deliveries_reconciled")
        is not gate_invariants.get("all_appserver_deliveries_reconciled")
        or derived.get("poisoned") is not False
        or gate_record.get("setup_requests") != []
    ):
        raise BenchmarkToolError(f"run {label} gate is poisoned, unbound, or used setup routes")
    crossing = state.get("crossing")
    if record.get("failure_code") == "TOKEN_LIMIT":
        endpoint_ok = (
            record.get("pass") is False
            and state.get("close_reason") == "token_limit"
            and isinstance(crossing, Mapping)
        )
    elif record.get("pass") is True:
        endpoint_ok = (
            record.get("failure_code") is None
            and state.get("close_reason") == "accepted_submission"
            and crossing is None
        )
    else:
        endpoint_ok = (
            record.get("pass") is False
            and record.get("failure_code") not in ("TIME_LIMIT", "TOKEN_LIMIT")
            and state.get("close_reason") == "natural_end"
            and crossing is None
        )
    protocol = _mapping(record.get("protocol"), f"run {label} protocol")
    verified = _mapping(protocol.get("verified"), f"run {label} protocol verification")
    if not endpoint_ok or any(
        verified.get(field) is not True
        for field in (
            "authenticated_provider_token_gate",
            "provider_gate_appserver_deliveries_reconciled",
            "provider_gate_terminal_endpoint",
        )
    ):
        raise BenchmarkToolError(f"run {label} provider-gate endpoint disagrees with outcome")
    return authenticated


def _authenticate_final_assignment_record(
    results_root: Path,
    record_path: Path,
    assignment: Mapping[str, Any],
    freeze_check: Mapping[str, Any],
    *,
    expected_attempt: int | None = None,
) -> dict[str, Any]:
    """Authenticate one final record before it may be resumed or counted."""

    if record_path.is_symlink() or not record_path.is_file():
        raise BenchmarkToolError(
            f"matrix final record is missing or not a regular non-symlink file: {record_path}"
        )
    value = read_json(record_path)
    if not isinstance(value, dict):
        raise BenchmarkToolError(f"matrix final record is not a JSON object: {record_path}")
    return _authenticate_final_assignment_record_payload(
        results_root,
        value,
        assignment,
        freeze_check,
        expected_attempt=expected_attempt,
        record_label=str(record_path),
    )


def _authenticate_final_assignment_record_payload(
    results_root: Path,
    value: dict[str, Any],
    assignment: Mapping[str, Any],
    freeze_check: Mapping[str, Any],
    *,
    expected_attempt: int | None = None,
    record_label: str = "in-memory final record",
) -> dict[str, Any]:
    """Authenticate an already parsed, sealed final-assignment record."""

    stored_digest = _sha256_value(
        value.get(MATRIX_RECORD_SHA256_FIELD),
        f"matrix final record {record_label} self-hash",
    )
    if stored_digest != matrix_record_digest(value):
        raise BenchmarkToolError(f"matrix final record self-hash is invalid: {record_label}")

    if value.get("schema_version") != 1 or value.get("kind") != "highambench-run":
        raise BenchmarkToolError(f"matrix final record header is invalid: {record_label}")
    expected_identity = _planned_assignment_record_identity(assignment)
    for field, expected in expected_identity.items():
        if value.get(field) != expected:
            raise BenchmarkToolError(
                f"matrix final record {record_label} has wrong planned {field}: "
                f"{value.get(field)!r} != {expected!r}"
            )

    attempt = value.get(MATRIX_ATTEMPT_FIELD)
    if isinstance(attempt, bool) or attempt not in (1, 2):
        raise BenchmarkToolError(f"matrix final record has an invalid attempt: {record_label}")
    if expected_attempt is not None and attempt != expected_attempt:
        raise BenchmarkToolError(
            f"matrix final record attempt does not match its active marker: {record_label}"
        )

    if (
        freeze_check.get("schema_version") != 1
        or freeze_check.get("kind") != "highambench-frozen-run-verification"
        or freeze_check.get("ok") is not True
    ):
        raise BenchmarkToolError("cannot authenticate a final record against an invalid freeze")
    freeze_agent = _mapping(freeze_check.get("agent"), "freeze-check agent")
    expected_agent = {
        "id": freeze_agent.get("id"),
        "version": freeze_agent.get("version"),
        "model": freeze_agent.get("model"),
        "reasoning_effort": freeze_agent.get("reasoning_effort"),
    }
    if value.get("agent") != expected_agent:
        raise BenchmarkToolError(f"matrix final record has stale agent provenance: {record_label}")
    if value.get("environment_id") != freeze_check.get("environment_id"):
        raise BenchmarkToolError(
            f"matrix final record has a stale environment identity: {record_label}"
        )
    owning_freeze = _authenticate_embedded_freeze_check(
        value, freeze_check, label=f"matrix final record {record_label}"
    )

    frozen_limits = _mapping(freeze_check.get("limits"), "freeze-check limits")
    record_limits = _mapping(value.get("limits"), f"matrix final record {record_label} limits")
    if (
        record_limits.get("time_seconds") != frozen_limits.get("wall_clock_seconds")
        or record_limits.get("model_tokens") != frozen_limits.get("total_model_tokens")
        or record_limits.get("prompt_startup_seconds")
        != frozen_limits.get("prompt_startup_timeout_seconds")
    ):
        raise BenchmarkToolError(f"matrix final record has stale frozen limits: {record_label}")

    allocation = value.get("allocation_hardware")
    if not isinstance(allocation, Mapping):
        raise BenchmarkToolError(
            f"matrix final record has no allocation hardware descriptor: {record_label}"
        )
    verify_allocation_hardware_descriptor(results_root, allocation, owning_freeze)

    if value.get("useful_work_started") is not True or value.get("scored") is not True:
        raise BenchmarkToolError(
            f"matrix final record is not a scored useful-work outcome: {record_label}"
        )
    protocol = _mapping(
        value.get("protocol"), f"matrix final record {record_label} protocol"
    )
    if protocol.get("complete") is not True:
        raise BenchmarkToolError(
            f"matrix final record has an incomplete frozen protocol: {record_label}"
        )
    authenticate_runner_provider_gate_summary(value)
    accepted_pass = _accepted_pass_has_exact_boundary(value)
    token_crossing = _failed_attempt_has_exact_provider_gate_crossing(value)
    natural_failure = _failed_attempt_has_exact_natural_drain(value)
    if not accepted_pass and not token_crossing and not natural_failure:
        raise BenchmarkToolError(
            "matrix final record is outside the Ultra positive outcome allowlist: "
            f"{record_label}"
        )
    if natural_failure and value.get("failure_code") not in EXPECTED_FAILURE_REASON_PRIORITY:
        raise BenchmarkToolError(
            f"matrix final record has an invalid scored failure reason: {record_label}"
        )
    return value


def _authenticate_existing_final_records(
    results_root: Path,
    records_dir: Path,
    assignments: Iterable[Mapping[str, Any]],
    freeze_check: Mapping[str, Any],
) -> dict[str, dict[str, Any]]:
    """Authenticate every present planned final before any hosted subprocess starts."""

    authenticated: dict[str, dict[str, Any]] = {}
    for assignment in assignments:
        run_id = _nonempty_string(assignment.get("run_id"), "assignment run_id")
        path = records_dir / f"{run_id}.json"
        if path.exists() or path.is_symlink():
            authenticated[run_id] = _authenticate_final_assignment_record(
                results_root, path, assignment, freeze_check
            )
    grouped: dict[str, list[tuple[Mapping[str, Any], Mapping[str, Any]]]] = {}
    for assignment in assignments:
        final = authenticated.get(str(assignment.get("run_id")))
        if final is not None:
            grouped.setdefault(str(assignment.get("pair_id")), []).append(
                (assignment, final)
            )
    for pair_id, present in grouped.items():
        if len(present) == 2:
            conditions = {str(assignment.get("condition")) for assignment, _ in present}
            if conditions != {"N", "L"}:
                raise BenchmarkToolError(
                    f"completed pair {pair_id!r} does not contain exact N/L conditions"
                )
            descriptors = [final.get("allocation_hardware") for _, final in present]
            if descriptors[0] != descriptors[1]:
                raise BenchmarkToolError(
                    f"completed pair {pair_id!r} does not share one exact allocation descriptor"
                )
    return authenticated


def _verify_partial_pairs_use_current_allocation(
    assignments: Iterable[Mapping[str, Any]],
    authenticated_finals: Mapping[str, Mapping[str, Any]],
    current_allocation: Mapping[str, Any],
) -> None:
    """Reject a half pair before any provider use on another allocation."""

    grouped: dict[str, list[Mapping[str, Any]]] = {}
    for assignment in assignments:
        final = authenticated_finals.get(str(assignment.get("run_id")))
        if final is not None:
            grouped.setdefault(str(assignment.get("pair_id")), []).append(final)
    for pair_id, finals in grouped.items():
        if len(finals) == 1 and finals[0].get("allocation_hardware") != dict(
            current_allocation
        ):
            raise BenchmarkToolError(
                f"half-finished pair {pair_id!r} is bound to another allocation; "
                "archive the uncommitted pair root and rerun both conditions"
            )


def pair_commit_digest(value: Mapping[str, Any]) -> str:
    payload = dict(value)
    payload.pop(PAIR_COMMIT_SHA256_FIELD, None)
    return canonical_document_digest(payload)


def _pair_commit_payload(
    results_root: Path,
    assignments: Sequence[Mapping[str, Any]],
    reference_freeze: Mapping[str, Any],
) -> dict[str, Any]:
    if len(assignments) != 2:
        raise BenchmarkToolError("pair commit requires exactly two assignments")
    pair_ids = {str(item.get("pair_id")) for item in assignments}
    if len(pair_ids) != 1 or {item.get("condition") for item in assignments} != {"N", "L"}:
        raise BenchmarkToolError("pair commit assignments are not one exact N/L pair")
    pair_id = next(iter(pair_ids))
    by_condition = {str(item.get("condition")): item for item in assignments}
    condition_order = list(assignments[0].get("condition_order", []))
    if condition_order not in (["N", "L"], ["L", "N"]):
        raise BenchmarkToolError("pair commit has an invalid canonical condition order")
    finals: dict[str, dict[str, Any]] = {}
    allocation_descriptor: dict[str, Any] | None = None
    freeze_digest: str | None = None
    for condition in ("N", "L"):
        assignment = by_condition[condition]
        run_id = _nonempty_string(assignment.get("run_id"), "pair assignment run_id")
        path = results_root / "records" / f"{run_id}.json"
        final = _authenticate_final_assignment_record(
            results_root, path, assignment, reference_freeze
        )
        descriptor = _mapping(
            final.get("allocation_hardware"), f"pair final {run_id} allocation"
        )
        if allocation_descriptor is None:
            allocation_descriptor = dict(descriptor)
        elif descriptor != allocation_descriptor:
            raise BenchmarkToolError(
                f"pair {pair_id!r} finals do not share one exact allocation descriptor"
            )
        wrapper = _mapping(
            final.get("frozen_run_verification"), f"pair final {run_id} freeze wrapper"
        )
        owning_digest = _sha256_value(
            wrapper.get("freeze_check_sha256"), f"pair final {run_id} freeze SHA-256"
        )
        if freeze_digest is None:
            freeze_digest = owning_digest
        elif owning_digest != freeze_digest:
            raise BenchmarkToolError(
                f"pair {pair_id!r} finals do not share one exact allocation freeze"
            )
        finals[condition] = {
            "run_id": run_id,
            "path": f"records/{run_id}.json",
            "sha256": sha256_file(path),
            "matrix_record_sha256": _sha256_value(
                final.get(MATRIX_RECORD_SHA256_FIELD),
                f"pair final {run_id} matrix self-hash",
            ),
        }
    assert allocation_descriptor is not None and freeze_digest is not None
    return {
        "schema_version": 1,
        "kind": PAIR_COMMIT_KIND,
        "pair_id": pair_id,
        "condition_order": condition_order,
        "run_ids": [
            _nonempty_string(by_condition[condition].get("run_id"), "pair run_id")
            for condition in condition_order
        ],
        "final_records": finals,
        "allocation_hardware": allocation_descriptor,
        "freeze_check_sha256": freeze_digest,
        "hardware_matching_policy_sha256": canonical_document_digest(
            HARDWARE_MATCHING_POLICY
        ),
    }


def create_or_verify_pair_commit(
    results_root: Path,
    assignments: Sequence[Mapping[str, Any]],
    reference_freeze: Mapping[str, Any],
) -> dict[str, Any]:
    """Atomically authenticate and commit one complete pair root."""

    expected = _pair_commit_payload(results_root, assignments, reference_freeze)
    expected[PAIR_COMMIT_SHA256_FIELD] = pair_commit_digest(expected)
    path = results_root / PAIR_COMMIT_PATH
    if path.is_symlink():
        raise BenchmarkToolError("pair commit must not be a symlink")
    if path.exists():
        if not path.is_file():
            raise BenchmarkToolError("pair commit is not a regular file")
        existing = _mapping(read_json(path), "pair commit")
        if set(existing) != PAIR_COMMIT_FIELDS:
            raise BenchmarkToolError("pair commit fields are not exact")
        stored = _sha256_value(
            existing.get(PAIR_COMMIT_SHA256_FIELD), "pair commit self-hash"
        )
        if stored != pair_commit_digest(existing):
            raise BenchmarkToolError("pair commit self-hash is invalid")
        if dict(existing) != expected:
            raise BenchmarkToolError("pair commit is stale or differs from exact finals")
        if stat.S_IMODE(path.stat().st_mode) != 0o444:
            raise BenchmarkToolError("pair commit mode is not immutable 0444")
        return dict(existing)
    write_json(path, expected)
    path.chmod(0o444)
    return create_or_verify_pair_commit(results_root, assignments, reference_freeze)


def pair_commit_descriptor(results_root: Path, commit: Mapping[str, Any]) -> dict[str, str]:
    path = results_root / PAIR_COMMIT_PATH
    if not path.is_file() or path.is_symlink():
        raise BenchmarkToolError("authenticated pair commit file is missing")
    return {
        "path": PAIR_COMMIT_PATH,
        "sha256": sha256_file(path),
        PAIR_COMMIT_SHA256_FIELD: _sha256_value(
            commit.get(PAIR_COMMIT_SHA256_FIELD), "pair commit self-hash"
        ),
    }


def verify_pair_commit(
    results_root: Path,
    assignments: Sequence[Mapping[str, Any]],
    reference_freeze: Mapping[str, Any],
) -> dict[str, Any]:
    path = results_root / PAIR_COMMIT_PATH
    if not path.exists() and not path.is_symlink():
        raise BenchmarkToolError("pair root has no pair_commit.json")
    return create_or_verify_pair_commit(results_root, assignments, reference_freeze)


def _authenticate_existing_incidents(
    results_root: Path,
    incidents_dir: Path,
    assignments: Iterable[Mapping[str, Any]],
    freeze_check: Mapping[str, Any],
    authenticated_finals: Mapping[str, Mapping[str, Any]],
) -> dict[str, dict[int, dict[str, Any]]]:
    """Authenticate the complete saved incident set before any provider work."""

    planned = list(assignments)
    expected_paths = {
        incidents_dir / f"{assignment['run_id']}.attempt-{attempt}.json"
        for assignment in planned
        for attempt in (1, 2)
    }
    if incidents_dir.exists() or incidents_dir.is_symlink():
        if incidents_dir.is_symlink() or not incidents_dir.is_dir():
            raise BenchmarkToolError(
                "matrix incidents path is not a regular non-symlink directory"
            )
        for path in incidents_dir.iterdir():
            if path.suffix == ".json" and path not in expected_paths:
                raise BenchmarkToolError(f"unmatched matrix incident file: {path}")

    authenticated: dict[str, dict[int, dict[str, Any]]] = {}
    for assignment in planned:
        run_id = _nonempty_string(assignment.get("run_id"), "assignment run_id")
        per_attempt: dict[int, dict[str, Any]] = {}
        for attempt, path in (
            (1, incidents_dir / f"{run_id}.attempt-1.json"),
            (2, incidents_dir / f"{run_id}.attempt-2.json"),
        ):
            if path.exists() or path.is_symlink():
                per_attempt[attempt] = _authenticate_matrix_incident(
                    results_root,
                    path,
                    assignment,
                    freeze_check,
                    expected_attempt=attempt,
                )
        if per_attempt:
            statuses = {
                attempt: value.get("matrix_incident", {}).get("status")
                for attempt, value in per_attempt.items()
            }
            if any(
                status
                in {
                    "terminal_pre_prompt_system_error",
                    "aborted_after_unscorable_useful_work",
                }
                for status in statuses.values()
            ):
                raise BenchmarkToolError(
                    f"terminal or unscorable matrix incident blocks resume for {run_id}"
                )
            final = authenticated_finals.get(run_id)
            if (
                set(per_attempt) != {1}
                or statuses.get(1) != "retryable_pre_prompt_system_error"
                or final is None
                or final.get(MATRIX_ATTEMPT_FIELD) != 2
            ):
                raise BenchmarkToolError(
                    f"interrupted startup retry blocks resume for {run_id}"
                )
            authenticated[run_id] = per_attempt
    return authenticated


def _assignment_task_identity(
    root: Path, assignment: Mapping[str, Any]
) -> Mapping[str, Any]:
    common = {
        "task_id",
        "paper_id",
        "paper_sha256",
        "tier",
        "target_dir",
        "target_file",
        "context_file",
    }
    if common.issubset(assignment):
        identity: dict[str, Any] = {
            field: str(assignment[field]) for field in common
        }
        if identity["tier"] == "T4":
            for field in (
                "required_declarations",
                "proof_declarations",
                "controlled_sorries",
            ):
                value = assignment.get(field)
                if not isinstance(value, list) or not value:
                    raise BenchmarkToolError(
                        f"T4 assignment lacks ordered {field}"
                    )
                identity[field] = [
                    dict(item) if isinstance(item, Mapping) else item for item in value
                ]
            identity["required_declaration"] = str(
                identity["proof_declarations"][0]
            )
            identity["theorem_name"] = identity["required_declaration"].rsplit(
                ".", 1
            )[-1]
        else:
            for field in ("theorem_name", "required_declaration"):
                if field not in assignment:
                    raise BenchmarkToolError(
                        f"singular assignment lacks {field}"
                    )
                identity[field] = str(assignment[field])
        return identity
    task_id = _nonempty_string(assignment.get("task_id"), "assignment task_id")
    task = load_task_catalog(root).get(task_id)
    if task is None:
        raise BenchmarkToolError(f"assignment names unknown task {task_id}")
    return task


def _allocation_end_epoch(args: argparse.Namespace) -> float | None:
    """Return the explicit or Slurm-provided allocation deadline.

    Slurm exports ``SLURM_JOB_END_TIME`` as a UNIX timestamp in batch and
    interactive jobs.  An explicit command-line value is useful for tests and
    non-Slurm launchers and takes precedence over the environment.
    """

    raw: Any = getattr(args, "allocation_end_epoch", None)
    if raw is None:
        raw = os.environ.get(SLURM_JOB_END_TIME_ENV)
    if raw in (None, ""):
        return None
    try:
        value = float(raw)
    except (TypeError, ValueError) as error:
        raise BenchmarkToolError(
            f"{SLURM_JOB_END_TIME_ENV} or --allocation-end-epoch must be a UNIX timestamp"
        ) from error
    if not value.is_integer() or value <= 0:
        raise BenchmarkToolError("allocation end epoch must be a positive integer")
    return value


def _unfinished_runs_in_pair(
    assignments: list[dict[str, Any]],
    start_index: int,
    records_dir: Path,
    results_root: Path,
    freeze_check: Mapping[str, Any],
    *,
    force: bool = False,
) -> int:
    pair_id = assignments[start_index]["pair_id"]
    unfinished = 0
    for assignment in assignments[start_index:]:
        if assignment["pair_id"] != pair_id:
            continue
        if force:
            unfinished += 1
            continue
        path = records_dir / f"{assignment['run_id']}.json"
        if path.exists() or path.is_symlink():
            _authenticate_final_assignment_record(
                results_root, path, assignment, freeze_check
            )
        else:
            unfinished += 1
    return unfinished


def _required_allocation_seconds(
    unfinished_pair_runs: int,
    *,
    run_limit_seconds: float,
    prompt_startup_timeout_seconds: float,
    post_submission_validation_reserve_seconds: float,
    guard_seconds: float,
) -> float:
    if unfinished_pair_runs <= 0:
        raise BenchmarkToolError("unfinished pair-run count must be positive")
    if (
        run_limit_seconds <= 0
        or prompt_startup_timeout_seconds <= 0
        or post_submission_validation_reserve_seconds <= 0
        or guard_seconds < 0
    ):
        raise BenchmarkToolError("allocation timing limits are invalid")
    # Every assignment permits one retry after a pre-prompt SYSTEM_ERROR.  Each
    # Popen may consume the full startup-handshake timeout outside measured run
    # time, so reserve two such windows before the one worst-case scored run.
    # The named post-submission reserve covers the complete serial hidden
    # validation and process-closure tail; it is separate from the general
    # allocation cleanup guard.
    return unfinished_pair_runs * (
        run_limit_seconds
        + 2 * prompt_startup_timeout_seconds
        + post_submission_validation_reserve_seconds
    ) + guard_seconds


def _clear_or_reject_interrupted_run(
    marker: Path,
    records_dir: Path,
    results_root: Path,
    assignments: Iterable[Mapping[str, Any]],
    freeze_check: Mapping[str, Any],
) -> None:
    """Never silently turn an externally interrupted hosted session into a retry."""

    if not marker.exists() and not marker.is_symlink():
        return
    if marker.is_symlink() or not marker.is_file():
        raise BenchmarkToolError("active-run marker is not a regular non-symlink file")
    value = _mapping(read_json(marker), "active-run marker")
    expected_fields = {
        "schema_version",
        "kind",
        "assignment",
        "attempt",
        "attempt_output",
        "started_at_unix",
        "allocation_hardware",
    }
    if set(value) != expected_fields:
        raise BenchmarkToolError("active-run marker fields are not exact")
    if (
        value.get("schema_version") != ACTIVE_RUN_MARKER_SCHEMA_VERSION
        or value.get("kind") != "highambench-active-hosted-attempt"
    ):
        raise BenchmarkToolError("active-run marker header is invalid")
    marker_assignment = _mapping(value.get("assignment"), "active-run assignment")
    run_id = _nonempty_string(marker_assignment.get("run_id"), "active-run marker run_id")
    planned_by_run_id = {
        _nonempty_string(item.get("run_id"), "assignment run_id"): item
        for item in assignments
    }
    planned = planned_by_run_id.get(run_id)
    if planned is None or dict(marker_assignment) != _planned_assignment_record_identity(planned):
        raise BenchmarkToolError("active-run marker does not name the exact planned assignment")
    attempt = value.get("attempt")
    if isinstance(attempt, bool) or attempt not in (1, 2):
        raise BenchmarkToolError("active-run marker attempt must be 1 or 2")
    started_at = value.get("started_at_unix")
    if isinstance(started_at, bool) or not isinstance(started_at, (int, float)) or started_at <= 0:
        raise BenchmarkToolError("active-run marker start time is invalid")
    expected_attempt_output = f"attempts/{run_id}.attempt-{attempt}.json"
    if value.get("attempt_output") != expected_attempt_output:
        raise BenchmarkToolError("active-run marker attempt-output path is invalid")
    marker_allocation = _mapping(
        value.get("allocation_hardware"), "active-run allocation hardware"
    )
    verify_allocation_hardware_descriptor(results_root, marker_allocation, freeze_check)
    final_record = records_dir / f"{run_id}.json"
    if final_record.exists() or final_record.is_symlink():
        final = _authenticate_final_assignment_record(
            results_root,
            final_record,
            planned,
            freeze_check,
            expected_attempt=attempt,
        )
        if final.get("allocation_hardware") != dict(marker_allocation):
            raise BenchmarkToolError(
                "active-run allocation descriptor does not bind to the final record"
            )
        attempt_output = (results_root / expected_attempt_output).resolve()
        try:
            attempt_output.relative_to(results_root.resolve())
        except ValueError as error:
            raise BenchmarkToolError("active-run attempt output escapes results root") from error
        if attempt_output.is_symlink() or not attempt_output.is_file():
            raise BenchmarkToolError("active-run marker's sealed attempt output is missing")
        attempt_value = read_json(attempt_output)
        if not isinstance(attempt_value, Mapping) or dict(attempt_value) != final:
            raise BenchmarkToolError(
                "active-run marker attempt output does not exactly bind to the final record"
            )
        marker.unlink()
        return
    raise BenchmarkToolError(
        "the previous matrix invocation ended during hosted attempt "
        f"{run_id!r}; the marker {marker} was retained so that the attempt cannot "
        "be silently discarded or retried. Audit the partial logs and record the "
        "infrastructure incident before resuming."
    )


def _attempt_usage_output(args: argparse.Namespace, attempt_output: Path) -> Path:
    """Return the trusted provider-usage path for one concrete attempt.

    The path is deliberately outside the model-writable workspace and unique to
    the retry number, so a startup retry can never consume a previous attempt's
    cumulative counter.
    """

    return (
        args.results_root.resolve()
        / "logs"
        / f"{attempt_output.stem}.usage.json"
    )


def runner_command(args: argparse.Namespace, assignment: dict[str, Any], attempt_jsonl: Path,
                   attempt_output: Path, base_workspace: Path) -> list[str]:
    root = args.benchmark_root.resolve()
    project = args.project_root.resolve()
    task = _assignment_task_identity(root, assignment)
    task_id = task["task_id"]
    paper_id = task["paper_id"]
    paper_sha256 = task["paper_sha256"]
    tier = task["tier"]
    condition = assignment["condition"]
    target_declaration = task["required_declaration"]
    plural = tier == "T4"
    required_declarations = list(task.get("required_declarations", ()))
    controlled_sorries = list(task.get("controlled_sorries", ()))
    if plural and (not required_declarations or not controlled_sorries):
        raise BenchmarkToolError("T4 runner command lacks its plural controlled surface")
    plural_runner_arguments: list[str] = []
    if plural:
        for lean_name in required_declarations:
            plural_runner_arguments.extend(("--required-declaration", lean_name))
        for hole in controlled_sorries:
            plural_runner_arguments.extend(
                (
                    "--controlled-sorry-json",
                    json.dumps(
                        hole,
                        sort_keys=True,
                        separators=(",", ":"),
                        ensure_ascii=False,
                    ),
                )
            )
    task_shared_olean_root = args.shared_olean_root.resolve() / paper_id
    usage_output = _attempt_usage_output(args, attempt_output)
    library_arguments = (
        [
            "--library-source",
            str(args.library_source.resolve()),
            "--library-root-file",
            str(args.library_root_file.resolve()),
            "--library-olean",
            str(args.library_olean.resolve()),
        ]
        if condition == "L"
        else []
    )
    common_adapter = [
        sys.executable,
        str(root / "tools" / "codex_isolated.py"),
        "--condition",
        condition,
        "--workspace",
        "{workspace}",
        "--prompt-file",
        "{workspace}/task/agent_prompt.md",
        "--context-file",
        f"{{workspace}}/task/{task['context_file']}",
        "--target-file",
        f"{{workspace}}/task/{task['target_file']}",
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
        "--shared-olean-root",
        str(task_shared_olean_root),
        *library_arguments,
        "--model",
        args.model,
        "--reasoning-effort",
        args.reasoning_effort,
        "--token-limit",
        str(args.token_limit),
        "--advisory-rollout-budget-limit",
        str(args.token_limit),
    ]
    if condition == "L":
        condition_prompt = root / CONDITION_L_PROMPT_RELATIVE
        common_adapter.extend(
            (
                "--condition-prompt-file",
                str(condition_prompt.resolve()),
                "--condition-prompt-sha256",
                sha256_file(condition_prompt),
            )
        )
    for option, expected in (
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
        positions = [index for index, value in enumerate(common_adapter) if value == option]
        if (
            len(positions) != 1
            or positions[0] + 1 >= len(common_adapter)
            or common_adapter[positions[0] + 1] != expected
        ):
            raise BenchmarkToolError(
                f"trusted agent command must contain exactly one {option} placeholder"
            )
    lean_base = [
        sys.executable,
        str(root / "tools" / "lean_isolated.py"),
        "--condition",
        condition,
        "--workspace",
        "{workspace}",
        "--toolchain-root",
        str(args.toolchain_root.resolve()),
        "--packages-root",
        str(args.packages_runtime_root.resolve()),
        "--shared-olean-root",
        str(task_shared_olean_root),
        *library_arguments,
    ]
    compile_command = lean_base[:2] + ["olean"] + lean_base[2:] + [
        "--source", "{checked_submission}"
    ]
    probe_command = lean_base[:2] + ["probe"] + lean_base[2:] + [
        "--source", "{probe}"
    ]
    audit_identity_arguments = (
        [
            "--audit-pairs-file",
            "{audit_pairs_file}",
            "--expected-module",
            "{expected_module}",
            "--local-modules-file",
            "{local_modules_file}",
        ]
        if plural
        else [
            "--target-theorem",
            target_declaration,
            "--expected-module",
            "{expected_module}",
            "--expected-theorem",
            "{expected_theorem}",
            "--local-modules-file",
            "{local_modules_file}",
        ]
    )
    audit_command = lean_base[:2] + ["audit"] + lean_base[2:] + [
        "--source", "{checked_submission}",
        "--audit-helper", str((root / "tools" / "dependency_audit.lean").resolve()),
        "--submission-module", "{submission_module}",
        *audit_identity_arguments,
    ]

    pair_order = "N-first" if assignment["condition_order"][0] == "N" else "L-first"
    command = [
        sys.executable,
        str((root / "tools" / "runner.py").resolve()),
        "--condition", condition,
        "--task-id", task_id,
        "--paper-id", paper_id,
        "--paper-sha256", paper_sha256,
        "--tier", tier,
        "--repetition-id", assignment["repetition_id"],
        "--pair-id", assignment["pair_id"],
        "--pair-order", pair_order,
        "--order-index", str(assignment["order_index"]),
        "--run-id", assignment["run_id"],
        "--agent-id", args.agent_id,
        "--agent-version", args.agent_version,
        "--model", args.model,
        "--reasoning-effort", args.reasoning_effort,
        "--environment-id", args.environment_id,
        "--freeze-check-json", args.freeze_check_json,
        "--base-workspace", str(base_workspace),
        "--task-root", str(root),
        "--controlled-manifest", str(root / "metadata" / "controlled" / f"{task_id}.json"),
        "--task-dest", "task",
        "--workspace-parent", str((args.results_root / "workspaces").resolve()),
        "--logs-dir", str((args.results_root / "logs").resolve()),
        "--raw-jsonl", str(attempt_jsonl),
        "--submission-relative", "Submission.lean",
        "--canonical-relative", f"task/{task['target_file']}",
        "--target-theorem", target_declaration,
        *plural_runner_arguments,
        "--submission-module", "Submission",
        "--audit-helper", str((root / "tools" / "dependency_audit.lean").resolve()),
        "--reject-workspace-local-module-imports",
        "--prompt-relative", "task/agent_prompt.md",
        "--usage-output", str(usage_output),
        "--agent-command-json", _json_argv(common_adapter),
        "--compile-command-json", _json_argv(compile_command),
        "--audit-command-json", _json_argv(audit_command),
        "--n-probe-command-json", _json_argv(probe_command),
        "--hidden-parent", str((args.results_root / "hidden").resolve()),
        "--time-limit-seconds", str(args.time_limit_seconds),
        "--prompt-startup-timeout-seconds",
        str(args.prompt_startup_timeout_seconds),
        "--validation-timeout-seconds",
        str(DEFAULT_VALIDATION_COMPILE_TIMEOUT_SECONDS),
        "--audit-timeout-seconds",
        str(DEFAULT_VALIDATION_AUDIT_TIMEOUT_SECONDS),
        "--token-limit", str(args.token_limit),
        "--fresh-conversation",
        "--filesystem-isolated",
        "--output", str(attempt_output),
    ]
    if args.agent_network_verified:
        command.append("--network-disabled")
    if args.token_control_verified:
        command.append("--token-enforced")
    if condition == "L":
        command.append("--library-available")
    backend_seed = assignment.get("backend_seed")
    if backend_seed is not None:
        if isinstance(backend_seed, bool) or not isinstance(backend_seed, int):
            raise BenchmarkToolError("assignment backend seed must be an integer or null")
        command.extend(("--seed", str(backend_seed)))
    return command


def run(args: argparse.Namespace) -> int:
    root = _require_dir(args.benchmark_root, "benchmark root")
    _require_dir(args.project_root, "project root")
    for path, label in (
        (args.codex, "Codex executable"),
        (args.auth_file, "Codex auth file"),
        (args.offline_shell, "offline shell"),
        (args.library_root_file, "library root file"),
    ):
        _require_file(path, label)
    for path, label in (
        (args.toolchain_root, "Lean toolchain"),
        (args.packages_root, "Lake packages"),
        (args.packages_runtime_root, "pruned packages runtime"),
        (args.shared_olean_root, "shared olean root"),
        (args.library_source, "library source"),
        (args.library_olean, "library olean root"),
    ):
        _require_dir(path, label)
    freeze_check = verify_frozen_run_environment(args, root)
    manifest = _mapping(
        read_json(root / "metadata" / "manifest.json"), "benchmark manifest"
    )
    config = _mapping(read_json(root / "metadata" / "config.json"), "config")
    task_catalog = load_task_catalog(root, manifest)
    repetition_ids = configured_repetition_ids(config)
    repetition_backend_seeds: dict[str, int | None] = {}
    for raw_repetition in config["repetitions"]:
        repetition = _mapping(raw_repetition, "config repetition")
        repetition_id = _nonempty_string(
            repetition.get("id"), "config repetition id"
        )
        backend_seed = repetition.get("backend_seed")
        if backend_seed is not None and (
            isinstance(backend_seed, bool) or not isinstance(backend_seed, int)
        ):
            raise BenchmarkToolError(
                f"config repetition {repetition_id} has an invalid backend_seed"
            )
        repetition_backend_seeds[repetition_id] = backend_seed
    _validate_planned_counts(config, task_catalog, repetition_ids)
    order = _mapping(read_json(root / "metadata" / "run_order.json"), "run order")
    assignments = assignments_from_order(order, task_catalog, repetition_ids)
    for assignment in assignments:
        assignment["backend_seed"] = repetition_backend_seeds[
            assignment["repetition_id"]
        ]
    expected_runs = len(task_catalog) * len(repetition_ids) * 2
    if len(assignments) != expected_runs:
        raise BenchmarkToolError(
            f"expected {expected_runs} assignments from frozen metadata, "
            f"found {len(assignments)}"
        )
    only_pair_id = getattr(args, "only_pair_id", None)
    if only_pair_id is not None:
        if getattr(args, "stop_after_paper", None) is not None:
            raise BenchmarkToolError(
                "--only-pair-id and --stop-after-paper are mutually exclusive"
            )
        if getattr(args, "force", False):
            raise BenchmarkToolError(
                "--force is forbidden for an atomic pair root; archive it and rerun both conditions"
            )
        assignments = _assignments_for_only_pair(assignments, only_pair_id)
    stop_after_paper = getattr(args, "stop_after_paper", None)
    paper_boundary_index = _paper_boundary_index(assignments, stop_after_paper)

    results = args.results_root.resolve()
    records = results / "records"
    attempts = results / "attempts"
    incidents = results / "incidents"
    for directory in (records, attempts, incidents, results / "logs", results / "workspaces"):
        directory.mkdir(parents=True, exist_ok=True)
    if only_pair_id is not None:
        _reject_foreign_pair_records(results, assignments)
    active_marker = results / ACTIVE_RUN_MARKER
    _clear_or_reject_interrupted_run(
        active_marker, records, results, assignments, freeze_check
    )
    authenticated_finals: dict[str, dict[str, Any]] = {}
    if not args.force:
        # Authenticate the complete present prefix/set before any hosted process
        # starts.  A corrupt later record must not permit earlier work to rerun.
        authenticated_finals = _authenticate_existing_final_records(
            results, records, assignments, freeze_check
        )
    # Incident checkpoints are security-sensitive even under --force: no later
    # provider request may start while a saved retry/unscorable ledger is
    # corrupt, stale, or unmatched.
    _authenticate_existing_incidents(
        results,
        incidents,
        assignments,
        freeze_check,
        authenticated_finals,
    )
    if only_pair_id is not None and len(authenticated_finals) == 2:
        commit = create_or_verify_pair_commit(results, assignments, freeze_check)
        _rebuild_jsonl(
            records,
            incidents,
            assignments,
            results / "runs.jsonl",
            results_root=results,
            freeze_check=freeze_check,
        )
        _write_pair_complete_status(results, str(only_pair_id), commit)
        print(f"HighamBench pair complete: {only_pair_id} (2/2 assignments)")
        return 0
    if only_pair_id is not None and (results / PAIR_COMMIT_PATH).exists():
        raise BenchmarkToolError(
            "pair_commit.json exists without two authenticated final records"
        )
    allocation_hardware = create_or_verify_allocation_hardware_record(
        results, freeze_check
    )
    _verify_partial_pairs_use_current_allocation(
        assignments, authenticated_finals, allocation_hardware
    )
    write_json(results / "freeze_check.json", freeze_check)
    args.freeze_check_json = json.dumps(
        freeze_check, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    )
    allocation_end_epoch = _allocation_end_epoch(args)
    allocation_guard_seconds = float(
        getattr(args, "allocation_guard_seconds", DEFAULT_ALLOCATION_GUARD_SECONDS)
    )
    prompt_startup_timeout_seconds = float(
        getattr(
            args,
            "prompt_startup_timeout_seconds",
            DEFAULT_PROMPT_STARTUP_TIMEOUT_SECONDS,
        )
    )
    post_submission_validation_reserve_seconds = float(
        getattr(
            args,
            "post_submission_validation_reserve_seconds",
            DEFAULT_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS,
        )
    )
    args.prompt_startup_timeout_seconds = prompt_startup_timeout_seconds
    if allocation_guard_seconds < 0:
        raise BenchmarkToolError("allocation guard seconds must be nonnegative")
    if prompt_startup_timeout_seconds != DEFAULT_PROMPT_STARTUP_TIMEOUT_SECONDS:
        raise BenchmarkToolError("prompt startup timeout must be exactly 120 seconds")
    if (
        post_submission_validation_reserve_seconds
        != DEFAULT_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS
    ):
        raise BenchmarkToolError(
            "post-submission validation reserve must be exactly 369 seconds"
        )

    with tempfile.TemporaryDirectory(prefix="highambench-base-", dir=results) as raw_base:
        base = Path(raw_base)
        stopped_for_allocation_deadline: dict[str, Any] | None = None
        stopped_after_requested_paper: dict[str, Any] | None = None
        # An atomic pair is admitted against the complete two-run envelope once.
        # Rechecking after its first final could clean-stop with a half pair even
        # though the original reservation included both run envelopes and the
        # cleanup guard.  Once admitted, finish both conditions or fail closed;
        # never manufacture an allocation checkpoint between N and L.
        atomic_pair_deadline_admitted = False
        for assignment_index, assignment in enumerate(assignments):
            if (
                paper_boundary_index is not None
                and assignment_index >= paper_boundary_index
            ):
                completed_through_boundary = len(
                    _authenticate_existing_final_records(
                        results,
                        records,
                        assignments[:paper_boundary_index],
                        freeze_check,
                    )
                )
                if completed_through_boundary != paper_boundary_index:
                    raise BenchmarkToolError(
                        "requested paper boundary was reached before all preceding "
                        "assignments had final records"
                    )
                previous = assignments[paper_boundary_index - 1]
                stopped_after_requested_paper = {
                    "schema_version": 1,
                    "kind": "highambench-matrix-chunk-status",
                    "status": "stopped_after_requested_paper",
                    "requested_paper_id": stop_after_paper,
                    "last_run_id": previous["run_id"],
                    "last_pair_id": previous["pair_id"],
                    "completed_runs_through_boundary": completed_through_boundary,
                    "planned_runs_through_boundary": paper_boundary_index,
                    "next_run_id": assignment["run_id"],
                    "next_pair_id": assignment["pair_id"],
                    "next_paper_id": assignment["paper_id"],
                    "matrix_planned_runs": len(assignments),
                }
                write_json(
                    results / "last_chunk_status.json",
                    stopped_after_requested_paper,
                )
                break
            final_record = records / f"{assignment['run_id']}.json"
            if (final_record.exists() or final_record.is_symlink()) and not args.force:
                _authenticate_final_assignment_record(
                    results, final_record, assignment, freeze_check
                )
                continue
            if allocation_end_epoch is not None and (
                only_pair_id is None or not atomic_pair_deadline_admitted
            ):
                unfinished_pair_runs = _unfinished_runs_in_pair(
                    assignments,
                    assignment_index,
                    records,
                    results,
                    freeze_check,
                    force=args.force,
                )
                required_seconds = _required_allocation_seconds(
                    unfinished_pair_runs,
                    run_limit_seconds=float(args.time_limit_seconds),
                    prompt_startup_timeout_seconds=prompt_startup_timeout_seconds,
                    post_submission_validation_reserve_seconds=(
                        post_submission_validation_reserve_seconds
                    ),
                    guard_seconds=allocation_guard_seconds,
                )
                remaining_seconds = allocation_end_epoch - time.time()
                if remaining_seconds < required_seconds:
                    stopped_for_allocation_deadline = {
                        "schema_version": 1,
                        "kind": "highambench-matrix-chunk-status",
                        "status": "stopped_before_allocation_deadline",
                        "next_run_id": assignment["run_id"],
                        "next_pair_id": assignment["pair_id"],
                        "unfinished_runs_in_next_pair": unfinished_pair_runs,
                        "allocation_end_epoch": int(allocation_end_epoch),
                        "remaining_seconds": round(remaining_seconds, 6),
                        "required_seconds": round(required_seconds, 6),
                        "prompt_startup_timeout_seconds": (
                            prompt_startup_timeout_seconds
                        ),
                        "startup_timeouts_reserved_per_unfinished_run": 2,
                        "post_submission_validation_reserve_seconds": (
                            post_submission_validation_reserve_seconds
                        ),
                        "guard_seconds": allocation_guard_seconds,
                    }
                    write_json(results / "last_chunk_status.json", stopped_for_allocation_deadline)
                    break
                if only_pair_id is not None:
                    atomic_pair_deadline_admitted = True
            if args.force:
                for old_incident in _incident_record_paths(incidents, assignment["run_id"]):
                    old_incident.unlink()
            selected: dict[str, Any] | None = None
            for attempt in (1, 2):
                attempt_jsonl = attempts / f"{assignment['run_id']}.attempt-{attempt}.jsonl"
                attempt_output = attempts / f"{assignment['run_id']}.attempt-{attempt}.json"
                attempt_jsonl.unlink(missing_ok=True)
                attempt_output.unlink(missing_ok=True)
                _attempt_usage_output(args, attempt_output).unlink(missing_ok=True)
                verify_allocation_hardware_descriptor(
                    results, allocation_hardware, freeze_check
                )
                command = runner_command(args, assignment, attempt_jsonl, attempt_output, base)
                write_json(
                    active_marker,
                    {
                        "schema_version": ACTIVE_RUN_MARKER_SCHEMA_VERSION,
                        "kind": "highambench-active-hosted-attempt",
                        "assignment": _planned_assignment_record_identity(assignment),
                        "attempt": attempt,
                        "attempt_output": (
                            f"attempts/{assignment['run_id']}.attempt-{attempt}.json"
                        ),
                        "started_at_unix": time.time(),
                        "allocation_hardware": _json_copy(allocation_hardware),
                    },
                )
                completed = subprocess.run(command, cwd=args.project_root.resolve(), check=False)
                if not attempt_output.is_file():
                    raise BenchmarkToolError(
                        f"runner produced no record for {assignment['run_id']} (exit {completed.returncode})"
                    )
                raw_selected = read_json(attempt_output)
                if not isinstance(raw_selected, dict):
                    raise BenchmarkToolError(
                        f"runner record for {assignment['run_id']} is not a JSON object"
                    )
                selected = raw_selected
                if selected.get("run_id") != assignment["run_id"]:
                    raise BenchmarkToolError(
                        f"runner returned run_id {selected.get('run_id')!r}; "
                        f"expected {assignment['run_id']!r}"
                    )
                _bind_allocation_hardware(selected, allocation_hardware)
                _bind_matrix_attempt(selected, attempt)
                # The runner cannot know the authenticated allocation descriptor
                # until run_matrix verifies the on-disk record.  Rewrite its
                # normalized attempt output before deriving any incident or final.
                write_json(attempt_output, selected)
                if _useful_work_attempt_requires_abort(selected):
                    incident_path = _preserve_matrix_incident(
                        selected,
                        incidents,
                        results_root=results,
                        assignment=assignment,
                        attempt=attempt,
                        attempt_output=attempt_output,
                        attempt_jsonl=attempt_jsonl,
                        status="aborted_after_unscorable_useful_work",
                        retry_allowed=False,
                        freeze_check=freeze_check,
                    )
                    _rebuild_jsonl(
                        records,
                        incidents,
                        assignments,
                        results / "runs.jsonl",
                        results_root=results,
                        freeze_check=freeze_check,
                    )
                    raise BenchmarkToolError(
                        "Ultra attempt produced useful work without either an "
                        "authenticated exact pass boundary or an exact natural "
                        "failure drain; the matrix aborted without scoring or retrying "
                        f"{assignment['run_id']!r}. The active-run marker and incident "
                        f"record {incident_path} were retained for audit."
                    )
                startup_system_error = (
                    selected.get("failure_code") == "SYSTEM_ERROR"
                    and selected.get("useful_work_started") is False
                )
                if not startup_system_error or attempt == 2:
                    if not startup_system_error:
                        break
                    incident_path = _preserve_matrix_incident(
                        selected,
                        incidents,
                        results_root=results,
                        assignment=assignment,
                        attempt=attempt,
                        attempt_output=attempt_output,
                        attempt_jsonl=attempt_jsonl,
                        status="terminal_pre_prompt_system_error",
                        retry_allowed=False,
                        freeze_check=freeze_check,
                    )
                    _rebuild_jsonl(
                        records,
                        incidents,
                        assignments,
                        results / "runs.jsonl",
                        results_root=results,
                        freeze_check=freeze_check,
                    )
                    raise BenchmarkToolError(
                        "the one permitted startup SYSTEM_ERROR retry also failed before "
                        "useful work; both incidents were preserved and no final record "
                        f"was manufactured for {assignment['run_id']!r}. The active-run "
                        "marker was retained to prevent any further automatic retry."
                    )
                _preserve_matrix_incident(
                    selected,
                    incidents,
                    results_root=results,
                    assignment=assignment,
                    attempt=attempt,
                    attempt_output=attempt_output,
                    attempt_jsonl=attempt_jsonl,
                    status="retryable_pre_prompt_system_error",
                    retry_allowed=True,
                    freeze_check=freeze_check,
                )
            assert selected is not None
            _bind_matrix_record_sha256(selected)
            _authenticate_final_assignment_record_payload(
                results, selected, assignment, freeze_check
            )
            # The sealed attempt output and final record are byte-equivalent JSON
            # documents.  An interrupted marker can therefore bind them exactly.
            write_json(attempt_output, selected)
            write_json(final_record, selected)
            active_marker.unlink(missing_ok=True)
            _rebuild_jsonl(
                records,
                incidents,
                assignments,
                results / "runs.jsonl",
                results_root=results,
                freeze_check=freeze_check,
            )
    _rebuild_jsonl(
        records,
        incidents,
        assignments,
        results / "runs.jsonl",
        results_root=results,
        freeze_check=freeze_check,
    )
    complete = len(
        _authenticate_existing_final_records(
            results, records, assignments, freeze_check
        )
    )
    if stopped_for_allocation_deadline is not None:
        print(
            "HighamBench chunk stopped cleanly before the allocation deadline: "
            f"{complete}/{len(assignments)} assignments complete; next "
            f"{stopped_for_allocation_deadline['next_run_id']}"
        )
        return CHUNK_INCOMPLETE_EXIT_CODE
    if stopped_after_requested_paper is not None:
        print(
            "HighamBench chunk stopped after requested paper "
            f"{stop_after_paper}: {complete}/{len(assignments)} assignments complete; "
            f"next {stopped_after_requested_paper['next_run_id']}"
        )
        return CHUNK_INCOMPLETE_EXIT_CODE
    if only_pair_id is not None:
        if complete != 2:
            raise BenchmarkToolError(
                f"atomic pair {only_pair_id!r} ended without exactly two final records"
            )
        commit = create_or_verify_pair_commit(results, assignments, freeze_check)
        _write_pair_complete_status(results, str(only_pair_id), commit)
        print(f"HighamBench pair complete: {only_pair_id} (2/2 assignments)")
        return 0
    write_json(
        results / "last_chunk_status.json",
        {
            "schema_version": 1,
            "kind": "highambench-matrix-chunk-status",
            "status": "matrix_complete",
            "completed_runs": complete,
            "planned_runs": len(assignments),
        },
    )
    print(f"HighamBench assignments complete: {complete}/{len(assignments)}")
    return 0 if complete == len(assignments) else 1


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    here = Path(__file__).resolve().parents[1]
    parser.add_argument("--benchmark-root", type=Path, default=here)
    parser.add_argument("--project-root", type=Path, required=True)
    parser.add_argument("--results-root", type=Path, required=True)
    parser.add_argument("--codex", type=Path, required=True)
    parser.add_argument("--auth-file", type=Path, required=True)
    parser.add_argument("--offline-shell", type=Path, required=True)
    parser.add_argument("--toolchain-root", type=Path, required=True)
    parser.add_argument("--packages-root", type=Path, required=True)
    parser.add_argument("--packages-runtime-root", type=Path, required=True)
    parser.add_argument("--shared-olean-root", type=Path, required=True)
    parser.add_argument("--library-source", type=Path, required=True)
    parser.add_argument("--library-root-file", type=Path, required=True)
    parser.add_argument("--library-olean", type=Path, required=True)
    parser.add_argument("--release-manifest", type=Path)
    parser.add_argument("--agent-id", help="optional assertion; metadata supplies the value")
    parser.add_argument("--agent-version", help="optional assertion; metadata and the binary supply it")
    parser.add_argument("--model", help="optional assertion; metadata supplies the value")
    parser.add_argument("--reasoning-effort", help="optional assertion; metadata supplies the value")
    parser.add_argument("--time-limit-seconds", type=int, help="optional assertion; metadata supplies it")
    parser.add_argument("--token-limit", type=int, help="optional assertion; metadata supplies it")
    parser.add_argument(
        "--prompt-startup-timeout-seconds",
        type=float,
        help=(
            "optional assertion; frozen config/environment supply the trusted "
            "pre-prompt handshake timeout (exactly 120 seconds)"
        ),
    )
    parser.add_argument(
        "--post-submission-validation-reserve-seconds",
        type=float,
        help=(
            "optional assertion; frozen config/environment supply the complete "
            "serial hidden-validation and process-closure reserve (exactly 369 seconds)"
        ),
    )
    parser.add_argument(
        "--allocation-end-epoch",
        type=int,
        help=(
            "UNIX timestamp at which the enclosing allocation ends; when omitted, "
            f"{SLURM_JOB_END_TIME_ENV} is used automatically when available"
        ),
    )
    parser.add_argument(
        "--allocation-guard-seconds",
        type=float,
        default=DEFAULT_ALLOCATION_GUARD_SECONDS,
        help=(
            "extra time reserved after the worst-case remaining runs in the current "
            "N/L pair before a new hosted attempt may start (default: 600)"
        ),
    )
    parser.add_argument(
        "--stop-after-paper",
        metavar="PAPER_ID",
        help=(
            "stop cleanly with exit 75 after every assignment through this paper "
            "has a final record, before starting the next paper"
        ),
    )
    parser.add_argument(
        "--only-pair-id",
        metavar="PAIR_ID",
        help=(
            "run exactly one canonical N/L pair as an atomic pair root; a complete "
            "pair writes pair_commit.json and no half pair may move allocations"
        ),
    )
    parser.add_argument(
        "--agent-network-verified",
        action="store_true",
        help="claim the agent shell no-socket diagnostic was completed",
    )
    parser.add_argument(
        "--token-control-verified",
        action="store_true",
        help=(
            "legacy assertion flag; the matrix independently verifies its frozen "
            "live app-server token control and advisory rollout-budget metadata"
        ),
    )
    parser.add_argument("--force", action="store_true")
    return parser


def main() -> int:
    try:
        args = make_parser().parse_args()
        return run(args)
    except (OSError, BenchmarkToolError, ValueError) as error:
        print(f"run-matrix error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
