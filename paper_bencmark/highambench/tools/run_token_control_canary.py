#!/usr/bin/env python3
"""Run or verify the private synthetic Ultra token-control canary.

The probe is deliberately not a benchmark assignment.  It stages only three
synthetic inputs and releases one deterministic inert prompt whose first provider
response must finish below a fixed 180,000-token cap.  The trusted adapter then
requests remote compaction; that second provider response must be the sole
crossing and may expose only one inert Compaction frame before its sanitized
completion.
Benchmark task,
context, target, common-prompt, condition-supplement, and shared-source bytes
are audited for non-identity/non-embedding and are never passed to the model.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import subprocess
import sys
from typing import Any, Mapping, Sequence

try:
    from .common import BenchmarkToolError, read_json, sha256_file, write_json
    from .hashes import create_manifest, load_manifest, verify_manifest
    from . import codex_isolated, run_matrix, runner
except ImportError:  # Direct script execution.
    from common import BenchmarkToolError, read_json, sha256_file, write_json  # type: ignore
    from hashes import create_manifest, load_manifest, verify_manifest  # type: ignore
    import codex_isolated  # type: ignore
    import run_matrix  # type: ignore
    import runner  # type: ignore


CANARY_ID = "TOKEN-CONTROL-SYNTHETIC-PROVIDER-GATE-V8"
CANARY_TASK_ID = CANARY_ID  # Compatibility alias used by older callers.
CANARY_RUN_ID = CANARY_ID
CANARY_CONDITION = "N"
PROMPT_PROTOCOL = "synthetic-inert-sanitized-provider-gate-compaction-crossing-v8"
EVIDENCE_KIND = "highambench-live-token-control-canary"
EVIDENCE_SCHEMA_VERSION = 3
FROZEN_EVIDENCE_PATH = (
    "paper_bencmark/highambench/metadata/evidence/token_control_live_canary.json"
)
DEFAULT_CANARY_TOKEN_LIMIT = 180_000
DEFAULT_CANARY_TIME_LIMIT_SECONDS = 300
PROMPT_STARTUP_TIMEOUT_SECONDS = 120.0
PROMPT_RELEASE_PROTOCOL_VERSION = "highambench-prompt-release-v1"
PROMPT_RELEASE_SCHEMA_VERSION = 1
PROMPT_GO_MINIMUM_RELEASE_WINDOW_SECONDS = 5.0
PROMPT_RELEASE_ADAPTER_NAME = "codex_isolated.py"
PROMPT_RELEASE_ADAPTER_VERSION = "1"
APP_SERVER_CLIENT_NAME = "highambench-isolated"
APP_SERVER_CLIENT_VERSION = "1"
TURN_START_REQUEST_ID = 3
INERT_RECORD_COUNT = 3_072
DIRECT_FINAL_ANSWER = "HIGHAMBENCH_SYNTHETIC_TOKEN_CONTROL_OK"
ACCOUNTING_PROJECTION_SCHEMA_VERSION = runner.ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION
TOKEN_USAGE_SOURCE = codex_isolated.ULTRA_USAGE_MEASUREMENT_SOURCE
TOKEN_NOTIFICATION = codex_isolated.ULTRA_USAGE_NOTIFICATION
TOKEN_USAGE_SCOPE = codex_isolated.ULTRA_USAGE_SCOPE
TOKEN_MEASUREMENT_SOURCE = runner.ULTRA_TOKEN_MEASUREMENT_SOURCE
TOKEN_ENFORCEMENT_MODE = runner.ULTRA_TOKEN_LIMIT_ENFORCEMENT_MODE
SPAWN_BINDING_SOURCE = "raw_function_call.call_id=subAgentActivity.id"

SYNTHETIC_COMMON_PROMPT = f"""# Private synthetic token-control probe

This is an unscored infrastructure probe, not a benchmark task.

Use no tools. Do not call functions, shell commands, subagents, or dynamic
tools. Do not read or modify any file. Ignore the inert records in the context;
they carry no task or instructions. Return exactly `{DIRECT_FINAL_ANSWER}` as
one direct final answer and do nothing else.
"""


def _make_inert_context() -> str:
    records = []
    for index in range(INERT_RECORD_COUNT):
        digest = hashlib.sha256(
            f"{PROMPT_PROTOCOL}:inert-record:{index:06d}".encode("ascii")
        ).hexdigest()
        records.append(f"INERT-CANARY-RECORD-{index:06d}-{digest}")
    return (
        "The records below are deterministic inert padding. They are not a "
        "mathematical task and must not be interpreted or transformed.\n\n"
        + "\n".join(records)
        + "\n\nEND INERT PADDING. Use no tools and return only "
        + DIRECT_FINAL_ANSWER
        + ".\n"
    )


SYNTHETIC_CONTEXT = _make_inert_context()
SYNTHETIC_TARGET = """-- Synthetic infrastructure target; it is not a benchmark theorem.
theorem highamBenchSyntheticTokenControl : True := by
  -- PROOF_START
  trivial
"""
SYNTHETIC_TARGET_THEOREM = "highamBenchSyntheticTokenControl"
SYNTHETIC_UNUSED_L_SUPPLEMENT = (
    "# Synthetic token-control L supplement\n\n"
    "This deterministic descriptor exists only to complete the signposted-library-v1 "
    "schema. Condition N receives none of these bytes.\n"
)

_TOKEN_FIELDS = (
    "input_tokens",
    "cached_input_tokens",
    "cache_write_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
    "total_tokens",
)
_REPLAY_FIELDS = (
    "schema_version",
    "accounting_projection_schema_version",
    "measurement_source",
    "notification",
    "usage_scope",
    "live_cumulative",
    "input_includes_cached",
    "root_thread_id",
    "root_turn_id",
    "thread_count",
    "response_count",
    *_TOKEN_FIELDS,
    "notification_sequence",
    "stop_reason",
    "interrupt_requested",
    "pending_interrupt_response_count",
    "active_thread_ids",
    "unresolved_thread_ids",
    "drain_complete",
    "measurement_exact",
    "invalid_reasons",
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
    "fork_policy_complete",
    "fork_policy",
    "spawn_linkage_complete",
    "descendant_accounting_complete",
    "cumulative_projection_complete",
    "accounting_complete",
    "threads",
    "response_ids",
)
ARTIFACT_LABELS = (
    "record",
    "agent_log",
    "usage",
    "raw_jsonl",
    "common_prompt",
    "context",
    "synthetic_target",
    "controlled_manifest",
    "benchmark_source_audit",
    "synthetic_prompt_provenance",
    "freeze_check",
    "runner_freeze_check",
    "invocation",
    "provider_gate",
)


def _mapping(value: Any, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise BenchmarkToolError(f"{label} must be a JSON object")
    return value


def _nonnegative_int(value: Any, label: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise BenchmarkToolError(f"synthetic token canary has invalid {label}")
    return value


def _positive_int(value: Any, label: str) -> int:
    result = _nonnegative_int(value, label)
    if result == 0:
        raise BenchmarkToolError(f"synthetic token canary has nonpositive {label}")
    return result


def _canonical_sha256(value: Mapping[str, Any] | list[Any]) -> str:
    payload = json.dumps(
        value, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _text_sha256(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def _self_hashed(value: Mapping[str, Any], field: str = "record_sha256") -> dict[str, Any]:
    result = dict(value)
    result[field] = _canonical_sha256(result)
    return result


def _verify_self_hash(value: Mapping[str, Any], field: str, label: str) -> None:
    digest = value.get(field)
    if not isinstance(digest, str) or len(digest) != 64:
        raise BenchmarkToolError(f"{label} has no self hash")
    canonical = dict(value)
    canonical.pop(field, None)
    if _canonical_sha256(canonical) != digest:
        raise BenchmarkToolError(f"{label} self hash is invalid")


def _relative_artifact(path: Path, root: Path) -> str:
    try:
        return path.resolve().relative_to(root.resolve()).as_posix()
    except ValueError as error:
        raise BenchmarkToolError(
            f"synthetic token-canary artifact is outside its root: {path}"
        ) from error


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


def _source_descriptor(path: str, text: str) -> dict[str, Any]:
    payload = text.encode("utf-8")
    return {
        "path": path,
        "sha256": hashlib.sha256(payload).hexdigest(),
        "bytes": len(payload),
    }


def synthetic_signposted_prompt_protocol() -> dict[str, Any]:
    """Return the production-compatible protocol over synthetic inputs only."""

    return {
        "version": runner.SIGNPOSTED_PROMPT_PROTOCOL_VERSION,
        "composition_order": list(runner.SIGNPOSTED_PROMPT_COMPOSITION_ORDER),
        "common_prompt": _source_descriptor("prompt.md", SYNTHETIC_COMMON_PROMPT),
        "condition_supplements": {
            "L": _source_descriptor(
                "synthetic_unused_condition_L.md", SYNTHETIC_UNUSED_L_SUPPLEMENT
            )
        },
        "N_receives_condition_supplement": False,
        "relevant_theorem_or_module_hints_supplied": False,
    }


def synthetic_prompt_provenance_record() -> dict[str, Any]:
    effective = synthetic_effective_prompt().encode("utf-8")
    return {
        "protocol_version": runner.SIGNPOSTED_PROMPT_PROTOCOL_VERSION,
        "condition": "N",
        "composition_order": list(runner.SIGNPOSTED_PROMPT_COMPOSITION_ORDER),
        "common_prompt": _source_descriptor("prompt.md", SYNTHETIC_COMMON_PROMPT),
        "condition_supplement": None,
        "task_context": _source_descriptor("context.md", SYNTHETIC_CONTEXT),
        "fixed_target": _source_descriptor("SyntheticTarget.lean", SYNTHETIC_TARGET),
        "effective_prompt": {
            "sha256": hashlib.sha256(effective).hexdigest(),
            "bytes": len(effective),
            "encoding": "utf-8",
            "composition": runner.EFFECTIVE_PROMPT_COMPOSITION,
        },
        "authentication": {
            "computed_before_prompt_release": True,
            "frozen_protocol_match": True,
            "controlled_task_sources_match": True,
            "agent_command_match": True,
        },
    }


def prompt_record() -> dict[str, Any]:
    context_bytes = SYNTHETIC_CONTEXT.encode("utf-8")
    effective = synthetic_effective_prompt().encode("utf-8")
    return {
        "protocol": PROMPT_PROTOCOL,
        "composition": (
            "common_prompt_then_task_context_then_synthetic_target_via_"
            "codex_isolated_build_prompt"
        ),
        "common_prompt_sha256": _text_sha256(SYNTHETIC_COMMON_PROMPT),
        "common_prompt_bytes": len(SYNTHETIC_COMMON_PROMPT.encode("utf-8")),
        "context_sha256": hashlib.sha256(context_bytes).hexdigest(),
        "context_bytes": len(context_bytes),
        "synthetic_target_sha256": _text_sha256(SYNTHETIC_TARGET),
        "synthetic_target_bytes": len(SYNTHETIC_TARGET.encode("utf-8")),
        "effective_prompt_sha256": hashlib.sha256(effective).hexdigest(),
        "effective_prompt_bytes": len(effective),
        "inert_record_count": INERT_RECORD_COUNT,
        "inert_payload_bytes": len(context_bytes),
        "inert_payload_bytes_at_least_250000": len(context_bytes) >= 250_000,
        "direct_final_answer": DIRECT_FINAL_ANSWER,
        "no_tools_instruction": True,
        "one_direct_final_answer_instruction": True,
        "benchmark_task_bytes_used": False,
    }


def _attestation_agent(freeze_check: Mapping[str, Any]) -> dict[str, Any]:
    agent = dict(_mapping(freeze_check.get("agent"), "canary freeze-check agent"))
    agent["ultra_orchestration"] = run_matrix.ultra_orchestration_record()
    return agent


def _role_for_benchmark_source(relative: str) -> str:
    if relative.endswith("/agent_prompt.md"):
        return "agent_prompt"
    if "/condition_prompts/" in relative:
        return "condition_prompt"
    if "/tasks/" in relative and relative.endswith("/Target.lean"):
        return "task_target"
    if "/tasks/" in relative and relative.endswith("/context.md"):
        return "task_context"
    if "/tasks/" in relative and relative.endswith("/task.json"):
        return "task_metadata"
    if "/shared/" in relative:
        return "shared_source"
    return "controlled_task_source"


def _benchmark_source_paths(
    project_root: Path, benchmark_root: Path, manifest: Mapping[str, Any]
) -> list[Path]:
    project = project_root.resolve()
    benchmark = benchmark_root.resolve()
    candidates: set[Path] = {benchmark / "agent_prompt.md"}
    condition_root = benchmark / "condition_prompts"
    if condition_root.is_dir():
        candidates.update(path for path in condition_root.rglob("*") if path.is_file())
    tasks_root = benchmark / "tasks"
    if not tasks_root.is_dir():
        raise BenchmarkToolError("benchmark task tree is missing")
    candidates.update(path for path in tasks_root.rglob("*") if path.is_file())
    shared = manifest.get("controlled_shared_files")
    if not isinstance(shared, list):
        raise BenchmarkToolError("benchmark manifest has no controlled shared files")
    for entry in shared:
        item = _mapping(entry, "controlled shared-file entry")
        relative = item.get("path")
        if not isinstance(relative, str) or not relative:
            raise BenchmarkToolError("controlled shared-file path is invalid")
        candidates.add((project / relative).resolve())
    result: list[Path] = []
    for path in sorted(candidates):
        resolved = path.resolve()
        try:
            resolved.relative_to(project)
        except ValueError as error:
            raise BenchmarkToolError(
                f"benchmark controlled source escapes project: {path}"
            ) from error
        if path.is_symlink() or not resolved.is_file():
            raise BenchmarkToolError(
                f"benchmark controlled source is missing or a symlink: {path}"
            )
        result.append(resolved)
    return result


def audit_benchmark_source_separation(
    *,
    project_root: Path,
    benchmark_root: Path,
    manifest: Mapping[str, Any],
    generated_sources: Mapping[str, bytes],
) -> dict[str, Any]:
    """Prove that no complete benchmark controlled source is a canary input."""

    required_generated = {"common_prompt", "context", "synthetic_target", "effective_prompt"}
    if set(generated_sources) != required_generated or any(
        not isinstance(payload, bytes) or not payload
        for payload in generated_sources.values()
    ):
        raise BenchmarkToolError("synthetic canary generated-source set is invalid")
    project = project_root.resolve()
    paths = _benchmark_source_paths(project, benchmark_root, manifest)
    catalog: list[dict[str, Any]] = []
    exact_sha_matches: list[dict[str, str]] = []
    exact_byte_matches: list[dict[str, str]] = []
    embedded_matches: list[dict[str, str]] = []
    generated_hashes = {
        label: {
            "sha256": hashlib.sha256(payload).hexdigest(),
            "bytes": len(payload),
        }
        for label, payload in sorted(generated_sources.items())
    }
    for path in paths:
        relative = path.relative_to(project).as_posix()
        payload = path.read_bytes()
        if not payload:
            raise BenchmarkToolError(
                f"benchmark controlled source is unexpectedly empty: {relative}"
            )
        digest = hashlib.sha256(payload).hexdigest()
        role = _role_for_benchmark_source("/" + relative)
        catalog.append(
            {"path": relative, "role": role, "sha256": digest, "bytes": len(payload)}
        )
        for label, generated in generated_sources.items():
            if digest == generated_hashes[label]["sha256"]:
                exact_sha_matches.append({"benchmark_path": relative, "generated": label})
            if payload == generated:
                exact_byte_matches.append({"benchmark_path": relative, "generated": label})
            if payload in generated:
                embedded_matches.append({"benchmark_path": relative, "generated": label})
    if exact_sha_matches or exact_byte_matches or embedded_matches:
        detail = exact_byte_matches or embedded_matches or exact_sha_matches
        raise BenchmarkToolError(
            "synthetic canary input contains or equals benchmark controlled bytes: "
            + json.dumps(detail, sort_keys=True)
        )
    roles: dict[str, int] = {}
    for item in catalog:
        roles[item["role"]] = roles.get(item["role"], 0) + 1
    p01_p02 = [
        item
        for item in catalog
        if "/tasks/P01/" in "/" + item["path"]
        or "/tasks/P02/" in "/" + item["path"]
        or item["path"].endswith("/P01Definitions.lean")
        or item["path"].endswith("/P02Definitions.lean")
    ]
    base = {
        "schema_version": 1,
        "kind": "highambench-synthetic-token-canary-source-separation",
        "benchmark_manifest_sha256": _canonical_sha256(dict(manifest)),
        "benchmark_source_catalog_sha256": _canonical_sha256(catalog),
        "benchmark_source_count": len(catalog),
        "benchmark_source_role_counts": dict(sorted(roles.items())),
        "p01_p02_source_count": len(p01_p02),
        "generated_sources": generated_hashes,
        "comparison": "whole-file SHA-256, exact-byte identity, and whole-source embedding",
        "exact_sha256_match_count": 0,
        "exact_byte_identity_match_count": 0,
        "embedded_benchmark_source_count": 0,
        "benchmark_task_bytes_used": False,
        "condition": "N",
        "condition_supplement_used": False,
        "library_or_library_path_used": False,
        "catalog": catalog,
    }
    return _self_hashed(base, "audit_sha256")


def _json_messages(path: Path) -> list[dict[str, Any]]:
    messages: list[dict[str, Any]] = []
    try:
        lines = path.read_text(encoding="utf-8").splitlines()
    except OSError as error:
        raise BenchmarkToolError(f"cannot read synthetic canary agent log: {error}") from error
    for line in lines:
        try:
            value = json.loads(line)
        except json.JSONDecodeError:
            continue
        if isinstance(value, dict):
            messages.append(value)
    return messages


def _audit_sanitized_crossing(
    messages: Sequence[Mapping[str, Any]],
    root: str,
    root_turn: str,
    *,
    below_response_id: str,
    crossing_response_id: str,
    compaction_turn_id: str,
) -> dict[str, Any]:
    """Authenticate the pinned turn-then-compaction notification sequence."""

    disallowed_item_types = {
        "commandExecution",
        "fileChange",
        "mcpToolCall",
        "collabAgentToolCall",
        "subAgentActivity",
        "dynamicToolCall",
        "webSearch",
        "imageView",
    }
    assistant_messages: list[tuple[int, str]] = []
    compaction_started: list[int] = []
    compaction_completed: list[int] = []
    compact_rpc_indices: list[int] = []
    raw_responses: list[tuple[int, str, str]] = []
    completed_turns: list[tuple[int, str]] = []
    for index, message in enumerate(messages):
        method = message.get("method")
        params = message.get("params")
        if method == "item/tool/call":
            raise BenchmarkToolError("synthetic token canary made a dynamic tool call")
        if method in ("item/started", "item/completed") and isinstance(params, Mapping):
            item = params.get("item")
            if isinstance(item, Mapping) and item.get("type") in disallowed_item_types:
                raise BenchmarkToolError("synthetic token canary used a forbidden tool item")
            if (
                method == "item/completed"
                and params.get("threadId") == root
                and params.get("turnId") == root_turn
                and isinstance(item, Mapping)
                and item.get("type") == "agentMessage"
            ):
                text = item.get("text")
                if not isinstance(text, str):
                    raise BenchmarkToolError("synthetic token canary final message is malformed")
                assistant_messages.append((index, text.strip()))
            if isinstance(item, Mapping) and item.get("type") == "contextCompaction":
                if (
                    params.get("threadId") != root
                    or params.get("turnId") != compaction_turn_id
                ):
                    raise BenchmarkToolError(
                        "synthetic token canary compaction item is not root-owned"
                    )
                (
                    compaction_started
                    if method == "item/started"
                    else compaction_completed
                ).append(index)
        if method == "rawResponseItem/completed" and isinstance(params, Mapping):
            item = params.get("item")
            if not isinstance(item, Mapping) or item.get("type") not in {
                "message",
                "agent_message",
                "reasoning",
                "compaction",
            }:
                raise BenchmarkToolError("synthetic token canary raw response contains a tool call")
            if item.get("type") == "compaction":
                raise BenchmarkToolError(
                    "pinned app-server unexpectedly exposed a raw compaction item"
                )
        if method == TOKEN_NOTIFICATION and isinstance(params, Mapping):
            if params.get("threadId") != root:
                raise BenchmarkToolError("synthetic token canary raw response is not root-owned")
            response_id = params.get("responseId")
            response_turn = params.get("turnId")
            if (
                not isinstance(response_id, str)
                or not response_id
                or not isinstance(response_turn, str)
                or not response_turn
            ):
                raise BenchmarkToolError("synthetic token canary raw response lacks an id")
            raw_responses.append((index, response_id, response_turn))
        elif method == "turn/completed" and isinstance(params, Mapping):
            terminal = params.get("turn")
            if (
                params.get("threadId") == root
                and isinstance(terminal, Mapping)
                and terminal.get("id") in {root_turn, compaction_turn_id}
                and terminal.get("status") == "completed"
            ):
                completed_turns.append((index, str(terminal["id"])))
        if (
            message.get("id") == codex_isolated.THREAD_COMPACT_REQUEST_ID
            and "method" not in message
        ):
            if message.get("result") != {} or "error" in message:
                raise BenchmarkToolError(
                    "synthetic token canary compact RPC result is not exact"
                )
            compact_rpc_indices.append(index)
    if len(assistant_messages) != 1 or assistant_messages[0][1] != DIRECT_FINAL_ANSWER:
        raise BenchmarkToolError(
            "synthetic token canary first turn did not release its one inert answer"
        )
    if (
        [(response_id, turn_id) for _index, response_id, turn_id in raw_responses]
        != [
            (below_response_id, root_turn),
            (crossing_response_id, compaction_turn_id),
        ]
        or not completed_turns
        or completed_turns[0][1] != root_turn
        or len(completed_turns) > 2
        or (
            len(completed_turns) == 2
            and completed_turns[1][1] != compaction_turn_id
        )
        or len(compaction_started) != 1
        or len(compact_rpc_indices) != 1
    ):
        raise BenchmarkToolError(
            "synthetic token canary compaction lifecycle is not exact"
        )
    first_raw_index, crossing_raw_index = (item[0] for item in raw_responses)
    first_turn_completed = completed_turns[0][0]
    compaction_turn_completed = (
        completed_turns[1][0] if len(completed_turns) == 2 else None
    )
    if not (
        assistant_messages[0][0]
        < first_raw_index
        < first_turn_completed
        and first_turn_completed < compaction_started[0] < crossing_raw_index
        and first_turn_completed < compact_rpc_indices[0] < crossing_raw_index
    ):
        raise BenchmarkToolError(
            "synthetic token canary compaction event order changed"
        )
    if (
        len(compaction_completed) > 1
        or (compaction_completed and compaction_completed[0] <= crossing_raw_index)
        or (
            compaction_turn_completed is not None
            and compaction_turn_completed <= crossing_raw_index
        )
    ):
        raise BenchmarkToolError(
            "synthetic token canary post-crossing compaction lifecycle changed"
        )
    started_compaction = _mapping(
        _mapping(
            messages[compaction_started[0]].get("params"),
            "synthetic token canary compaction-start params",
        ).get("item"),
        "synthetic token canary compaction-start item",
    )
    compaction_item_id = started_compaction.get("id")
    if not isinstance(compaction_item_id, str) or not compaction_item_id:
        raise BenchmarkToolError("synthetic token canary compaction item lacks an id")
    compaction_item_finished = False
    compaction_turn_finished = False
    status_count = 0
    token_usage_notice_count = 0
    rate_limit_notice_count = 0
    for index in range(crossing_raw_index + 1, len(messages)):
        message = messages[index]
        method = message.get("method")
        params = message.get("params")
        if method == "thread/tokenUsage/updated" and isinstance(params, Mapping):
            if (
                token_usage_notice_count != 0
                or params.get("threadId") != root
                or params.get("turnId") != compaction_turn_id
                or not isinstance(params.get("tokenUsage"), Mapping)
            ):
                raise BenchmarkToolError(
                    "synthetic token canary has post-crossing model activity"
                )
            token_usage_notice_count = 1
            continue
        if method == "account/rateLimits/updated" and isinstance(params, Mapping):
            if (
                rate_limit_notice_count != 0
                or set(params) != {"rateLimits"}
                or not isinstance(params.get("rateLimits"), Mapping)
            ):
                raise BenchmarkToolError(
                    "synthetic token canary has post-crossing model activity"
                )
            rate_limit_notice_count = 1
            continue
        if method == "item/completed" and isinstance(params, Mapping):
            item = params.get("item")
            if (
                compaction_item_finished
                or compaction_turn_finished
                or status_count != 0
                or params.get("threadId") != root
                or params.get("turnId") != compaction_turn_id
                or not isinstance(item, Mapping)
                or item.get("type") != "contextCompaction"
                or item.get("id") != compaction_item_id
            ):
                raise BenchmarkToolError(
                    "synthetic token canary has post-crossing model activity"
                )
            compaction_item_finished = True
            continue
        if method == "turn/completed" and isinstance(params, Mapping):
            turn_record = params.get("turn")
            if (
                compaction_turn_finished
                or params.get("threadId") != root
                or not isinstance(turn_record, Mapping)
                or turn_record.get("id") != compaction_turn_id
                or turn_record.get("status") != "completed"
            ):
                raise BenchmarkToolError(
                    "synthetic token canary has post-crossing model activity"
                )
            compaction_turn_finished = True
            continue
        if method == "thread/status/changed" and isinstance(params, Mapping):
            status = params.get("status")
            if (
                status_count != 0
                or params.get("threadId") != root
                or not isinstance(status, Mapping)
                or status.get("type") not in {"idle", "shutdown"}
            ):
                raise BenchmarkToolError(
                    "synthetic token canary has post-crossing model activity"
                )
            status_count = 1
            continue
        raise BenchmarkToolError(
            "synthetic token canary has post-crossing model activity"
        )
    return {
        "below_cap_raw_response_completed_index": first_raw_index,
        "crossing_raw_response_completed_index": crossing_raw_index,
        "compaction_turn_completed_index": compaction_turn_completed,
        "observed_order": (
            "below_cap_direct_final_then_compaction_item_then_crossing_"
            "rawResponse_completed_then_no_model_activity"
        ),
        "crossing_response_id": crossing_response_id,
        "provider_answer_content_released": False,
        "sanitized_compaction_completion_required": True,
        "compaction_item_count": 1,
        "tool_call_count": 0,
    }


def validate_usage_and_log(
    usage: Mapping[str, Any],
    agent_log: Path,
    *,
    token_limit: int,
    gate_authentication: Mapping[str, Any],
) -> dict[str, Any]:
    root = usage.get("root_thread_id")
    turn = usage.get("root_turn_id")
    if not isinstance(root, str) or not root or not isinstance(turn, str) or not turn:
        raise BenchmarkToolError("synthetic token canary lacks a root thread/turn")
    crossing = _mapping(usage.get("first_crossing"), "synthetic canary first crossing")
    gate_record = _mapping(
        gate_authentication.get("record"), "synthetic provider-gate record"
    )
    gate_state = _mapping(gate_record.get("state"), "synthetic provider-gate state")
    gate_crossing = _mapping(
        gate_state.get("crossing"), "synthetic provider-gate crossing"
    )
    gate_derived = _mapping(
        gate_authentication.get("derived"), "synthetic provider-gate derivation"
    )
    calls = gate_record.get("calls")
    if not isinstance(calls, list) or len(calls) != 2:
        raise BenchmarkToolError(
            "synthetic provider gate did not retain turn then compaction calls"
        )
    below_call = _mapping(calls[0], "synthetic below-cap provider-gate call")
    sole_call = _mapping(calls[1], "synthetic compaction provider-gate call")
    below_metadata = _mapping(
        below_call.get("request_metadata"),
        "synthetic below-cap provider-gate request metadata",
    )
    request_metadata = _mapping(
        sole_call.get("request_metadata"), "synthetic provider-gate request metadata"
    )
    sanitized_events = sole_call.get("released_sanitized_events")
    compaction_event = (
        sanitized_events[0]
        if isinstance(sanitized_events, list) and len(sanitized_events) == 2
        else None
    )
    compaction_item = (
        compaction_event.get("item")
        if isinstance(compaction_event, Mapping)
        else None
    )
    if (
        gate_authentication.get("authenticated") is not True
        or gate_state.get("phase") != "CLOSED"
        or gate_state.get("close_reason") != "token_limit"
        or gate_record.get("setup_requests") != []
        or below_metadata.get("request_kind") != "turn"
        or below_call.get("crossed_cap") is not False
        or below_call.get("release_kind") != "byte_identity"
        or below_call.get("released_body_sha256")
        != below_call.get("upstream_body_sha256")
        or below_call.get("released_body_bytes")
        != below_call.get("upstream_body_bytes")
        or below_call.get("client_release_complete") is not True
        or sole_call.get("crossed_cap") is not True
        or gate_crossing.get("sole_inflight") is not True
        or gate_crossing.get("request_kind") != "compaction"
        or request_metadata.get("request_kind") != "compaction"
        or gate_crossing.get("release_kind")
        != runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE
        or sole_call.get("release_kind")
        != runner.PROVIDER_GATE_COMPACTION_CROSSING_RELEASE
        or sole_call.get("released_sanitized_event") is None
        or not isinstance(sanitized_events, list)
        or len(sanitized_events) != 2
        or not isinstance(compaction_event, Mapping)
        or set(compaction_event) != {"type", "item"}
        or compaction_event.get("type") != "response.output_item.done"
        or not isinstance(compaction_item, Mapping)
        or set(compaction_item) != {"type", "encrypted_content"}
        or compaction_item.get("type") != "compaction"
        or not isinstance(compaction_item.get("encrypted_content"), str)
        or not compaction_item.get("encrypted_content")
        or sole_call.get("response_id") != crossing.get("response_id")
        or gate_crossing.get("response_id") != crossing.get("response_id")
        or gate_crossing.get("completed_tokens") != crossing.get("tokens")
        or sole_call.get("previous_total") != below_call.get("committed_total")
        or sole_call.get("committed_total") != crossing.get("tokens")
        or not isinstance(below_call.get("committed_total"), int)
        or isinstance(below_call.get("committed_total"), bool)
        or not 0 < below_call["committed_total"] < token_limit
        or gate_derived.get("response_count") != 2
        or gate_derived.get("response_ids")
        != [below_call.get("response_id"), sole_call.get("response_id")]
    ):
        raise BenchmarkToolError(
            "synthetic token canary lacks its sole sanitized gate crossing"
        )
    normalized = runner._read_ultra_token_usage(usage)
    response_ledger = normalized.get("appserver_response_ledger")
    if not isinstance(response_ledger, list) or len(response_ledger) != 2:
        raise BenchmarkToolError(
            "synthetic token canary lacks its turn/compaction response ledger"
        )
    below_response = _mapping(
        response_ledger[0], "synthetic below-cap response ledger entry"
    )
    compaction_response = _mapping(
        response_ledger[1], "synthetic compaction response ledger entry"
    )
    compaction_turn_id = compaction_response.get("turn_id")
    if (
        below_response.get("response_id") != below_call.get("response_id")
        or below_response.get("thread_id") != root
        or below_response.get("turn_id") != turn
        or compaction_response.get("response_id") != sole_call.get("response_id")
        or compaction_response.get("thread_id") != root
        or not isinstance(compaction_turn_id, str)
        or not compaction_turn_id
        or compaction_turn_id == turn
        or request_metadata.get("turn_id") != compaction_turn_id
    ):
        raise BenchmarkToolError(
            "synthetic token canary response ledger changed its compaction identity"
        )
    appserver_usage = {
        field: _nonnegative_int(usage.get(field), f"app-server {field}")
        for field in _TOKEN_FIELDS
    }
    provider_usage = {
        **{
            field: _nonnegative_int(normalized.get(field), f"provider {field}")
            for field in _TOKEN_FIELDS[:-1]
        },
        "total_tokens": _nonnegative_int(
            normalized.get("model_tokens"), "provider total_tokens"
        ),
    }
    reconciliation = run_matrix.verify_provider_usage_reconciliation(
        usage.get("provider_usage_reconciliation"),
        expected_provider_usage=provider_usage,
        expected_appserver_usage=appserver_usage,
        expected_provider_response_ids=gate_derived.get("response_ids"),
        expected_appserver_response_ids=usage.get("response_ids"),
        expected_appserver_response_ledger=usage.get("appserver_response_ledger"),
        required_suppressed_wait_count=0,
        required_superseded_collaboration_message_count=0,
        required_discarded_after_explicit_child_interrupt_count=0,
    )
    if (
        normalized.get("provider_usage_reconciliation") != reconciliation
        or normalized.get("provider_response_count") != 2
        or normalized.get("appserver_response_count") != 2
        or normalized.get("suppressed_collaboration_wait_response_count") != 0
        or normalized.get(
            "superseded_by_collaboration_message_response_count"
        )
        != 0
        or normalized.get(
            "discarded_after_explicit_child_interrupt_response_count"
        )
        != 0
        or normalized.get("provider_response_ids")
        != reconciliation["provider_response_ids"]
        or normalized.get("appserver_response_ids")
        != reconciliation["appserver_response_ids"]
        or normalized.get("response_count") != 2
        or normalized.get("response_ids")
        != reconciliation["provider_response_ids"]
        or normalized.get("call_count") != 2
    ):
        raise BenchmarkToolError(
            "synthetic token canary normalized provider totals are inconsistent"
        )
    messages = _json_messages(agent_log)
    event_order = _audit_sanitized_crossing(
        messages,
        root,
        turn,
        below_response_id=str(below_call["response_id"]),
        crossing_response_id=str(gate_crossing["response_id"]),
        compaction_turn_id=compaction_turn_id,
    )
    total = _positive_int(normalized.get("model_tokens"), "total model tokens")
    first = _positive_int(crossing.get("tokens"), "first crossing tokens")
    if (
        usage.get("measurement_source") != TOKEN_USAGE_SOURCE
        or usage.get("notification") != TOKEN_NOTIFICATION
        or usage.get("usage_scope") != TOKEN_USAGE_SCOPE
        or usage.get("drain_complete") is not False
        or usage.get("measurement_exact") is not True
        or usage.get("stop_reason") != "token_limit"
        or usage.get("interrupt_requested") is not False
        or usage.get("pending_interrupt_response_count") != 0
        or usage.get("active_thread_ids") != [root]
        or usage.get("unresolved_thread_ids") != []
        or usage.get("invalid_reasons") != []
        or usage.get("thread_count") != 1
        or usage.get("response_count") != 2
        or usage.get("notification_sequence") != 2
        or usage.get("accounting_projection_schema_version")
        != ACCOUNTING_PROJECTION_SCHEMA_VERSION
        or usage.get("spawn_binding_source") != SPAWN_BINDING_SOURCE
        or any(
            usage.get(field) != []
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
        or any(
            usage.get(field) is not True
            for field in (
                "spawn_linkage_complete",
                "descendant_accounting_complete",
                "fork_policy_complete",
            )
        )
        or usage.get("cumulative_projection_complete") is not False
        or usage.get("accounting_complete") is not False
        or first < token_limit
        or total != first
    ):
        raise BenchmarkToolError(
            "synthetic token canary lacks an exact root-only provider-gate crossing"
        )
    fork_policy = _mapping(
        usage.get("fork_policy"), "synthetic token canary fork policy"
    )
    expected_policy = {
        **codex_isolated.ultra_fork_policy_static_record(),
        "call_evidence": [],
        "complete": True,
    }
    if dict(fork_policy) != expected_policy:
        raise BenchmarkToolError(
            "synthetic token canary lacks the exact empty frozen fork-policy ledger"
        )
    threads = usage.get("threads")
    if not isinstance(threads, list) or len(threads) != 1:
        raise BenchmarkToolError("synthetic token canary root accounting is absent")
    root_accounting = _mapping(threads[0], "synthetic token canary root accounting")
    zero = {field: 0 for field in _TOKEN_FIELDS}
    if (
        root_accounting.get("thread_id") != root
        or root_accounting.get("parent_thread_id") is not None
        or root_accounting.get("spawn_binding_status") != "root_zero"
        or root_accounting.get("expected_cumulative_baseline") != zero
        or root_accounting.get("cumulative_baseline") != zero
        or root_accounting.get("cumulative_projection_exempt_response_id") is not None
        or root_accounting.get("response_count") != 2
        or root_accounting.get("cumulative_projection_match")
        is not usage.get("cumulative_projection_complete")
        or root_accounting.get("accounting_complete")
        is not usage.get("accounting_complete")
        or root_accounting.get("turn_status") != "inProgress"
        or root_accounting.get("active_turn_id") != compaction_turn_id
    ):
        raise BenchmarkToolError("synthetic token canary root projection is invalid")
    projection = {
        "accounting_projection_schema_version": ACCOUNTING_PROJECTION_SCHEMA_VERSION,
        "provider_gate_protocol": runner.PROVIDER_GATE_PROTOCOL,
        "provider_gate_record_sha256": gate_authentication.get("record_sha256"),
        "provider_gate_close_reason": gate_state.get("close_reason"),
        "provider_gate_response_ids": gate_derived.get("response_ids"),
        "provider_gate_deliveries_reconciled": _mapping(
            gate_record.get("invariants"), "synthetic provider-gate invariants"
        ).get("all_appserver_deliveries_reconciled"),
        "provider_usage_reconciliation": reconciliation,
        "provider_gate_setup_requests_empty": gate_record.get("setup_requests") == [],
        "provider_requests_quiescent": gate_state.get("all_complete") is True,
        "adapter_teardown_complete": _mapping(
            usage.get("adapter_teardown"), "synthetic adapter teardown"
        ).get("completed")
        is True,
        "spawn_binding_source": SPAWN_BINDING_SOURCE,
        "root_thread_id": root,
        "root_expected_cumulative_baseline": zero,
        "root_cumulative_projection_status": root_accounting.get(
            "cumulative_projection_status"
        ),
        "spawn_linkage_complete": usage.get("spawn_linkage_complete"),
        "descendant_accounting_complete": usage.get(
            "descendant_accounting_complete"
        ),
        "cumulative_projection_complete": usage.get(
            "cumulative_projection_complete"
        ),
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
        "fork_policy_complete": usage.get("fork_policy_complete"),
        "fork_policy": expected_policy,
        "accounting_complete": usage.get("accounting_complete"),
        "root_only": True,
    }
    projection["projection_payload_sha256"] = _canonical_sha256(projection)
    return {
        "input_tokens_including_cached": normalized["input_tokens"],
        "cached_input_tokens": normalized["cached_input_tokens"],
        "output_tokens": normalized["output_tokens"],
        "first_crossing_tokens": first,
        "first_crossing_overshoot_tokens": first - token_limit,
        "overshoot_tokens": first - token_limit,
        "final_endpoint_tokens": total,
        "final_overshoot_tokens": total - token_limit,
        "total_model_tokens": total,
        "response_count": 2,
        "provider_response_count": 2,
        "appserver_response_count": 2,
        "suppressed_collaboration_wait_response_count": 0,
        "superseded_by_collaboration_message_response_count": 0,
        "discarded_after_explicit_child_interrupt_response_count": 0,
        "thread_count": 1,
        "observed_child_thread_count": 0,
        "notification_sequence": 2,
        "notification_count_in_audit_log": 2,
        "root_terminal_status": "completed_before_compaction_crossing",
        "drain_complete": False,
        "tree_quiescent": False,
        "measurement_exact": True,
        "natural_completion": False,
        "token_limit_triggered": True,
        "stop_reason": "token_limit",
        "upstream_request_kind": "compaction",
        "provider_answer_content_released": False,
        "provider_gate_record_sha256": gate_authentication.get("record_sha256"),
        "benchmark_task_bytes_used": False,
        "event_order": event_order,
        "accounting_projection": projection,
    }


def validate_canary_record(
    record: Mapping[str, Any],
    *,
    canary_limit: int,
    agent_log: Path,
    usage_artifact: Mapping[str, Any],
) -> dict[str, Any]:
    if (
        record.get("run_id") != CANARY_ID
        or record.get("task_id") != CANARY_ID
        or record.get("paper_id") != "SYNTHETIC"
        or record.get("condition") != "N"
        or record.get("pass") is not False
        or record.get("failure_code") != "TOKEN_LIMIT"
        or type(record.get("agent_exit_code")) is not int
        or record.get("agent_exit_code") != 0
        or record.get("useful_work_started") is not True
        or record.get("scored") is not True
        or record.get("library_use") is not False
        or record.get("library_declarations") != []
        or record.get("submission_sha256") is not None
        or record.get("final_submission_sha256") is not None
        or record.get("ultra_submission_boundary") != {"verified": False}
    ):
        raise BenchmarkToolError("synthetic token canary runner outcome is invalid")
    normalized = runner._read_ultra_token_usage(usage_artifact)
    if record.get("token_usage") != normalized:
        raise BenchmarkToolError("synthetic token canary record changed its usage ledger")
    gate_authentication = run_matrix.authenticate_runner_provider_gate_summary(record)
    outcome = validate_usage_and_log(
        usage_artifact,
        agent_log,
        token_limit=canary_limit,
        gate_authentication=gate_authentication,
    )
    measurement = _mapping(record.get("token_measurement"), "canary token measurement")
    enforcement = _mapping(measurement.get("limit_enforcement"), "canary limit enforcement")
    expected_enforcement = {
        "mode": TOKEN_ENFORCEMENT_MODE,
        "notification": TOKEN_NOTIFICATION,
        "configured_limit_tokens": canary_limit,
        "triggered": True,
        "observed_tokens": outcome["first_crossing_tokens"],
        "overshoot_tokens": outcome["first_crossing_overshoot_tokens"],
        "first_crossing_tokens": outcome["first_crossing_tokens"],
        "first_crossing_overshoot_tokens": outcome[
            "first_crossing_overshoot_tokens"
        ],
        "final_endpoint_tokens": outcome["final_endpoint_tokens"],
        "final_overshoot_tokens": outcome["final_overshoot_tokens"],
        "checked_before_submission_validation": True,
        "one_response_overshoot_possible": True,
        "concurrent_inflight_overshoot_possible": False,
    }
    if any(enforcement.get(key) != value for key, value in expected_enforcement.items()):
        raise BenchmarkToolError("synthetic token canary threshold enforcement is invalid")
    if (
        measurement.get("source") != TOKEN_MEASUREMENT_SOURCE
        or measurement.get("provider_cumulative_total_exact") is not True
        or measurement.get("cached_input_counted_once") is not True
        or measurement.get("trusted_usage_path_outside_workspace") is not True
        or measurement.get("usage_scope") != TOKEN_USAGE_SCOPE
        or measurement.get("thread_count") != 1
        or measurement.get("response_count") != 2
        or measurement.get("tree_drain_complete") is not False
    ):
        raise BenchmarkToolError("synthetic token canary measurement is not exact")
    protocol = _mapping(record.get("protocol"), "canary protocol")
    claims = _mapping(protocol.get("claims"), "canary protocol claims")
    verified = _mapping(protocol.get("verified"), "canary protocol verification")
    if (
        claims.get("token_limit_enforced_by_agent") is not True
        or verified.get("authenticated_prompt_release") is not True
        or verified.get("authenticated_provider_token_gate") is not True
        or verified.get("provider_gate_appserver_deliveries_reconciled") is not True
        or verified.get("provider_gate_terminal_endpoint") is not True
    ):
        raise BenchmarkToolError(
            "synthetic token canary lacks token enforcement or authenticated prompt release"
        )
    network = _mapping(record.get("network_violation"), "canary network evidence")
    if network.get("detected") is not False or network.get("integrity_ok") is not True:
        raise BenchmarkToolError("synthetic token canary recorded a network violation")
    outcome["actual_stop_seconds"] = record.get("actual_stop_seconds")
    return outcome


def controls_record(
    frozen_token_limit: int, canary_token_limit: int, wall_time_seconds: int
) -> dict[str, Any]:
    if (
        type(frozen_token_limit) is not int
        or type(canary_token_limit) is not int
        or frozen_token_limit <= canary_token_limit
        or canary_token_limit != DEFAULT_CANARY_TOKEN_LIMIT
        or canary_token_limit >= runner.PROVIDER_RESPONSE_TOKEN_BOUND
        or wall_time_seconds <= 0
    ):
        raise BenchmarkToolError("synthetic token canary controls are invalid")
    return {
        "frozen_benchmark_token_limit": frozen_token_limit,
        "outer_canary_token_limit": canary_token_limit,
        "nested_advisory_rollout_budget_limit": frozen_token_limit,
        "canary_wall_time_seconds": wall_time_seconds,
        "measurement_source": TOKEN_USAGE_SOURCE,
        "notification": TOKEN_NOTIFICATION,
        "usage_scope": TOKEN_USAGE_SCOPE,
        "live_cumulative": True,
        "cached_input_counted_once": True,
        "all_descendant_threads_included": True,
        "response_ids_deduplicated": True,
        "drain_complete_required": False,
        "provider_token_quiescence_required": True,
        "tree_quiescence_distinct_from_provider_quiescence": True,
        "measurement_exact_required": True,
        "root_completion_is_tree_barrier": False,
        "trusted_adapter_freezes_first_threshold": False,
        "trusted_adapter_latches_first_threshold": True,
        "trusted_usage_path_outside_workspace": True,
        "condition_isolation_mode": "N_without_library_or_condition_supplement",
        "condition_supplement_used": False,
        "library_or_library_path_used": False,
        "synthetic_input_required": True,
        "benchmark_task_bytes_used": False,
        "upstream_compaction_requested": True,
        "provider_answer_content_release_forbidden": True,
        "sanitized_compaction_crossing_required": True,
        "no_tools_required": True,
        "root_only_required": True,
        "natural_completion_required": False,
        "authenticated_prompt_release_required": True,
        "prompt_release_protocol_version": PROMPT_RELEASE_PROTOCOL_VERSION,
        "prompt_startup_timeout_seconds": PROMPT_STARTUP_TIMEOUT_SECONDS,
        "prompt_ready_go_released_files_required": 3,
        "prompt_artifact_canonical_json_required": True,
        "prompt_artifact_sealed_mode": "0444",
        "measurement_time_origin": "RELEASED.released_at_monotonic_ns",
        "release_based_deadline_required": True,
        "submission_boundary_expected": False,
        "exact_event_order_required": (
            "below_cap_direct_final_then_compaction_item_then_crossing_"
            "rawResponse_completed_then_no_model_activity"
        ),
        "sealed_provider_gate_mode": "0444",
        "provider_gate_close_reason": "token_limit",
        "provider_gate_setup_requests": [],
        "accounting_projection_schema_version": ACCOUNTING_PROJECTION_SCHEMA_VERSION,
        "spawn_binding_source": SPAWN_BINDING_SOURCE,
        "spawn_linkage_complete_required": True,
        "descendant_accounting_complete_required": True,
        "cumulative_projection_complete_required": False,
        "accounting_complete_required": False,
        "ephemeral_thread": False,
        "history_persistence": "none",
        "thread_resume_or_fork_used": False,
        "state_directory_reused": False,
    }


def _runner_freeze_record(freeze_check: Mapping[str, Any]) -> dict[str, Any]:
    value = json.loads(json.dumps(freeze_check, sort_keys=True))
    if not isinstance(value, dict):
        raise BenchmarkToolError("synthetic token canary freeze check is invalid")
    production_prompt = value.get("prompt_protocol")
    synthetic_protocol = synthetic_signposted_prompt_protocol()
    value["prompt_protocol"] = synthetic_protocol
    value["synthetic_canary"] = {
        "canary_id": CANARY_ID,
        "prompt_protocol": PROMPT_PROTOCOL,
        "signposted_prompt_protocol": runner.SIGNPOSTED_PROMPT_PROTOCOL_VERSION,
        "synthetic_prompt_protocol_sha256": _canonical_sha256(synthetic_protocol),
        "condition": "N",
        "N_receives_condition_supplement": False,
        "matrix_assignment": False,
        "scored": False,
        "benchmark_task_bytes_used": False,
        "production_freeze_check_sha256": _canonical_sha256(dict(freeze_check)),
        "production_prompt_protocol_sha256": (
            _canonical_sha256(dict(production_prompt))
            if isinstance(production_prompt, Mapping)
            else None
        ),
    }
    return value


def _write_synthetic_inputs(task: Path) -> tuple[Path, Path, Path]:
    task.mkdir(parents=True)
    prompt = task / "prompt.md"
    context = task / "context.md"
    target = task / "SyntheticTarget.lean"
    prompt.write_text(SYNTHETIC_COMMON_PROMPT, encoding="utf-8")
    context.write_text(SYNTHETIC_CONTEXT, encoding="utf-8")
    target.write_text(SYNTHETIC_TARGET, encoding="utf-8")
    return prompt, context, target


def _adapter_command(args: argparse.Namespace, *, state_parent: Path) -> list[str]:
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
        "task",
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
        "--provider-token-gate-compaction-canary",
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
        str(args.canary_token_limit),
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
    return [
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
        "--reject-workspace-local-module-imports",
        "--prompt-relative",
        "task/prompt.md",
        "--usage-output",
        str(usage_output.resolve()),
        "--agent-command-json",
        json.dumps(adapter, separators=(",", ":")),
        "--compile-command-json",
        json.dumps(compile_command, separators=(",", ":")),
        "--n-probe-command-json",
        json.dumps(probe_command, separators=(",", ":")),
        "--hidden-parent",
        str((result_root / "hidden").resolve()),
        "--time-limit-seconds",
        str(args.canary_time_limit_seconds),
        "--prompt-startup-timeout-seconds",
        str(int(PROMPT_STARTUP_TIMEOUT_SECONDS)),
        "--token-limit",
        str(args.canary_token_limit),
        "--fresh-conversation",
        "--filesystem-isolated",
        "--network-disabled",
        "--token-enforced",
        "--output",
        str(runner_record.resolve()),
    ]


def _option_value(argv: Sequence[str], option: str) -> str:
    positions = [index for index, item in enumerate(argv) if item == option]
    if len(positions) != 1 or positions[0] + 1 >= len(argv):
        raise BenchmarkToolError(f"synthetic token canary invocation lacks unique {option}")
    return argv[positions[0] + 1]


def _verify_provider_command(
    command: Sequence[str], *, canary_limit: int, frozen_limit: int
) -> None:
    expected = {
        "--condition": "N",
        "--controlled-relative": "task",
        "--prompt-file": "{workspace}/task/prompt.md",
        "--context-file": "{workspace}/task/context.md",
        "--target-file": "{workspace}/task/SyntheticTarget.lean",
        "--prompt-ready-output": "{prompt_ready_output}",
        "--prompt-go-input": "{prompt_go_input}",
        "--prompt-release-output": "{prompt_release_output}",
        "--prompt-handshake-nonce": "{prompt_handshake_nonce}",
        "--prompt-run-id": "{run_id}",
        "--provider-gate-live-output": "{provider_gate_live_output}",
        "--provider-gate-output": "{provider_gate_output}",
        "--model-catalog-sha256": "{model_catalog_sha256}",
        "--model-entry-sha256": "{model_entry_sha256}",
        "--provider-response-bound": "{provider_response_bound}",
        "--token-limit": str(canary_limit),
        "--advisory-rollout-budget-limit": str(frozen_limit),
    }
    for option, wanted in expected.items():
        if _option_value(command, option) != wanted:
            raise BenchmarkToolError(f"synthetic provider command has wrong {option}")
    if command.count("--provider-token-gate-compaction-canary") != 1:
        raise BenchmarkToolError(
            "synthetic provider command lacks its unique compaction-canary mode"
        )
    forbidden = (
        "--condition-prompt-file",
        "--condition-prompt-sha256",
        "--library-source-root",
        "--library-root-file",
        "--library-olean-root",
    )
    if any(option in command for option in forbidden):
        raise BenchmarkToolError("synthetic provider command exposes L/library material")
    joined = "\n".join(command)
    if "/tasks/P01/" in joined or "/tasks/P02/" in joined:
        raise BenchmarkToolError("synthetic provider command exposes a P01/P02 task path")


def _verify_rendered_provider_command(
    template: Sequence[str],
    rendered: Sequence[str],
    *,
    usage_output: Path,
    prompt_paths: Mapping[str, Path],
    handshake_nonce: str,
    run_id: str,
    canary_limit: int,
    frozen_limit: int,
) -> None:
    """Bind the runner-recorded provider argv to its pre-release template."""

    if len(template) != len(rendered):
        raise BenchmarkToolError("synthetic provider command changed length")
    workspace: str | None = None
    for expected, actual in zip(template, rendered):
        if expected == "{workspace}":
            if not isinstance(actual, str) or not actual or not Path(actual).is_absolute():
                raise BenchmarkToolError("synthetic provider workspace was not rendered")
            workspace = actual
            continue
        if expected.startswith("{workspace}/"):
            suffix = expected[len("{workspace}") :]
            if (
                not isinstance(actual, str)
                or not actual.endswith(suffix)
                or not Path(actual).is_absolute()
            ):
                raise BenchmarkToolError("synthetic provider staged-source path drifted")
            candidate_workspace = actual[: -len(suffix)]
            if workspace not in (None, candidate_workspace):
                raise BenchmarkToolError("synthetic provider used two workspaces")
            workspace = candidate_workspace
            continue
        if expected == "{usage_output}":
            if Path(actual).resolve() != usage_output.resolve():
                raise BenchmarkToolError("synthetic provider trusted usage path drifted")
            continue
        placeholder_values = {
            "{prompt_ready_output}": str(prompt_paths["ready"]),
            "{prompt_go_input}": str(prompt_paths["go"]),
            "{prompt_release_output}": str(prompt_paths["release"]),
            "{prompt_handshake_nonce}": handshake_nonce,
            "{run_id}": run_id,
            "{provider_gate_live_output}": str(
                runner.provider_gate_paths(usage_output.resolve())["live"]
            ),
            "{provider_gate_output}": str(
                runner.provider_gate_paths(usage_output.resolve())["final"]
            ),
        }
        gate_catalog = _mapping(
            _mapping(
                read_json(runner.provider_gate_paths(usage_output.resolve())["final"]),
                "synthetic provider-gate artifact",
            ).get("configuration"),
            "synthetic provider-gate configuration",
        )
        placeholder_values.update(
            {
                "{model_catalog_sha256}": str(gate_catalog.get("model_catalog_sha256")),
                "{model_entry_sha256}": str(gate_catalog.get("model_entry_sha256")),
                "{provider_response_bound}": str(gate_catalog.get("response_bound")),
            }
        )
        if expected in placeholder_values:
            if actual != placeholder_values[expected]:
                raise BenchmarkToolError(
                    "synthetic provider prompt-handshake binding drifted"
                )
            continue
        if actual != expected:
            raise BenchmarkToolError("synthetic provider command differs from invocation")
    if workspace is None:
        raise BenchmarkToolError("synthetic provider command has no rendered workspace")
    _verify_provider_command(
        template, canary_limit=canary_limit, frozen_limit=frozen_limit
    )


_PROMPT_COMMON_FIELDS = (
    "schema_version",
    "protocol_version",
    "handshake_nonce",
    "run_id",
    "condition",
    "model",
    "reasoning_effort",
    "root_thread_id",
    "turn_start_request_id",
    "effective_prompt_sha256",
    "effective_prompt_bytes",
    "adapter_name",
    "adapter_version",
    "app_server_client_name",
    "app_server_client_version",
    "elapsed_clock",
)


def _prompt_handshake_paths(usage_path: Path) -> dict[str, Path]:
    name = usage_path.name
    suffix = ".usage.json"
    base = name[: -len(suffix)] if name.endswith(suffix) else usage_path.stem
    if not base or base in (".", ".."):
        raise BenchmarkToolError("synthetic canary usage path has no handshake basename")
    return {
        "ready": usage_path.parent / f"{base}.prompt-ready.json",
        "go": usage_path.parent / f"{base}.prompt-go.json",
        "release": usage_path.parent / f"{base}.prompt-release.json",
    }


def _authenticate_prompt_artifact(
    descriptor: Mapping[str, Any],
    *,
    expected_path: Path,
    hash_field: str,
    label: str,
) -> dict[str, Any]:
    if set(descriptor) != {"path", "file_sha256", "record_sha256", "record"}:
        raise BenchmarkToolError(f"synthetic prompt {label} descriptor schema is invalid")
    raw_path = descriptor.get("path")
    file_digest = descriptor.get("file_sha256")
    record_digest = descriptor.get("record_sha256")
    if (
        not isinstance(raw_path, str)
        or not Path(raw_path).is_absolute()
        or Path(raw_path) != expected_path
        or not isinstance(file_digest, str)
        or re.fullmatch(r"[0-9a-f]{64}", file_digest) is None
        or not isinstance(record_digest, str)
        or re.fullmatch(r"[0-9a-f]{64}", record_digest) is None
    ):
        raise BenchmarkToolError(f"synthetic prompt {label} descriptor identity is invalid")
    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    try:
        file_descriptor = os.open(expected_path, flags)
    except OSError as error:
        raise BenchmarkToolError(
            f"synthetic prompt {label} artifact is missing or unsafe"
        ) from error
    try:
        details = os.fstat(file_descriptor)
        if (
            not stat.S_ISREG(details.st_mode)
            or stat.S_IMODE(details.st_mode) != 0o444
            or details.st_size <= 0
            or details.st_size > 64 * 1024
        ):
            raise BenchmarkToolError(
                f"synthetic prompt {label} artifact is not sealed 0444 canonical JSON"
            )
        chunks: list[bytes] = []
        remaining = details.st_size
        while remaining:
            chunk = os.read(file_descriptor, min(remaining, 64 * 1024))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        payload = b"".join(chunks)
        if len(payload) != details.st_size:
            raise BenchmarkToolError(
                f"synthetic prompt {label} artifact changed while being read"
            )
    finally:
        os.close(file_descriptor)
    try:
        current = expected_path.lstat()
    except OSError as error:
        raise BenchmarkToolError(
            f"synthetic prompt {label} artifact disappeared"
        ) from error
    if (
        stat.S_ISLNK(current.st_mode)
        or stat.S_IMODE(current.st_mode) != 0o444
        or current.st_dev != details.st_dev
        or current.st_ino != details.st_ino
        or current.st_size != details.st_size
    ):
        raise BenchmarkToolError(
            f"synthetic prompt {label} artifact changed while being authenticated"
        )
    if hashlib.sha256(payload).hexdigest() != file_digest:
        raise BenchmarkToolError(f"synthetic prompt {label} file hash is invalid")
    try:
        raw_record = json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise BenchmarkToolError(
            f"synthetic prompt {label} artifact is not UTF-8 JSON"
        ) from error
    record = _mapping(raw_record, f"synthetic prompt {label} record")
    canonical = (
        json.dumps(record, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")
    if payload != canonical:
        raise BenchmarkToolError(
            f"synthetic prompt {label} artifact is not canonically encoded"
        )
    digest = record.get(hash_field)
    unsigned = dict(record)
    unsigned.pop(hash_field, None)
    if (
        digest != record_digest
        or _canonical_sha256(unsigned) != record_digest
    ):
        raise BenchmarkToolError(f"synthetic prompt {label} self hash is invalid")
    if descriptor.get("record") != dict(record):
        raise BenchmarkToolError(f"synthetic prompt {label} embedded record is stale")
    return dict(record)


def authenticate_prompt_release(
    record: Mapping[str, Any],
    *,
    usage_artifact: Mapping[str, Any],
    usage_path: Path,
    provider_command: Sequence[str],
    wall_time_seconds: int,
) -> dict[str, Any]:
    """Independently authenticate the exact synthetic prompt-release origin."""

    release = _mapping(record.get("prompt_release"), "synthetic prompt release")
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
    prompt_bytes = synthetic_effective_prompt().encode("utf-8")
    nonce = release.get("handshake_nonce")
    if (
        set(release) != expected_top_fields
        or release.get("schema_version") != PROMPT_RELEASE_SCHEMA_VERSION
        or release.get("protocol_version") != PROMPT_RELEASE_PROTOCOL_VERSION
        or release.get("required") is not True
        or release.get("status") != "released_authenticated"
        or release.get("authenticated") is not True
        or release.get("timing_exact") is not True
        or release.get("useful_work_basis") != "authenticated_release"
        or release.get("startup_timeout_seconds") != PROMPT_STARTUP_TIMEOUT_SECONDS
        or release.get("startup_timeout_triggered") is not False
        or release.get("go_minimum_release_window_seconds")
        != PROMPT_GO_MINIMUM_RELEASE_WINDOW_SECONDS
        or not isinstance(nonce, str)
        or re.fullmatch(r"[0-9a-f]{64}", nonce) is None
        or release.get("elapsed_clock") != "CLOCK_MONOTONIC"
        or release.get("effective_prompt_sha256")
        != hashlib.sha256(prompt_bytes).hexdigest()
        or release.get("effective_prompt_bytes") != len(prompt_bytes)
        or release.get("stale_artifacts_removed") != []
        or release.get("error") is not None
    ):
        raise BenchmarkToolError("synthetic prompt-release header is invalid")

    usage_path = usage_path.resolve()
    expected_paths = {
        key: value.resolve() for key, value in _prompt_handshake_paths(usage_path).items()
    }
    artifact_paths = _mapping(
        release.get("artifact_paths"), "synthetic prompt-release paths"
    )
    if artifact_paths != {key: str(value) for key, value in expected_paths.items()}:
        raise BenchmarkToolError("synthetic prompt-release paths are not usage-bound")
    if any(path.parent != usage_path.parent for path in expected_paths.values()):
        raise BenchmarkToolError("synthetic prompt-release paths escape trusted logs")

    descriptors = {
        "ready": _mapping(release.get("ready"), "synthetic prompt READY descriptor"),
        "go": _mapping(release.get("go"), "synthetic prompt GO descriptor"),
        "release": _mapping(
            release.get("released"), "synthetic prompt RELEASED descriptor"
        ),
    }
    ready = _authenticate_prompt_artifact(
        descriptors["ready"],
        expected_path=expected_paths["ready"],
        hash_field="ready_sha256",
        label="READY",
    )
    go = _authenticate_prompt_artifact(
        descriptors["go"],
        expected_path=expected_paths["go"],
        hash_field="go_sha256",
        label="GO",
    )
    released = _authenticate_prompt_artifact(
        descriptors["release"],
        expected_path=expected_paths["release"],
        hash_field="release_sha256",
        label="RELEASED",
    )

    model = _option_value(provider_command, "--model")
    effort = _option_value(provider_command, "--reasoning-effort")
    root_thread_id = usage_artifact.get("root_thread_id")
    if not isinstance(root_thread_id, str) or not root_thread_id:
        raise BenchmarkToolError("synthetic prompt release lacks a usage-bound root")
    common = {
        "schema_version": PROMPT_RELEASE_SCHEMA_VERSION,
        "protocol_version": PROMPT_RELEASE_PROTOCOL_VERSION,
        "handshake_nonce": nonce,
        "run_id": CANARY_RUN_ID,
        "condition": "N",
        "model": model,
        "reasoning_effort": effort,
        "root_thread_id": root_thread_id,
        "turn_start_request_id": TURN_START_REQUEST_ID,
        "effective_prompt_sha256": hashlib.sha256(prompt_bytes).hexdigest(),
        "effective_prompt_bytes": len(prompt_bytes),
        "adapter_name": PROMPT_RELEASE_ADAPTER_NAME,
        "adapter_version": PROMPT_RELEASE_ADAPTER_VERSION,
        "app_server_client_name": APP_SERVER_CLIENT_NAME,
        "app_server_client_version": APP_SERVER_CLIENT_VERSION,
        "elapsed_clock": "CLOCK_MONOTONIC",
    }
    ready_variable = {
        "kind": "highambench_prompt_ready",
        "turn_start_write_state": "not_started",
        "ready_at_monotonic_ns": ready.get("ready_at_monotonic_ns"),
        "ready_at_unix_ns": ready.get("ready_at_unix_ns"),
    }
    if set(ready) != set(_PROMPT_COMMON_FIELDS) | set(ready_variable) | {"ready_sha256"} or any(
        ready.get(key) != value for key, value in {**common, **ready_variable}.items()
    ):
        raise BenchmarkToolError("synthetic prompt READY identity is invalid")
    go_variable = {
        "kind": "highambench_prompt_go",
        "ready_sha256": ready["ready_sha256"],
        "turn_start_write_authorized": True,
        "authorized_at_monotonic_ns": go.get("authorized_at_monotonic_ns"),
        "authorized_at_unix_ns": go.get("authorized_at_unix_ns"),
    }
    if set(go) != set(_PROMPT_COMMON_FIELDS) | set(go_variable) | {"go_sha256"} or any(
        go.get(key) != value for key, value in {**common, **go_variable}.items()
    ):
        raise BenchmarkToolError("synthetic prompt GO identity is invalid")

    request = {
        "id": TURN_START_REQUEST_ID,
        "method": "turn/start",
        "params": {
            "approvalPolicy": "never",
            "cwd": "/workspace",
            "effort": effort,
            "input": [{"type": "text", "text": synthetic_effective_prompt()}],
            "model": model,
            "sandboxPolicy": {"type": "dangerFullAccess"},
            "threadId": root_thread_id,
        },
    }
    wire = (
        json.dumps(request, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")
    released_variable = {
        "kind": "highambench_prompt_released",
        "ready_sha256": ready["ready_sha256"],
        "go_sha256": go["go_sha256"],
        "turn_start_write_state": "flushed",
        "timestamp_capture_point": "immediately_before_turn_start_write",
        "turn_start_request_sha256": hashlib.sha256(wire).hexdigest(),
        "turn_start_request_bytes": len(wire),
        "released_at_monotonic_ns": released.get("released_at_monotonic_ns"),
        "released_at_unix_ns": released.get("released_at_unix_ns"),
        "turn_start_flushed_at_monotonic_ns": released.get(
            "turn_start_flushed_at_monotonic_ns"
        ),
        "turn_start_flushed_at_unix_ns": released.get(
            "turn_start_flushed_at_unix_ns"
        ),
    }
    if set(released) != set(_PROMPT_COMMON_FIELDS) | set(released_variable) | {"release_sha256"} or any(
        released.get(key) != value
        for key, value in {**common, **released_variable}.items()
    ):
        raise BenchmarkToolError("synthetic prompt RELEASED identity is invalid")

    timestamps = (
        ready.get("ready_at_monotonic_ns"),
        go.get("authorized_at_monotonic_ns"),
        released.get("released_at_monotonic_ns"),
        released.get("turn_start_flushed_at_monotonic_ns"),
    )
    wall_timestamps = (
        ready.get("ready_at_unix_ns"),
        go.get("authorized_at_unix_ns"),
        released.get("released_at_unix_ns"),
        released.get("turn_start_flushed_at_unix_ns"),
    )
    if (
        any(type(value) is not int or value <= 0 for value in timestamps)
        or list(timestamps) != sorted(timestamps)
        or any(type(value) is not int or value <= 0 for value in wall_timestamps)
        or list(wall_timestamps) != sorted(wall_timestamps)
    ):
        raise BenchmarkToolError("synthetic prompt-release timestamps are invalid")

    expected_command_options = {
        "--prompt-ready-output": str(expected_paths["ready"]),
        "--prompt-go-input": str(expected_paths["go"]),
        "--prompt-release-output": str(expected_paths["release"]),
        "--prompt-handshake-nonce": nonce,
        "--prompt-run-id": CANARY_RUN_ID,
    }
    if any(
        _option_value(provider_command, option) != value
        for option, value in expected_command_options.items()
    ):
        raise BenchmarkToolError("synthetic prompt release is not command-bound")

    actual_stop = record.get("actual_stop_seconds")
    if (
        not isinstance(wall_time_seconds, int)
        or isinstance(wall_time_seconds, bool)
        or wall_time_seconds <= 0
        or not isinstance(actual_stop, (int, float))
        or isinstance(actual_stop, bool)
        or actual_stop <= 0
        or actual_stop >= wall_time_seconds
        or record.get("first_valid_seconds") is not None
        or record.get("submission_sha256") is not None
        or record.get("final_submission_sha256") is not None
    ):
        raise BenchmarkToolError(
            "synthetic token crossing is not measured from authenticated prompt release"
        )
    release_monotonic = int(timestamps[2])
    deadline_monotonic = release_monotonic + wall_time_seconds * 1_000_000_000
    crossing = _mapping(
        usage_artifact.get("first_crossing"), "synthetic prompt-release crossing"
    )
    crossing_unix = crossing.get("observed_at_unix_ns")
    if (
        type(crossing_unix) is not int
        or crossing_unix < int(wall_timestamps[2])
        or crossing_unix
        >= int(wall_timestamps[2]) + wall_time_seconds * 1_000_000_000
    ):
        raise BenchmarkToolError("synthetic token crossing falls outside release deadline")
    return {
        "schema_version": PROMPT_RELEASE_SCHEMA_VERSION,
        "protocol_version": PROMPT_RELEASE_PROTOCOL_VERSION,
        "status": "released_authenticated",
        "authenticated": True,
        "timing_exact": True,
        "useful_work_basis": "authenticated_release",
        "startup_timeout_seconds": PROMPT_STARTUP_TIMEOUT_SECONDS,
        "startup_timeout_triggered": False,
        "go_minimum_release_window_seconds": (
            PROMPT_GO_MINIMUM_RELEASE_WINDOW_SECONDS
        ),
        "artifact_content_verified": True,
        "artifact_count": 3,
        "artifacts": {
            label: {
                "path": str(expected_paths[label]),
                "file_sha256": descriptors[label]["file_sha256"],
                "record_sha256": descriptors[label]["record_sha256"],
            }
            for label in ("ready", "go", "release")
        },
        "canonical_encoding": "compact_sorted_key_utf8_json_newline",
        "sealed_mode": "0444",
        "handshake_nonce": nonce,
        "root_thread_id": root_thread_id,
        "effective_prompt_sha256": hashlib.sha256(prompt_bytes).hexdigest(),
        "effective_prompt_bytes": len(prompt_bytes),
        "turn_start_request_sha256": hashlib.sha256(wire).hexdigest(),
        "turn_start_wire_verified": True,
        "command_binding_verified": True,
        "root_identity_verified": True,
        "ready_sha256": ready["ready_sha256"],
        "go_sha256": go["go_sha256"],
        "release_sha256": released["release_sha256"],
        "measurement_time_origin": "RELEASED.released_at_monotonic_ns",
        "released_at_monotonic_ns": release_monotonic,
        "deadline_monotonic_ns": deadline_monotonic,
        "deadline_derivation": (
            "released_at_monotonic_ns + wall_time_seconds*1000000000"
        ),
        "wall_time_seconds": wall_time_seconds,
        "actual_stop_seconds": actual_stop,
        "token_crossing_within_deadline": True,
        "first_valid_seconds": None,
        "submission_boundary": None,
        "sanitized_provider_gate_crossing": True,
        "top_level_artifact_count_unchanged": len(ARTIFACT_LABELS),
    }


def build_attestation(
    *,
    production_freeze_check: Mapping[str, Any],
    runner_freeze_check: Mapping[str, Any],
    frozen_token_limit: int,
    canary_token_limit: int,
    canary_time_limit_seconds: int,
    result_root: Path,
    project_root: Path,
    paths: Mapping[str, Path],
    outcome: Mapping[str, Any],
    source_separation: Mapping[str, Any],
) -> dict[str, Any]:
    artifacts = {
        label: {
            "path": _relative_artifact(paths[label], result_root),
            "sha256": sha256_file(paths[label]),
        }
        for label in ARTIFACT_LABELS
    }
    return {
        "schema_version": EVIDENCE_SCHEMA_VERSION,
        "kind": EVIDENCE_KIND,
        "status": "passed",
        "public_release": False,
        "scored": False,
        "matrix_assignment": False,
        "synthetic_input": True,
        "benchmark_task_bytes_used": False,
        "canary_id": CANARY_ID,
        "benchmark_id": production_freeze_check.get("benchmark_id"),
        "pre_canary_environment_id": production_freeze_check.get("environment_id"),
        # Compatibility field: this is the exact check embedded in the runner record.
        "freeze_check_sha256": _canonical_sha256(dict(runner_freeze_check)),
        "pre_canary_freeze_check_sha256": _canonical_sha256(
            dict(production_freeze_check)
        ),
        "runner_freeze_check_sha256": _canonical_sha256(dict(runner_freeze_check)),
        "assignment": {
            "task_id": CANARY_ID,
            "paper_id": "SYNTHETIC",
            "condition": "N",
            "repetition_id": "canary",
            "matrix_assignment": False,
        },
        "agent": _attestation_agent(production_freeze_check),
        "prompt": prompt_record(),
        "source_separation": {
            key: source_separation[key]
            for key in (
                "audit_sha256",
                "benchmark_manifest_sha256",
                "benchmark_source_catalog_sha256",
                "benchmark_source_count",
                "benchmark_source_role_counts",
                "p01_p02_source_count",
                "exact_sha256_match_count",
                "exact_byte_identity_match_count",
                "embedded_benchmark_source_count",
                "benchmark_task_bytes_used",
                "condition_supplement_used",
                "library_or_library_path_used",
            )
        },
        "artifact_root": result_root.resolve().relative_to(
            project_root.resolve()
        ).as_posix(),
        "controls": controls_record(
            frozen_token_limit, canary_token_limit, canary_time_limit_seconds
        ),
        "outcome": dict(outcome),
        "artifacts": artifacts,
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
        raise BenchmarkToolError(f"synthetic canary artifact {label} is invalid")
    path = (artifact_root / relative).resolve()
    try:
        path.relative_to(artifact_root)
        artifact_root.relative_to(project_root.resolve())
    except ValueError as error:
        raise BenchmarkToolError(f"synthetic canary artifact {label} escapes its root") from error
    if path.is_symlink() or not path.is_file() or sha256_file(path) != digest:
        raise BenchmarkToolError(f"synthetic canary artifact {label} failed authentication")
    if label == "provider_gate" and stat.S_IMODE(path.lstat().st_mode) != 0o444:
        raise BenchmarkToolError(
            "synthetic canary provider-gate artifact is not sealed mode 0444"
        )
    return path


def validate_attestation_document(
    evidence: Mapping[str, Any],
    *,
    project_root: Path,
    expected_benchmark_id: str,
    expected_agent: Mapping[str, Any],
    expected_frozen_token_limit: int,
) -> dict[str, Any]:
    if (
        evidence.get("schema_version") != EVIDENCE_SCHEMA_VERSION
        or evidence.get("kind") != EVIDENCE_KIND
        or evidence.get("status") != "passed"
        or evidence.get("public_release") is not False
        or evidence.get("scored") is not False
        or evidence.get("matrix_assignment") is not False
        or evidence.get("synthetic_input") is not True
        or evidence.get("benchmark_task_bytes_used") is not False
        or evidence.get("canary_id") != CANARY_ID
        or evidence.get("benchmark_id") != expected_benchmark_id
        or evidence.get("agent") != dict(expected_agent)
        or evidence.get("prompt") != prompt_record()
    ):
        raise BenchmarkToolError("synthetic token-canary attestation header is invalid")
    controls = _mapping(evidence.get("controls"), "synthetic canary controls")
    wall = controls.get("canary_wall_time_seconds")
    if not isinstance(wall, int) or isinstance(wall, bool) or dict(controls) != controls_record(
        expected_frozen_token_limit, DEFAULT_CANARY_TOKEN_LIMIT, wall
    ):
        raise BenchmarkToolError("synthetic token-canary controls are invalid")
    project = project_root.resolve()
    artifact_root_raw = evidence.get("artifact_root")
    if not isinstance(artifact_root_raw, str) or not artifact_root_raw:
        raise BenchmarkToolError("synthetic token-canary artifact root is missing")
    artifact_root = (project / artifact_root_raw).resolve()
    try:
        artifact_root.relative_to(project)
    except ValueError as error:
        raise BenchmarkToolError("synthetic token-canary artifact root escapes project") from error
    artifacts = _mapping(evidence.get("artifacts"), "synthetic canary artifacts")
    if set(artifacts) != set(ARTIFACT_LABELS):
        raise BenchmarkToolError("synthetic token-canary artifact set is incomplete")
    paths = {
        label: _artifact_path(
            project, artifact_root, _mapping(artifacts[label], label), label
        )
        for label in ARTIFACT_LABELS
    }
    exact_sources = {
        "common_prompt": SYNTHETIC_COMMON_PROMPT.encode("utf-8"),
        "context": SYNTHETIC_CONTEXT.encode("utf-8"),
        "synthetic_target": SYNTHETIC_TARGET.encode("utf-8"),
    }
    for label, wanted in exact_sources.items():
        if paths[label].read_bytes() != wanted:
            raise BenchmarkToolError(f"synthetic token-canary {label} bytes changed")
    manifest = load_manifest(paths["controlled_manifest"])
    if {
        entry.get("path") for entry in manifest.get("files", []) if isinstance(entry, Mapping)
    } != {"prompt.md", "context.md", "SyntheticTarget.lean"}:
        raise BenchmarkToolError("synthetic token-canary controlled manifest is not exact")
    if not verify_manifest(paths["common_prompt"].parent, manifest)["ok"]:
        raise BenchmarkToolError("synthetic token-canary controlled sources failed verification")
    if codex_isolated.build_prompt(
        paths["common_prompt"], paths["context"], paths["synthetic_target"]
    ) != synthetic_effective_prompt():
        raise BenchmarkToolError("synthetic token-canary effective prompt changed")
    production_freeze = _mapping(read_json(paths["freeze_check"]), "pre-canary freeze check")
    runner_freeze = _mapping(
        read_json(paths["runner_freeze_check"]), "runner canary freeze check"
    )
    if (
        production_freeze.get("benchmark_id") != expected_benchmark_id
        or production_freeze.get("agent") != dict(expected_agent)
        or evidence.get("pre_canary_freeze_check_sha256")
        != _canonical_sha256(dict(production_freeze))
        or evidence.get("runner_freeze_check_sha256")
        != _canonical_sha256(dict(runner_freeze))
        or evidence.get("freeze_check_sha256")
        != _canonical_sha256(dict(runner_freeze))
        or dict(runner_freeze) != _runner_freeze_record(production_freeze)
    ):
        raise BenchmarkToolError("synthetic token-canary freeze provenance is invalid")
    source_audit = _mapping(
        read_json(paths["benchmark_source_audit"]), "benchmark source separation"
    )
    _verify_self_hash(source_audit, "audit_sha256", "benchmark source separation")
    benchmark_root = project / "paper_bencmark" / "highambench"
    benchmark_manifest = _mapping(
        read_json(benchmark_root / "metadata" / "manifest.json"), "benchmark manifest"
    )
    regenerated = audit_benchmark_source_separation(
        project_root=project,
        benchmark_root=benchmark_root,
        manifest=benchmark_manifest,
        generated_sources={
            **exact_sources,
            "effective_prompt": synthetic_effective_prompt().encode("utf-8"),
        },
    )
    if dict(source_audit) != regenerated:
        raise BenchmarkToolError("synthetic token-canary source-separation audit is stale")
    source_summary = _mapping(evidence.get("source_separation"), "source summary")
    if any(source_summary.get(key) != source_audit.get(key) for key in source_summary):
        raise BenchmarkToolError("synthetic token-canary source summary is stale")
    if set(source_summary) != {
        "audit_sha256",
        "benchmark_manifest_sha256",
        "benchmark_source_catalog_sha256",
        "benchmark_source_count",
        "benchmark_source_role_counts",
        "p01_p02_source_count",
        "exact_sha256_match_count",
        "exact_byte_identity_match_count",
        "embedded_benchmark_source_count",
        "benchmark_task_bytes_used",
        "condition_supplement_used",
        "library_or_library_path_used",
    }:
        raise BenchmarkToolError("synthetic token-canary source summary schema is invalid")
    provenance = _mapping(
        read_json(paths["synthetic_prompt_provenance"]), "synthetic prompt provenance"
    )
    _verify_self_hash(provenance, "record_sha256", "synthetic prompt provenance")
    if (
        provenance.get("kind") != "highambench-synthetic-token-canary-prompt-provenance"
        or provenance.get("computed_before_prompt_release") is not True
        or provenance.get("prompt") != prompt_record()
        or provenance.get("source_separation_audit_sha256")
        != source_audit.get("audit_sha256")
        or provenance.get("controlled_manifest_sha256")
        != sha256_file(paths["controlled_manifest"])
        or provenance.get("condition") != "N"
        or provenance.get("condition_supplement") is not None
        or provenance.get("library_paths") != []
        or provenance.get("benchmark_task_bytes_used") is not False
    ):
        raise BenchmarkToolError("synthetic token-canary prompt provenance is invalid")
    invocation = _mapping(read_json(paths["invocation"]), "synthetic canary invocation")
    _verify_self_hash(invocation, "record_sha256", "synthetic canary invocation")
    argv = invocation.get("argv")
    if not isinstance(argv, list) or not all(isinstance(item, str) for item in argv):
        raise BenchmarkToolError("synthetic token-canary invocation is malformed")
    if (
        invocation.get("kind") != "highambench-synthetic-token-canary-invocation"
        or invocation.get("prompt_protocol") != PROMPT_PROTOCOL
        or invocation.get("benchmark_task_bytes_used") is not False
        or _option_value(argv, "--condition") != "N"
        or _option_value(argv, "--task-id") != CANARY_ID
        or _option_value(argv, "--paper-id") != "SYNTHETIC"
        or _option_value(argv, "--token-limit") != str(DEFAULT_CANARY_TOKEN_LIMIT)
        or _option_value(argv, "--prompt-startup-timeout-seconds")
        != str(int(PROMPT_STARTUP_TIMEOUT_SECONDS))
        or Path(_option_value(argv, "--task-root")).resolve()
        != paths["common_prompt"].parent.resolve()
        or Path(_option_value(argv, "--controlled-manifest")).resolve()
        != paths["controlled_manifest"].resolve()
        or Path(_option_value(argv, "--usage-output")).resolve()
        != paths["usage"].resolve()
        or Path(_option_value(argv, "--raw-jsonl")).resolve()
        != paths["raw_jsonl"].resolve()
        or Path(_option_value(argv, "--output")).resolve()
        != paths["record"].resolve()
        or _option_value(argv, "--canonical-relative")
        != "task/SyntheticTarget.lean"
        or _option_value(argv, "--prompt-relative") != "task/prompt.md"
        or "--library-available" in argv
    ):
        raise BenchmarkToolError("synthetic token-canary invocation provenance is invalid")
    try:
        provider_template = json.loads(_option_value(argv, "--agent-command-json"))
    except json.JSONDecodeError as error:
        raise BenchmarkToolError("synthetic provider command is invalid JSON") from error
    if not isinstance(provider_template, list) or not all(
        isinstance(item, str) for item in provider_template
    ):
        raise BenchmarkToolError("synthetic provider command is malformed")
    _verify_provider_command(
        provider_template,
        canary_limit=DEFAULT_CANARY_TOKEN_LIMIT,
        frozen_limit=expected_frozen_token_limit,
    )
    record = _mapping(read_json(paths["record"]), "synthetic token-canary runner record")
    frozen_wrapper = _mapping(
        record.get("frozen_run_verification"), "synthetic canary frozen verification"
    )
    if (
        frozen_wrapper.get("freeze_check") != dict(runner_freeze)
        or frozen_wrapper.get("freeze_check_sha256")
        != _canonical_sha256(dict(runner_freeze))
        or record.get("environment_id") != production_freeze.get("environment_id")
        or record.get("prompt_provenance") != synthetic_prompt_provenance_record()
    ):
        raise BenchmarkToolError("synthetic token-canary runner freeze binding is invalid")
    provider_command = record.get("agent_command")
    if not isinstance(provider_command, list) or not all(
        isinstance(item, str) for item in provider_command
    ):
        raise BenchmarkToolError("synthetic token-canary record lacks its provider command")
    _verify_rendered_provider_command(
        provider_template,
        provider_command,
        usage_output=paths["usage"],
        prompt_paths={
            key: value.resolve()
            for key, value in _prompt_handshake_paths(paths["usage"].resolve()).items()
        },
        handshake_nonce=str(
            _mapping(record.get("prompt_release"), "synthetic prompt release").get(
                "handshake_nonce"
            )
        ),
        run_id=CANARY_RUN_ID,
        canary_limit=DEFAULT_CANARY_TOKEN_LIMIT,
        frozen_limit=expected_frozen_token_limit,
    )
    usage_artifact = _mapping(read_json(paths["usage"]), "synthetic canary usage")
    outcome = validate_canary_record(
        record,
        canary_limit=DEFAULT_CANARY_TOKEN_LIMIT,
        agent_log=paths["agent_log"],
        usage_artifact=usage_artifact,
    )
    outcome["prompt_release"] = authenticate_prompt_release(
        record,
        usage_artifact=usage_artifact,
        usage_path=paths["usage"],
        provider_command=provider_command,
        wall_time_seconds=wall,
    )
    if evidence.get("outcome") != outcome:
        raise BenchmarkToolError("synthetic token-canary outcome is stale")
    verified_artifacts = {
        label: {
            "path": artifacts[label]["path"],
            "sha256": artifacts[label]["sha256"],
            "bytes": paths[label].stat().st_size,
        }
        for label in ARTIFACT_LABELS
    }
    return {
        "status": "passed",
        "canary_limit_tokens": DEFAULT_CANARY_TOKEN_LIMIT,
        "first_crossing_tokens": outcome["first_crossing_tokens"],
        "final_endpoint_tokens": outcome["final_endpoint_tokens"],
        "thread_count": 1,
        "observed_child_thread_count": 0,
        "response_count": 2,
        "drain_complete": False,
        "provider_gate_quiescent": True,
        "measurement_exact": True,
        "synthetic_input": True,
        "matrix_assignment": False,
        "benchmark_task_bytes_used": False,
        "prompt_protocol": PROMPT_PROTOCOL,
        "prompt_release": outcome["prompt_release"],
        "source_separation_audit_sha256": source_audit["audit_sha256"],
        "accounting_projection": outcome["accounting_projection"],
        "artifacts": verified_artifacts,
    }


def run_canary(args: argparse.Namespace) -> int:
    if args.canary_token_limit != DEFAULT_CANARY_TOKEN_LIMIT:
        raise BenchmarkToolError(
            "synthetic token canary cap is fixed at 180000 tokens"
        )
    if args.canary_time_limit_seconds <= 0:
        raise BenchmarkToolError("synthetic token canary wall time must be positive")
    if args.reasoning_effort != "ultra" or args.model != "gpt-5.6-sol":
        raise BenchmarkToolError("synthetic token canary requires frozen Sol/Ultra")
    result_root = args.results_root.resolve()
    if result_root.exists() and any(result_root.iterdir()):
        raise BenchmarkToolError("synthetic token-canary result root must be absent or empty")
    result_root.mkdir(parents=True, exist_ok=True)
    try:
        result_root.relative_to(args.project_root.resolve())
    except ValueError as error:
        raise BenchmarkToolError("synthetic token-canary result root must be below project") from error
    for name in ("logs", "attempts", "workspaces", "hidden", "state", "base"):
        (result_root / name).mkdir()
    production_freeze = run_matrix.verify_frozen_run_environment(
        args,
        args.benchmark_root.resolve(),
        regenerating_token_control_canary=True,
    )
    if args.canary_token_limit >= args.token_limit:
        raise BenchmarkToolError("synthetic canary cap must be below benchmark cap")
    if args.canary_time_limit_seconds > args.time_limit_seconds:
        raise BenchmarkToolError("synthetic canary wall time exceeds benchmark wall time")
    inputs = result_root / "inputs"
    prompt, context, target = _write_synthetic_inputs(inputs)
    controlled_manifest = inputs / "controlled.json"
    write_json(
        controlled_manifest,
        create_manifest(
            inputs,
            requested=["prompt.md", "context.md", "SyntheticTarget.lean"],
            label="synthetic-token-control-canary",
        ),
    )
    if codex_isolated.build_prompt(prompt, context, target) != synthetic_effective_prompt():
        raise BenchmarkToolError("synthetic token-canary prompt composition drifted")
    benchmark_manifest = _mapping(
        read_json(args.benchmark_root / "metadata" / "manifest.json"),
        "benchmark manifest",
    )
    source_separation = audit_benchmark_source_separation(
        project_root=args.project_root,
        benchmark_root=args.benchmark_root,
        manifest=benchmark_manifest,
        generated_sources={
            "common_prompt": prompt.read_bytes(),
            "context": context.read_bytes(),
            "synthetic_target": target.read_bytes(),
            "effective_prompt": synthetic_effective_prompt().encode("utf-8"),
        },
    )
    source_audit_path = result_root / "logs" / "benchmark_source_audit.json"
    write_json(source_audit_path, source_separation)
    prompt_provenance = _self_hashed(
        {
            "schema_version": 1,
            "kind": "highambench-synthetic-token-canary-prompt-provenance",
            "computed_before_prompt_release": True,
            "prompt": prompt_record(),
            "source_separation_audit_sha256": source_separation["audit_sha256"],
            "controlled_manifest_sha256": sha256_file(controlled_manifest),
            "condition": "N",
            "condition_supplement": None,
            "library_paths": [],
            "benchmark_task_bytes_used": False,
        }
    )
    prompt_provenance_path = result_root / "logs" / "synthetic_prompt_provenance.json"
    write_json(prompt_provenance_path, prompt_provenance)
    freeze_path = result_root / "logs" / "freeze_check.json"
    runner_freeze_path = result_root / "logs" / "runner_freeze_check.json"
    write_json(freeze_path, production_freeze)
    runner_freeze = _runner_freeze_record(production_freeze)
    write_json(runner_freeze_path, runner_freeze)
    usage_output = result_root / "logs" / "synthetic_token_control.usage.json"
    runner_record = result_root / "attempts" / "synthetic_token_control.record.json"
    raw_jsonl = result_root / "attempts" / "synthetic_token_control.record.jsonl"
    command = _runner_command(
        args,
        result_root=result_root,
        task_root=inputs,
        controlled_manifest=controlled_manifest,
        runner_freeze_check=runner_freeze,
        usage_output=usage_output,
        runner_record=runner_record,
        raw_jsonl=raw_jsonl,
        state_parent=result_root / "state",
    )
    provider_template = json.loads(_option_value(command, "--agent-command-json"))
    if not isinstance(provider_template, list):
        raise BenchmarkToolError("synthetic provider command template is malformed")
    _verify_provider_command(
        provider_template,
        canary_limit=args.canary_token_limit,
        frozen_limit=args.token_limit,
    )
    invocation_path = result_root / "logs" / "invocation.json"
    write_json(
        invocation_path,
        _self_hashed(
            {
                "schema_version": 1,
                "kind": "highambench-synthetic-token-canary-invocation",
                "argv": command,
                "prompt_protocol": PROMPT_PROTOCOL,
                "prompt_provenance_sha256": sha256_file(prompt_provenance_path),
                "benchmark_source_audit_sha256": sha256_file(source_audit_path),
                "benchmark_task_bytes_used": False,
                "provider_input_role": "synthetic_prompt_context_target_only",
            }
        ),
    )
    try:
        completed = subprocess.run(
            command,
            cwd=args.project_root.resolve(),
            check=False,
            timeout=args.canary_time_limit_seconds + 180,
        )
    except subprocess.TimeoutExpired as error:
        raise BenchmarkToolError("synthetic token-canary runner timed out") from error
    if completed.returncode != 1:
        raise BenchmarkToolError(
            f"synthetic token-canary runner exited {completed.returncode}, expected TOKEN_LIMIT exit 1"
        )
    if not runner_record.is_file() or not usage_output.is_file():
        raise BenchmarkToolError("synthetic token-canary runner omitted its record/usage")
    record = _mapping(read_json(runner_record), "synthetic token-canary record")
    agent_log = Path(str(record.get("agent_log", ""))).resolve()
    if not agent_log.is_file():
        raise BenchmarkToolError("synthetic token-canary runner omitted its agent log")
    usage = _mapping(read_json(usage_output), "synthetic token-canary usage")
    outcome = validate_canary_record(
        record,
        canary_limit=args.canary_token_limit,
        agent_log=agent_log,
        usage_artifact=usage,
    )
    rendered_provider = record.get("agent_command")
    if not isinstance(rendered_provider, list) or not all(
        isinstance(item, str) for item in rendered_provider
    ):
        raise BenchmarkToolError("synthetic token-canary record lacks provider argv")
    prompt_release = _mapping(
        record.get("prompt_release"), "synthetic prompt release"
    )
    prompt_paths = {
        key: value.resolve()
        for key, value in _prompt_handshake_paths(usage_output.resolve()).items()
    }
    _verify_rendered_provider_command(
        provider_template,
        rendered_provider,
        usage_output=usage_output,
        prompt_paths=prompt_paths,
        handshake_nonce=str(prompt_release.get("handshake_nonce")),
        run_id=CANARY_RUN_ID,
        canary_limit=args.canary_token_limit,
        frozen_limit=args.token_limit,
    )
    outcome["prompt_release"] = authenticate_prompt_release(
        record,
        usage_artifact=usage,
        usage_path=usage_output,
        provider_command=rendered_provider,
        wall_time_seconds=args.canary_time_limit_seconds,
    )
    paths = {
        "record": runner_record,
        "agent_log": agent_log,
        "usage": usage_output,
        "raw_jsonl": raw_jsonl,
        "common_prompt": prompt,
        "context": context,
        "synthetic_target": target,
        "controlled_manifest": controlled_manifest,
        "benchmark_source_audit": source_audit_path,
        "synthetic_prompt_provenance": prompt_provenance_path,
        "freeze_check": freeze_path,
        "runner_freeze_check": runner_freeze_path,
        "invocation": invocation_path,
        "provider_gate": runner.provider_gate_paths(usage_output.resolve())["final"],
    }
    evidence = build_attestation(
        production_freeze_check=production_freeze,
        runner_freeze_check=runner_freeze,
        frozen_token_limit=args.token_limit,
        canary_token_limit=args.canary_token_limit,
        canary_time_limit_seconds=args.canary_time_limit_seconds,
        result_root=result_root,
        project_root=args.project_root,
        paths=paths,
        outcome=outcome,
        source_separation=source_separation,
    )
    validate_attestation_document(
        evidence,
        project_root=args.project_root,
        expected_benchmark_id=str(production_freeze.get("benchmark_id")),
        expected_agent=_attestation_agent(production_freeze),
        expected_frozen_token_limit=args.token_limit,
    )
    evidence_output = result_root / "token_control_canary_attestation.json"
    write_json(evidence_output, evidence)
    print(
        "HighamBench private synthetic token-control canary passed: "
        f"crossed and was quarantined at {outcome['final_endpoint_tokens']} tokens; "
        "no benchmark task bytes were used"
    )
    print(f"Attestation: {evidence_output}")
    return 0


def make_parser() -> argparse.ArgumentParser:
    parser = run_matrix.make_parser()
    parser.description = __doc__
    parser.add_argument(
        "--canary-token-limit", type=int, default=DEFAULT_CANARY_TOKEN_LIMIT
    )
    parser.add_argument(
        "--canary-time-limit-seconds",
        type=int,
        default=DEFAULT_CANARY_TIME_LIMIT_SECONDS,
    )
    parser.add_argument(
        "--verify-only",
        type=Path,
        metavar="EVIDENCE_JSON",
        help="authenticate frozen synthetic evidence without contacting the provider",
    )
    return parser


def _verify_only(args: argparse.Namespace) -> int:
    freeze = run_matrix.verify_frozen_run_environment(
        args,
        args.benchmark_root.resolve(),
        regenerating_token_control_canary=True,
    )
    evidence = _mapping(read_json(args.verify_only), "synthetic token-canary evidence")
    summary = validate_attestation_document(
        evidence,
        project_root=args.project_root,
        expected_benchmark_id=str(freeze.get("benchmark_id")),
        expected_agent=_attestation_agent(freeze),
        expected_frozen_token_limit=args.token_limit,
    )
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


def main(argv: Sequence[str] | None = None) -> int:
    try:
        args = make_parser().parse_args(argv)
        return _verify_only(args) if args.verify_only is not None else run_canary(args)
    except (OSError, BenchmarkToolError, ValueError) as error:
        print(f"synthetic token-control canary error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
