#!/usr/bin/env python3
"""Run one fresh Codex proof attempt inside a curated bubblewrap filesystem.

The Codex control process needs provider network access.  Model-generated shell
commands are launched through ``offline_shell.c``.  That launcher installs a
kernel seccomp rule that denies socket operations and is inherited by every
command descendant.  The outer filesystem contains only system programs, the
frozen Lean toolchain, mathlib, the task workspace, and (for condition L)
NumStability.  Codex's own nested filesystem sandbox is disabled because nested
user namespaces are unavailable inside the outer bubblewrap namespace; the
outer namespace supplies the filesystem boundary instead.

Authentication is copied into a fresh temporary Codex state directory only for
startup.  It is removed after ``thread/start`` succeeds and before the adapter
sends ``turn/start``, so the model cannot issue a shell command while the copied
credential exists.

The adapter speaks the app-server JSONL protocol directly instead of using
``codex exec --json``.  For the Ultra treatment, exact usage from every
``rawResponse/completed`` notification is deduplicated and summed over the
rooted coordinator/subagent thread tree.  Per-thread cumulative usage is never
summed; instead it proves raw-event completeness against a fork-derived
baseline.  The pinned V2 runtime binds a successful raw ``spawn_agent`` call to
``subAgentActivity`` by equal call/item ID.  A no-history child has a zero
baseline, while a full-history child inherits the parent's exact usage before
the spawn response.  Any unexplained cumulative residual therefore fails
closed instead of being accepted as an arbitrary inherited baseline.
Ultra proof acceptance uses a protected dynamic ``submit_proof`` call reached
through one exact trusted ``exec`` program.  The adapter binds the outer raw
item and provider response to the separately observed inner dynamic call.  The
inner call snapshots fixed ``Candidate.lean``, remains unanswered while the
trusted runner validates the bytes, and is never resolved on acceptance.

The runner also supplies a fresh marker file.  The offline shell appends to it
whenever the kernel blocks a socket-related system call, so the outer runner can
reject an attempt even if that attempt later writes a valid proof.
"""

from __future__ import annotations

import argparse
import contextlib
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import queue
import re
import signal
import shutil
import stat
import subprocess
import sys
import tempfile
import threading
import time
from typing import Any, Callable, Iterable, Mapping, TextIO
from urllib.parse import urlsplit

try:
    from .provider_token_gate import (
        CLOSE_REASON_ACCEPTED_SUBMISSION,
        CLOSE_REASON_NATURAL_END,
        CLOSE_REASON_SYSTEM_ERROR,
        CLOSE_REASON_TOKEN_LIMIT,
        DEFAULT_RESPONSE_BOUND,
        PHASE_EXCLUSIVE,
        PHASE_POISONED,
        PROVIDER_GATE_FINAL_SUFFIX,
        PROVIDER_GATE_LIVE_SUFFIX,
        RELEASE_SANITIZED_COMPACTION_CROSSING,
        ProviderTokenGate,
        provider_gate_artifact_path,
        provider_gate_live_path,
        validate_artifact as validate_provider_gate_artifact,
    )
except ImportError:  # pragma: no cover - direct script execution
    from provider_token_gate import (  # type: ignore
        CLOSE_REASON_ACCEPTED_SUBMISSION,
        CLOSE_REASON_NATURAL_END,
        CLOSE_REASON_SYSTEM_ERROR,
        CLOSE_REASON_TOKEN_LIMIT,
        DEFAULT_RESPONSE_BOUND,
        PHASE_EXCLUSIVE,
        PHASE_POISONED,
        PROVIDER_GATE_FINAL_SUFFIX,
        PROVIDER_GATE_LIVE_SUFFIX,
        RELEASE_SANITIZED_COMPACTION_CROSSING,
        ProviderTokenGate,
        provider_gate_artifact_path,
        provider_gate_live_path,
        validate_artifact as validate_provider_gate_artifact,
    )


DISABLED_FEATURES = (
    "apps",
    "browser_use",
    "computer_use",
    "external_agent_memory_import",
    "goals",
    "image_generation",
    "memories",
    "plugins",
    "remote_plugin",
    "skill_search",
    "standalone_web_search",
)

NETWORK_VIOLATION_MARKER_ENV = "HIGHAMBENCH_NETWORK_VIOLATION_MARKER"
INITIALIZE_REQUEST_ID = 1
THREAD_START_REQUEST_ID = 2
TURN_START_REQUEST_ID = 3
THREAD_COMPACT_REQUEST_ID = 4
PROVIDER_GATE_COMPACTION_CANARY_TIMEOUT_SECONDS = 180.0
APP_SERVER_CLIENT_NAME = "highambench-isolated"
APP_SERVER_CLIENT_VERSION = "1"
PROMPT_RELEASE_SCHEMA_VERSION = 1
PROMPT_RELEASE_PROTOCOL_VERSION = "highambench-prompt-release-v1"
PROMPT_RELEASE_ADAPTER_NAME = "codex_isolated.py"
PROMPT_RELEASE_ADAPTER_VERSION = "1"
PROMPT_READY_KIND = "highambench_prompt_ready"
PROMPT_GO_KIND = "highambench_prompt_go"
PROMPT_RELEASED_KIND = "highambench_prompt_released"
PROMPT_READY_SUFFIX = ".prompt-ready.json"
STATE_CLEANUP_ATTEMPTS = 5
STATE_CLEANUP_RETRY_SECONDS = 0.1
PROMPT_GO_SUFFIX = ".prompt-go.json"
PROMPT_RELEASE_SUFFIX = ".prompt-release.json"
PROMPT_HANDSHAKE_POLL_SECONDS = 0.01
MAX_PROMPT_HANDSHAKE_BYTES = 64 * 1024
TOKEN_USAGE_MEASUREMENT_SOURCE = "codex_app_server_thread/tokenUsage/updated"
ULTRA_USAGE_MEASUREMENT_SOURCE = "codex_app_server_rawResponse/completed"
ULTRA_USAGE_NOTIFICATION = "rawResponse/completed"
ULTRA_USAGE_SCOPE = "rooted_attempt_thread_tree_completed_responses"
ULTRA_REASONING_EFFORT = "ultra"
ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION = 6
PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION = 3
APP_SERVER_EVENT_TIME_RESOLUTION_NS = 1_000_000
# This is the runner's operational provider-gate cleanup envelope, not an
# upstream-response completeness bound.  Expiry leaves the lifecycle
# unreconciled so terminal close/finalization still fails closed.
EXPLICIT_CHILD_INTERRUPT_RECONCILIATION_GRACE_SECONDS = 45.0
EXPLICIT_CHILD_INTERRUPT_RECONCILIATION_POLL_SECONDS = 0.01
PROVIDER_USAGE_RECONCILIATION_KEYS = frozenset(
    {
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
)
COLLABORATION_MESSAGE_EVIDENCE_KEYS = frozenset(
    {
        "item_id",
        "item_sha256",
        "author",
        "recipient",
        "observed_at_unix_ns",
        "observed_at_monotonic_ns",
    }
)
SUPERSEDED_BY_COLLABORATION_MESSAGE_EVIDENCE_KEYS = frozenset(
    {
        "response_id",
        "provider_call_id",
        "thread_id",
        "turn_id",
        "successor_response_id",
        "successor_call_id",
        "collaboration_messages",
    }
)
DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_EVIDENCE_KEYS = frozenset(
    {
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
)
SUPPRESSED_COLLABORATION_WAIT_EVIDENCE_KEYS = frozenset(
    {
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
)
PROVIDER_RESPONSE_TOKEN_BOUND = DEFAULT_RESPONSE_BOUND
PROVIDER_GATE_PROVIDER_ID = "highambench_token_gate"
PROVIDER_GATE_CLOSE_TOKEN_LIMIT = CLOSE_REASON_TOKEN_LIMIT
PROVIDER_GATE_CLOSE_ACCEPTED_SUBMISSION = CLOSE_REASON_ACCEPTED_SUBMISSION
PROVIDER_GATE_CLOSE_NATURAL_END = CLOSE_REASON_NATURAL_END
PROVIDER_GATE_CLOSE_SYSTEM_ERROR = CLOSE_REASON_SYSTEM_ERROR
ULTRA_ADAPTER_TEARDOWN_KEYS = frozenset(
    {
        "process_group_isolated",
        "immediate",
        "stdin_closed",
        "signal",
        "returncode",
        "completed",
        "started_at_unix_ns",
        "started_at_monotonic_ns",
        "completed_at_unix_ns",
        "completed_at_monotonic_ns",
    }
)
ULTRA_FORK_POLICY_SCHEMA_VERSION = 1
ULTRA_FORK_POLICY_ENFORCEMENT = "codex_pre_tool_use_command_hook_v1"
ULTRA_FORK_POLICY_HOOK_NOTIFICATION = "hook/completed"
ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION = "hook/started"
ULTRA_FORK_POLICY_HOOK_EVENT_NAME = "preToolUse"
ULTRA_FORK_POLICY_MATCHER = "^(Agent|spawn_agent|collaborationspawn_agent)$"
ULTRA_FORK_POLICY_SOURCE = "user"
ULTRA_FORK_POLICY_EXECUTION_MODE = "sync"
ULTRA_FORK_POLICY_HANDLER_TYPE = "command"
ULTRA_FORK_POLICY_SCOPE = "turn"
ULTRA_FORK_POLICY_DISPLAY_ORDER = 0
ULTRA_FORK_POLICY_HELPER_FILENAME = "highambench-ultra-fork-policy.py"
ULTRA_FORK_POLICY_HOOKS_FILENAME = "hooks.json"
ULTRA_FORK_POLICY_TIMEOUT_SECONDS = 5
ULTRA_FORK_POLICY_TRUST_BYPASS_CLI_FLAG = "--dangerously-bypass-hook-trust"
ULTRA_FORK_POLICY_TRUST_BYPASS_CONFIG_KEY = "bypass_hook_trust"
ULTRA_FORK_POLICY_TRUST_BYPASS_EFFECTIVE_SOURCE = "thread_start_config"
ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE = (
    'fork_turns for call {call_id} must be omitted or set to "all" or "none".'
)
ULTRA_FORK_USAGE_HINT = (
    'For spawn_agent, omit fork_turns (defaults to "all") or set it to exactly '
    '"all" or "none"; positive integers and all other values are unavailable.'
)
ULTRA_FORK_POLICY_ALLOWED_FORK_TURNS = ("omitted", "all", "none")
ULTRA_FORK_POLICY_ALLOW_STATUS = "completed"
ULTRA_FORK_POLICY_BLOCK_STATUS = "blocked"
ULTRA_FORK_POLICY_ALLOW_DECISION = "allow"
ULTRA_FORK_POLICY_BLOCK_DECISION = "block"
ULTRA_FORK_POLICY_AWAITING_HOOK_STATUS = "awaiting_hook_evidence"
ULTRA_FORK_POLICY_ALLOWED_RESOLUTION_STATUS = "hook_allowed_awaiting_spawn"
ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS = "policy_blocked_without_child"
ULTRA_FORK_POLICY_INVALID_RESOLUTION_STATUS = "invalid_hook_evidence"
ULTRA_SPAWN_AGENT_THREAD_LIMIT_FAILURE_KIND = "agent_thread_limit_reached"
ULTRA_SPAWN_AGENT_THREAD_LIMIT_FAILURE_OUTPUT = (
    "collab spawn failed: agent thread limit reached"
)
ULTRA_FORK_POLICY_HELPER_SOURCE = '''#!/usr/bin/python3.10
import json
import re
import sys

REASON_TEMPLATE = 'fork_turns for call {call_id} must be omitted or set to "all" or "none".'


def deny(call_id):
    reason = REASON_TEMPLATE.format(call_id=call_id)
    output = {
        "hookSpecificOutput": {
            "hookEventName": "PreToolUse",
            "permissionDecision": "deny",
            "permissionDecisionReason": reason,
        }
    }
    sys.stdout.write(json.dumps(output, sort_keys=True, separators=(",", ":")) + "\\n")


def main():
    try:
        request = json.load(sys.stdin)
    except (json.JSONDecodeError, OSError, TypeError, ValueError):
        deny("unknown")
        return
    if not isinstance(request, dict):
        deny("unknown")
        return
    call_id = request.get("tool_use_id")
    tool_input = request.get("tool_input")
    if (
        request.get("hook_event_name") != "PreToolUse"
        or request.get("tool_name")
        not in ("Agent", "spawn_agent", "collaborationspawn_agent")
        or not isinstance(call_id, str)
        or re.fullmatch(r"call_[A-Za-z0-9_-]{1,120}", call_id) is None
        or not isinstance(tool_input, dict)
    ):
        deny("unknown")
        return
    if (
        "fork_turns" not in tool_input or tool_input["fork_turns"] in ("all", "none")
    ):
        return
    deny(call_id)


if __name__ == "__main__":
    main()
'''
ULTRA_FORK_POLICY_HELPER_SHA256 = hashlib.sha256(
    ULTRA_FORK_POLICY_HELPER_SOURCE.encode("utf-8")
).hexdigest()
ULTRA_FORK_USAGE_HINT_SHA256 = hashlib.sha256(
    ULTRA_FORK_USAGE_HINT.encode("utf-8")
).hexdigest()
INTERRUPT_REQUEST_ID_START = 1000
SUBMISSION_TOOL_NAME = "submit_proof"
SUBMISSION_BARRIER_SCHEMA_VERSION = 5
SUBMISSION_REQUEST_SUFFIX = ".submission-request.json"
SUBMISSION_ACK_SUFFIX = ".submission-ack.json"
SUBMISSION_CALL_SUFFIX = ".submission-call.json"
SUBMISSION_CHALLENGE_SUFFIX = ".submission-challenge.json"
SUBMISSION_SNAPSHOT_SUFFIX = ".submission-{sequence}.lean"
MAX_SUBMISSION_BYTES = 4 * 1024 * 1024
MAX_REJECTION_NOTE_BYTES = 2048
SUBMISSION_ACK_POLL_SECONDS = 0.02
NESTED_SUBMISSION_WIRE_FORMAT = "functions_exec_dynamic_submit_proof_v3"
NESTED_SUBMISSION_EXEC_YIELD_TIME_MS = 2_400_000
NESTED_SUBMISSION_EXEC_YIELD_ENVELOPE_BASIS = (
    "prompt_release_wall_clock_plus_post_submission_validation_reserve"
)
NESTED_SUBMISSION_EXEC_YIELD_ATTEMPT_WALL_SECONDS = 1_800
NESTED_SUBMISSION_EXEC_YIELD_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS = 369
NESTED_SUBMISSION_EXEC_YIELD_ENVELOPE_MS = 1_000 * (
    NESTED_SUBMISSION_EXEC_YIELD_ATTEMPT_WALL_SECONDS
    + NESTED_SUBMISSION_EXEC_YIELD_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS
)
NESTED_SUBMISSION_EXEC_YIELD_MARGIN_MS = (
    NESTED_SUBMISSION_EXEC_YIELD_TIME_MS
    - NESTED_SUBMISSION_EXEC_YIELD_ENVELOPE_MS
)
NESTED_SUBMISSION_EXEC_SOURCE = (
    '// @exec: {"yield_time_ms": 2400000}\n'
    'text(await tools.submit_proof({candidate_path:"Candidate.lean"}));\n'
)
NESTED_SUBMISSION_EXEC_SOURCE_BYTES = 104
NESTED_SUBMISSION_EXEC_SOURCE_SHA256 = (
    "d8f1e2e53f379a5e1a0cd273127af52f71c150c9fa7c7a50dc177d40e6c12d14"
)
SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE = (
    "inner_dynamic_call_before_raw_response_completed"
)
SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER = (
    "raw_response_completed_before_inner_dynamic_call"
)


def _ultra_fork_policy_paths(inside_home: str) -> tuple[str, str]:
    """Return the two immutable in-namespace policy artifact paths."""

    normalized_home = str(PurePosixPath(inside_home))
    if not normalized_home.startswith("/") or normalized_home == "/":
        raise RuntimeError("inside home must be a specific absolute path")
    codex_home = PurePosixPath(normalized_home) / ".codex"
    return (
        str(codex_home / ULTRA_FORK_POLICY_HOOKS_FILENAME),
        str(codex_home / ULTRA_FORK_POLICY_HELPER_FILENAME),
    )


def _ultra_fork_policy_hooks_bytes(inside_home: str) -> bytes:
    hooks_path, helper_path = _ultra_fork_policy_paths(inside_home)
    del hooks_path
    value = {
        "hooks": {
            "PreToolUse": [
                {
                    "matcher": ULTRA_FORK_POLICY_MATCHER,
                    "hooks": [
                        {
                            "type": "command",
                            "command": f"/usr/bin/python3.10 {helper_path}",
                            "timeout": ULTRA_FORK_POLICY_TIMEOUT_SECONDS,
                        }
                    ],
                }
            ]
        }
    }
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")


def ultra_fork_policy_static_record(
    inside_home: str = "/u501/m2fetrat",
) -> dict[str, Any]:
    """Return the one public frozen policy record shared by all auditors."""

    source_path, helper_path = _ultra_fork_policy_paths(inside_home)
    hooks_bytes = _ultra_fork_policy_hooks_bytes(inside_home)
    return {
        "schema_version": ULTRA_FORK_POLICY_SCHEMA_VERSION,
        "enforcement": ULTRA_FORK_POLICY_ENFORCEMENT,
        "hook_notification": ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
        "hook_event_name": ULTRA_FORK_POLICY_HOOK_EVENT_NAME,
        "matcher": ULTRA_FORK_POLICY_MATCHER,
        "source": ULTRA_FORK_POLICY_SOURCE,
        "source_path": source_path,
        "execution_mode": ULTRA_FORK_POLICY_EXECUTION_MODE,
        "handler_type": ULTRA_FORK_POLICY_HANDLER_TYPE,
        "scope": ULTRA_FORK_POLICY_SCOPE,
        "display_order": ULTRA_FORK_POLICY_DISPLAY_ORDER,
        "command": f"/usr/bin/python3.10 {helper_path}",
        "helper_filename": ULTRA_FORK_POLICY_HELPER_FILENAME,
        "helper_sha256": ULTRA_FORK_POLICY_HELPER_SHA256,
        "hooks_json_sha256": hashlib.sha256(hooks_bytes).hexdigest(),
        "block_reason_template": ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE,
        "usage_hint": ULTRA_FORK_USAGE_HINT,
        "usage_hint_sha256": ULTRA_FORK_USAGE_HINT_SHA256,
        "hook_trust_bypass_cli_flag_present": True,
        "hook_trust_bypass_thread_config": {
            ULTRA_FORK_POLICY_TRUST_BYPASS_CONFIG_KEY: True,
        },
        "hook_trust_bypass_effective_source": (
            ULTRA_FORK_POLICY_TRUST_BYPASS_EFFECTIVE_SOURCE
        ),
        "allowed_fork_turns": list(ULTRA_FORK_POLICY_ALLOWED_FORK_TURNS),
        "positive_integer_fork_turns_allowed": False,
    }


def _write_frozen_policy_file(path: Path, payload: bytes, mode: int) -> None:
    """Create or authenticate one deterministic policy file without replacement."""

    path.parent.mkdir(parents=True, exist_ok=True)
    if path.exists() or path.is_symlink():
        if path.is_symlink() or not path.is_file() or path.read_bytes() != payload:
            raise RuntimeError("temporary Ultra fork-policy artifact is not exact")
        if stat.S_IMODE(path.stat().st_mode) != mode:
            raise RuntimeError("temporary Ultra fork-policy artifact has the wrong mode")
        return
    descriptor = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC, mode)
    try:
        offset = 0
        while offset < len(payload):
            written = os.write(descriptor, payload[offset:])
            if written <= 0:
                raise RuntimeError("could not write Ultra fork-policy artifact")
            offset += written
        os.fsync(descriptor)
        os.fchmod(descriptor, mode)
    finally:
        os.close(descriptor)


def _prepare_ultra_fork_policy(
    state_root: Path, inside_home: str
) -> tuple[Path, Path, dict[str, Any]]:
    """Generate the trusted hook outside writable HOME and attest exact bytes."""

    policy_dir = state_root / "policy"
    policy_dir.mkdir(mode=0o700, parents=False, exist_ok=True)
    hooks_path = policy_dir / ULTRA_FORK_POLICY_HOOKS_FILENAME
    helper_path = policy_dir / ULTRA_FORK_POLICY_HELPER_FILENAME
    hooks_bytes = _ultra_fork_policy_hooks_bytes(inside_home)
    helper_bytes = ULTRA_FORK_POLICY_HELPER_SOURCE.encode("utf-8")
    _write_frozen_policy_file(hooks_path, hooks_bytes, 0o444)
    _write_frozen_policy_file(helper_path, helper_bytes, 0o555)
    record = ultra_fork_policy_static_record(inside_home)
    if hashlib.sha256(hooks_path.read_bytes()).hexdigest() != record["hooks_json_sha256"]:
        raise RuntimeError("temporary Ultra hooks.json hash mismatch")
    if hashlib.sha256(helper_path.read_bytes()).hexdigest() != record["helper_sha256"]:
        raise RuntimeError("temporary Ultra fork-policy helper hash mismatch")
    return hooks_path, helper_path, record


class _TokenLimitReached(Exception):
    """Stop after persisting the first provider notification at or above the cap."""


class _SubmissionAccepted(Exception):
    """End the app-server without resolving an accepted dynamic tool call."""


def submission_barrier_paths(usage_output: Path, sequence: int | None = None) -> dict[str, Path]:
    """Derive runner-owned barrier artifacts from the protected usage path."""

    base = str(usage_output)
    result = {
        "request": Path(base + SUBMISSION_REQUEST_SUFFIX),
        "ack": Path(base + SUBMISSION_ACK_SUFFIX),
        "call": Path(base + SUBMISSION_CALL_SUFFIX),
        "challenge": Path(base + SUBMISSION_CHALLENGE_SUFFIX),
    }
    if sequence is not None:
        if sequence <= 0:
            raise RuntimeError("submission sequence must be positive")
        result["snapshot"] = Path(
            base + SUBMISSION_SNAPSHOT_SUFFIX.format(sequence=sequence)
        )
    return result


def prompt_handshake_paths(usage_output: Path) -> dict[str, Path]:
    """Derive the three trusted prompt-release artifacts from one usage path."""

    name = usage_output.name
    suffix = ".usage.json"
    base = name[: -len(suffix)] if name.endswith(suffix) else usage_output.stem
    if not base or base in (".", ".."):
        raise RuntimeError("usage output cannot derive a prompt-handshake name")
    return {
        "ready": usage_output.parent / f"{base}{PROMPT_READY_SUFFIX}",
        "go": usage_output.parent / f"{base}{PROMPT_GO_SUFFIX}",
        "release": usage_output.parent / f"{base}{PROMPT_RELEASE_SUFFIX}",
    }


def provider_gate_paths(usage_output: Path) -> dict[str, Path]:
    """Derive the trusted live and sealed provider-gate artifacts."""

    return {
        "live": provider_gate_live_path(usage_output),
        "final": provider_gate_artifact_path(usage_output),
    }


def _provider_gate_state_view(snapshot: Mapping[str, Any]) -> Mapping[str, Any]:
    """Accept the public state view from either a live record or direct snapshot."""

    state = snapshot.get("state")
    return state if isinstance(state, Mapping) else snapshot


def _validated_provider_gate_paths(
    args: argparse.Namespace, workspace: Path, usage_output: Path
) -> dict[str, Path]:
    """Authenticate the runner-selected gate paths before opening a socket."""

    expected = provider_gate_paths(usage_output)
    supplied = {
        "live": getattr(args, "provider_gate_live_output", None),
        "final": getattr(args, "provider_gate_output", None),
    }
    if any(not isinstance(path, Path) for path in supplied.values()):
        raise RuntimeError("both provider-gate output paths are required for Ultra")
    trusted_parent = usage_output.parent.resolve(strict=True)
    resolved: dict[str, Path] = {}
    for label, raw in supplied.items():
        assert isinstance(raw, Path)
        if not raw.is_absolute():
            raise RuntimeError(f"provider-gate {label} output must be absolute")
        if raw.parent.resolve(strict=True) != trusted_parent:
            raise RuntimeError(
                f"provider-gate {label} output must be a direct child of trusted logs"
            )
        if raw != expected[label]:
            raise RuntimeError(
                f"provider-gate {label} output does not match the usage-bound path"
            )
        try:
            raw.lstat()
        except FileNotFoundError:
            pass
        else:
            raise RuntimeError(f"provider-gate {label} artifact already exists")
        try:
            raw.relative_to(workspace)
        except ValueError:
            pass
        else:
            raise RuntimeError(
                f"provider-gate {label} artifact must be outside the model workspace"
            )
        resolved[label] = raw
    if len(set(resolved.values())) != 2 or usage_output in resolved.values():
        raise RuntimeError("provider-gate artifacts are not distinct")
    return resolved


def canonical_record_sha256(value: Mapping[str, Any], hash_field: str) -> str:
    """Hash a JSON record while excluding its self-authentication field."""

    unsigned = {key: item for key, item in value.items() if key != hash_field}
    encoded = json.dumps(
        unsigned, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def authenticated_record(value: Mapping[str, Any], hash_field: str) -> dict[str, Any]:
    """Return a copy with a canonical self-hash."""

    result = dict(value)
    result[hash_field] = canonical_record_sha256(result, hash_field)
    return result


def verify_authenticated_record(value: Any, hash_field: str) -> dict[str, Any]:
    """Fail closed on malformed, stale, or tampered runner/adapter records."""

    if not isinstance(value, Mapping):
        raise RuntimeError("submission barrier record is not a JSON object")
    digest = value.get(hash_field)
    if not isinstance(digest, str) or not re.fullmatch(r"[0-9a-f]{64}", digest):
        raise RuntimeError("submission barrier record lacks a valid self-hash")
    if canonical_record_sha256(value, hash_field) != digest:
        raise RuntimeError("submission barrier record self-hash mismatch")
    return dict(value)


def _write_json_exclusive(path: Path, value: Mapping[str, Any]) -> None:
    """Publish a protected record without overwriting a stale artifact."""

    path.parent.mkdir(parents=True, exist_ok=True)
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC
    descriptor = os.open(path, flags, 0o600)
    try:
        payload = (
            json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
            + "\n"
        ).encode("utf-8")
        offset = 0
        while offset < len(payload):
            offset += os.write(descriptor, payload[offset:])
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def _write_json_atomic_exclusive(path: Path, value: Mapping[str, Any]) -> None:
    """Atomically publish a complete regular JSON file without replacement."""

    payload = (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")
    if len(payload) > MAX_PROMPT_HANDSHAKE_BYTES:
        raise RuntimeError("prompt-handshake record is unexpectedly large")
    descriptor, temporary_name = tempfile.mkstemp(
        prefix=f".{path.name}.", suffix=".tmp", dir=path.parent
    )
    temporary = Path(temporary_name)
    try:
        os.fchmod(descriptor, 0o600)
        offset = 0
        while offset < len(payload):
            written = os.write(descriptor, payload[offset:])
            if written <= 0:
                raise RuntimeError("could not write prompt-handshake record")
            offset += written
        os.fsync(descriptor)
        os.close(descriptor)
        descriptor = -1
        # A hard-link publishes the already-complete inode atomically and, unlike
        # os.replace(), fails if a stale path or symlink appeared in the race.
        os.link(temporary, path, follow_symlinks=False)
        os.chmod(path, 0o444, follow_symlinks=False)
        directory = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    finally:
        if descriptor >= 0:
            os.close(descriptor)
        temporary.unlink(missing_ok=True)


def write_authenticated_record_atomic(
    path: Path, value: Mapping[str, Any], hash_field: str
) -> dict[str, Any]:
    """Self-hash and atomically publish a trusted handshake record."""

    record = authenticated_record(value, hash_field)
    _write_json_atomic_exclusive(path, record)
    return record


def read_authenticated_record_file(path: Path, hash_field: str) -> dict[str, Any]:
    """Read one bounded regular non-symlink authenticated record."""

    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(path, flags)
    try:
        details = os.fstat(descriptor)
        if not stat.S_ISREG(details.st_mode):
            raise RuntimeError("prompt-handshake artifact is not a regular file")
        if details.st_size <= 0 or details.st_size > MAX_PROMPT_HANDSHAKE_BYTES:
            raise RuntimeError("prompt-handshake artifact has an invalid size")
        chunks: list[bytes] = []
        remaining = details.st_size + 1
        while remaining > 0:
            chunk = os.read(descriptor, min(remaining, 65536))
            if not chunk:
                break
            chunks.append(chunk)
            remaining -= len(chunk)
        payload = b"".join(chunks)
        if len(payload) != details.st_size:
            raise RuntimeError("prompt-handshake artifact changed while being read")
    finally:
        os.close(descriptor)
    try:
        raw = json.loads(payload.decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise RuntimeError("prompt-handshake artifact is not canonical JSON") from error
    record = verify_authenticated_record(raw, hash_field)
    canonical = (
        json.dumps(record, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")
    if payload != canonical:
        raise RuntimeError("prompt-handshake artifact is not canonically encoded")
    return record


def _bounded_tool_note(note: str) -> str:
    encoded = note.encode("utf-8", errors="replace")[:MAX_REJECTION_NOTE_BYTES]
    return encoded.decode("utf-8", errors="ignore") or "submission rejected"


def _dynamic_tool_response(
    stream: TextIO, request_id: Any, *, success: bool, note: str
) -> None:
    _write_protocol_message(
        stream,
        {
            "id": request_id,
            "result": {
                "contentItems": [
                    {"type": "inputText", "text": _bounded_tool_note(note)}
                ],
                "success": success,
            },
        },
    )


def _safe_candidate_bytes(workspace: Path, raw_path: Any) -> tuple[str, bytes]:
    """Read a stable regular candidate without following any symlink."""

    if not isinstance(raw_path, str) or not raw_path or len(raw_path) > 512:
        raise RuntimeError("candidate_path must be a nonempty relative UTF-8 path")
    if "\x00" in raw_path or "\\" in raw_path:
        raise RuntimeError("candidate_path must use safe POSIX path syntax")
    relative = PurePosixPath(raw_path)
    if (
        relative.is_absolute()
        or raw_path != relative.as_posix()
        or any(part in ("", ".", "..") for part in relative.parts)
    ):
        raise RuntimeError("candidate_path must stay below the workspace")
    if relative.as_posix() == "Submission.lean":
        raise RuntimeError("Submission.lean is runner-owned; submit a scratch candidate")

    current = workspace
    parts = list(relative.parts)
    for index, part in enumerate(parts):
        current = current / part
        try:
            metadata = current.lstat()
        except OSError as error:
            raise RuntimeError(f"cannot read candidate_path: {error}") from error
        if stat.S_ISLNK(metadata.st_mode):
            raise RuntimeError("candidate_path may not contain a symlink")
        if index < len(parts) - 1 and not stat.S_ISDIR(metadata.st_mode):
            raise RuntimeError("candidate_path parent is not a directory")
    if not stat.S_ISREG(metadata.st_mode):
        raise RuntimeError("candidate_path must name a regular file")

    flags = os.O_RDONLY | os.O_CLOEXEC
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(current, flags)
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise RuntimeError("candidate_path must name a regular file")
        first = bytearray()
        while len(first) <= MAX_SUBMISSION_BYTES:
            chunk = os.read(descriptor, min(65536, MAX_SUBMISSION_BYTES + 1 - len(first)))
            if not chunk:
                break
            first.extend(chunk)
        if len(first) > MAX_SUBMISSION_BYTES:
            raise RuntimeError("candidate proof exceeds the submission size limit")
        middle = os.fstat(descriptor)
        os.lseek(descriptor, 0, os.SEEK_SET)
        second = bytearray()
        while len(second) < len(first) + 1:
            chunk = os.read(descriptor, min(65536, len(first) + 1 - len(second)))
            if not chunk:
                break
            second.extend(chunk)
        after = os.fstat(descriptor)
    finally:
        os.close(descriptor)
    stable_fields = ("st_dev", "st_ino", "st_mode", "st_size", "st_mtime_ns", "st_ctime_ns")
    if any(
        getattr(before, field) != getattr(middle, field)
        or getattr(before, field) != getattr(after, field)
        for field in stable_fields
    ) or bytes(first) != bytes(second):
        raise RuntimeError("candidate_path changed while it was snapshotted")
    return relative.as_posix(), bytes(first)


def _write_bytes_exclusive(path: Path, payload: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor = os.open(
        path, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC, 0o600
    )
    try:
        offset = 0
        while offset < len(payload):
            offset += os.write(descriptor, payload[offset:])
        os.fsync(descriptor)
    finally:
        os.close(descriptor)


def is_canonical_nested_submit_exec_input(
    source: Any, *, candidate_path: str
) -> bool:
    """Recognize only the exact frozen code-mode submit invocation bytes."""

    return bool(
        candidate_path == "Candidate.lean"
        and source == NESTED_SUBMISSION_EXEC_SOURCE
        and len(source.encode("utf-8")) == NESTED_SUBMISSION_EXEC_SOURCE_BYTES
        and hashlib.sha256(source.encode("utf-8")).hexdigest()
        == NESTED_SUBMISSION_EXEC_SOURCE_SHA256
    )


def nested_submission_exec_yield_record() -> dict[str, Any]:
    """Return the frozen proof that code-mode cannot yield during the run."""

    return {
        "outer_exec_yield_time_ms": NESTED_SUBMISSION_EXEC_YIELD_TIME_MS,
        "outer_exec_yield_envelope_basis": (
            NESTED_SUBMISSION_EXEC_YIELD_ENVELOPE_BASIS
        ),
        "outer_exec_yield_attempt_wall_seconds": (
            NESTED_SUBMISSION_EXEC_YIELD_ATTEMPT_WALL_SECONDS
        ),
        "outer_exec_yield_post_submission_validation_reserve_seconds": (
            NESTED_SUBMISSION_EXEC_YIELD_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS
        ),
        "outer_exec_yield_envelope_ms": NESTED_SUBMISSION_EXEC_YIELD_ENVELOPE_MS,
        "outer_exec_yield_margin_ms": NESTED_SUBMISSION_EXEC_YIELD_MARGIN_MS,
        "outer_exec_timer_starts_at_or_after_prompt_release": True,
        "outer_exec_yield_exceeds_envelope": (
            NESTED_SUBMISSION_EXEC_YIELD_TIME_MS
            > NESTED_SUBMISSION_EXEC_YIELD_ENVELOPE_MS
        ),
    }


class SubmissionBarrier:
    """Authenticate a root-only Ultra proof boundary through a blocked tool call."""

    def __init__(
        self,
        *,
        workspace: Path,
        usage_output: Path,
        ledger: "AttemptUsageLedger",
        protocol_input: TextIO,
        protocol_reader: "_ProtocolReader",
        provider_gate: ProviderTokenGate | None = None,
    ) -> None:
        self.workspace = workspace
        self.usage_output = usage_output
        self.ledger = ledger
        self.protocol_input = protocol_input
        self.protocol_reader = protocol_reader
        self.provider_gate = provider_gate
        self.paths = submission_barrier_paths(usage_output)
        self.pending: dict[str, Any] | None = None
        self.sequence = 0
        self.accepted = False
        stale = [
            path
            for key, path in self.paths.items()
            if key != "challenge" and (path.exists() or path.is_symlink())
        ]
        stale.extend(
            usage_output.parent.glob(usage_output.name + ".submission-*.lean")
        )
        if stale:
            raise RuntimeError("stale submission-barrier artifact exists")
        challenge_path = self.paths["challenge"]
        if challenge_path.is_symlink() or not challenge_path.is_file():
            raise RuntimeError("runner submission challenge is missing")
        try:
            challenge_raw = json.loads(challenge_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            raise RuntimeError(f"cannot read runner submission challenge: {error}") from error
        self.challenge = verify_authenticated_record(
            challenge_raw, "challenge_sha256"
        )
        if (
            self.challenge.get("schema_version") != SUBMISSION_BARRIER_SCHEMA_VERSION
            or self.challenge.get("kind") != "highambench_submission_challenge"
            or not isinstance(self.challenge.get("attempt_nonce"), str)
            or not self.challenge["attempt_nonce"]
            or not isinstance(self.challenge.get("run_id"), str)
            or not self.challenge["run_id"]
            or not isinstance(
                self.challenge.get("validator_contract_sha256"), str
            )
            or not re.fullmatch(
                r"[0-9a-f]{64}", self.challenge["validator_contract_sha256"]
            )
            or any(
                self.challenge.get(field) != expected
                for field, expected in nested_submission_exec_yield_record().items()
            )
        ):
            raise RuntimeError("runner submission challenge is malformed")

    def _gate_submission_eligibility(self) -> str | None:
        if self.provider_gate is None:
            return None
        state = _provider_gate_state_view(self.provider_gate.snapshot())
        if state.get("poisoned") is True:
            raise RuntimeError("provider-token gate was poisoned before submission")
        if (
            state.get("crossing") is not None
            or state.get("close_reason") == PROVIDER_GATE_CLOSE_TOKEN_LIMIT
        ):
            return "the exact provider-token cap has been reached"
        close_reason = state.get("close_reason")
        if close_reason not in (None, PROVIDER_GATE_CLOSE_ACCEPTED_SUBMISSION):
            return "the provider-token gate is already closed"
        return None

    @staticmethod
    def dynamic_tool_spec() -> dict[str, Any]:
        return {
            "type": "function",
            "name": SUBMISSION_TOOL_NAME,
            "description": (
                "Root coordinator only. In a separate final response, after testing a "
                "scratch Candidate.lean and waiting for every descendant to finish, call "
                "this as the sole nested tool call from the exact trusted outer exec "
                f"program {NESTED_SUBMISSION_EXEC_SOURCE!r}. Never create "
                "Submission.lean directly."
            ),
            "inputSchema": {
                "type": "object",
                "properties": {
                    "candidate_path": {
                        "type": "string",
                        "const": "Candidate.lean",
                        "description": "The already-tested scratch Lean file.",
                    }
                },
                "required": ["candidate_path"],
                "additionalProperties": False,
            },
        }

    def _reject(self, message: Mapping[str, Any], note: str) -> None:
        request_id = message.get("id")
        if not isinstance(request_id, (str, int)) or isinstance(request_id, bool):
            raise RuntimeError("dynamic tool request has an invalid JSON-RPC id")
        _dynamic_tool_response(
            self.protocol_input, request_id, success=False, note=note
        )

    def capture(self, message: Mapping[str, Any]) -> bool:
        """Capture an app-server request without blocking the notification stream."""

        if message.get("method") != "item/tool/call":
            return False
        request_id = message.get("id")
        params = message.get("params")
        if (
            not isinstance(request_id, (str, int))
            or isinstance(request_id, bool)
            or not isinstance(params, Mapping)
        ):
            raise RuntimeError("app-server emitted malformed dynamic tool request")
        if params.get("tool") != SUBMISSION_TOOL_NAME:
            raise RuntimeError("app-server requested an unregistered dynamic tool")
        gate_eligibility = self._gate_submission_eligibility()
        if gate_eligibility is not None:
            self._reject(message, gate_eligibility)
            return True
        if params.get("namespace") not in (None, ""):
            self._reject(message, "submit_proof may not use a tool namespace")
            return True
        thread_id = params.get("threadId")
        turn_id = params.get("turnId")
        call_id = params.get("callId")
        arguments = params.get("arguments")
        if not all(
            isinstance(value, str) and value
            for value in (thread_id, turn_id, call_id)
        ) or not isinstance(arguments, Mapping):
            self._reject(message, "malformed submit_proof request")
            return True
        if set(arguments) != {"candidate_path"}:
            self._reject(message, "submit_proof requires only candidate_path")
            return True
        candidate_path = arguments.get("candidate_path")
        if not isinstance(candidate_path, str):
            self._reject(message, "candidate_path must be a string")
            return True
        if candidate_path != "Candidate.lean":
            self._reject(message, "candidate_path must be exactly Candidate.lean")
            return True
        if thread_id != self.ledger.root_thread_id:
            self._reject(message, "only the root coordinator may submit a proof")
            return True
        if self.pending is not None:
            self._reject(message, "another submission request is already pending")
            return True
        wire = self.ledger.pending_submission_wire(
            turn_id=turn_id,
            call_id=call_id,
            candidate_path=candidate_path,
        )
        completed_match: tuple[str, dict[str, Any], dict[str, Any]] | None = None
        if wire is None:
            completed_match = self.ledger.completed_submission_response(
                turn_id=turn_id,
                call_id=call_id,
                candidate_path=candidate_path,
            )
            if completed_match is not None:
                wire = completed_match[2]
        # Diagnose a positively identified noncanonical outer/inner attempt
        # before consulting token projections.  In response-first app-server
        # order, an omitted final newline can otherwise masquerade as a missing
        # root cumulative update.  An entirely unstaged submit still follows
        # the ordinary descendant/accounting precedence below.
        noncanonical_wire_attempt = (
            wire is None
            and self.ledger.noncanonical_submission_wire_attempt(
                turn_id=turn_id,
                call_id=call_id,
                candidate_path=candidate_path,
            )
        )
        if noncanonical_wire_attempt:
            self._reject(
                message,
                "submit_proof outer exec wire is noncanonical. Retry in a new "
                "final response; the source must exactly match this "
                f"{NESTED_SUBMISSION_EXEC_SOURCE_BYTES}-byte program, including "
                f"its final newline, as the sole outer exec item: "
                f"{NESTED_SUBMISSION_EXEC_SOURCE!r}",
            )
            return True
        eligibility = self.ledger.boundary_eligible(
            turn_id=turn_id,
            submit_response_id=(
                completed_match[0] if completed_match is not None else None
            ),
        )
        if eligibility is not None:
            self._reject(message, eligibility)
            return True
        if wire is None:
            self._reject(
                message,
                "submit_proof lacks the exact preceding outer exec raw item and "
                "matching dynamicToolCall item/started evidence",
            )
            return True
        call_observed_at_unix_ns = time.time_ns()
        call_observed_at_monotonic_ns = time.monotonic_ns()
        try:
            normalized_path, candidate = _safe_candidate_bytes(
                self.workspace, candidate_path
            )
            next_sequence = self.sequence + 1
            attempt_paths = submission_barrier_paths(
                self.usage_output, next_sequence
            )
            _write_bytes_exclusive(attempt_paths["snapshot"], candidate)
            call_record = authenticated_record(
                {
                    "schema_version": SUBMISSION_BARRIER_SCHEMA_VERSION,
                    "kind": "highambench_submission_call",
                    "sequence": next_sequence,
                    "challenge_sha256": self.challenge["challenge_sha256"],
                    "attempt_nonce": self.challenge["attempt_nonce"],
                    "run_id": self.challenge.get("run_id"),
                    "validator_contract_sha256": self.challenge.get(
                        "validator_contract_sha256"
                    ),
                    "jsonrpc_request_id": request_id,
                    "call_id": call_id,
                    "inner_dynamic_call_id": call_id,
                    "inner_dynamic_tool_name": SUBMISSION_TOOL_NAME,
                    "inner_dynamic_arguments": {"candidate_path": normalized_path},
                    **wire,
                    "thread_id": thread_id,
                    "turn_id": turn_id,
                    "candidate_path": normalized_path,
                    "candidate_sha256": hashlib.sha256(candidate).hexdigest(),
                    "candidate_size_bytes": len(candidate),
                    "snapshot_name": attempt_paths["snapshot"].name,
                    "captured_at_unix_ns": call_observed_at_unix_ns,
                    "captured_at_monotonic_ns": call_observed_at_monotonic_ns,
                },
                "call_sha256",
            )
            _write_json_exclusive(attempt_paths["call"], call_record)
        except RuntimeError as error:
            if "attempt_paths" in locals():
                with contextlib.suppress(OSError):
                    attempt_paths["snapshot"].unlink()
                with contextlib.suppress(OSError):
                    attempt_paths["call"].unlink()
            self._reject(message, str(error))
            return True
        self.sequence = next_sequence
        self.pending = {
            "message": dict(message),
            "request_id": request_id,
            "thread_id": thread_id,
            "turn_id": turn_id,
            "call_id": call_id,
            "candidate_path": normalized_path,
            "candidate": candidate,
            "candidate_sha256": hashlib.sha256(candidate).hexdigest(),
            "call_record": call_record,
            "wire": wire,
            "captured_response_id": (
                completed_match[0] if completed_match is not None else None
            ),
            "attempt_paths": attempt_paths,
            "captured_notification_sequence": self.ledger.notification_sequence,
            "captured_at_unix_ns": call_record["captured_at_unix_ns"],
            "captured_at_monotonic_ns": call_record[
                "captured_at_monotonic_ns"
            ],
        }
        return True

    def _observe_during_hidden_validation(
        self, message: Mapping[str, Any]
    ) -> None:
        """Accept only bookkeeping tails while the inner submit stays blocked.

        In particular, a ``custom_tool_call_output`` from the outer exec is not
        harmless: a code-mode progress yield completes that model-visible tool
        call and can immediately launch another provider response.  The frozen
        exec pragma is long enough that the official attempt and validation
        envelope must end first, so observing any such output remains fatal.
        """

        method = message.get("method")
        if method == "thread/tokenUsage/updated":
            self.ledger.observe(message)
            return
        if method == "thread/status/changed":
            params = message.get("params")
            if (
                not isinstance(params, Mapping)
                or params.get("threadId") != self.ledger.root_thread_id
            ):
                raise RuntimeError(
                    "post-boundary descendant thread activity is forbidden"
                )
            self.ledger.observe(message)
            return
        raise RuntimeError(
            f"post-boundary app-server activity is forbidden: {method!r}"
        )

    def _wait_for_ack(self, request: Mapping[str, Any]) -> dict[str, Any]:
        ack_path = self.paths["ack"]
        while not ack_path.exists():
            # The tool remains blocked, but app-server notifications are still
            # asynchronous.  Drain them so any post-boundary model/child work
            # taints the attempt instead of hiding behind validator latency.
            try:
                message = self.protocol_reader.get(
                    timeout=SUBMISSION_ACK_POLL_SECONDS
                )
            except queue.Empty:
                continue
            else:
                self._observe_during_hidden_validation(message)
        while True:
            try:
                message = self.protocol_reader.get_nowait()
            except queue.Empty:
                break
            self._observe_during_hidden_validation(message)
        if ack_path.is_symlink() or not ack_path.is_file():
            raise RuntimeError("submission ack is not a regular non-symlink file")
        try:
            raw = json.loads(ack_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as error:
            raise RuntimeError(f"cannot read submission ack: {error}") from error
        ack = verify_authenticated_record(raw, "ack_sha256")
        expected = {
            "schema_version": SUBMISSION_BARRIER_SCHEMA_VERSION,
            "kind": "highambench_submission_ack",
            "sequence": request["sequence"],
            "request_sha256": request["request_sha256"],
            "candidate_sha256": request["candidate_sha256"],
        }
        if any(ack.get(key) != value for key, value in expected.items()):
            raise RuntimeError("submission ack does not bind the pending request")
        if ack.get("decision") not in ("accept", "reject"):
            raise RuntimeError("submission ack has an invalid decision")
        note = ack.get("note")
        if not isinstance(note, str) or len(note.encode("utf-8")) > MAX_REJECTION_NOTE_BYTES:
            raise RuntimeError("submission ack note is malformed or too large")
        return ack

    def _cleanup_attempt(self, paths: Mapping[str, Path]) -> None:
        for path in (
            self.paths["ack"],
            self.paths["call"],
            paths["snapshot"],
            # The request is the runner's readiness marker; remove it last so
            # observing its absence proves every per-attempt artifact is gone.
            self.paths["request"],
        ):
            with contextlib.suppress(OSError):
                path.unlink()

    def advance(self) -> bool:
        """Activate a pending call only after its exact raw response is durable."""

        pending = self.pending
        if pending is None:
            return False
        gate_eligibility = self._gate_submission_eligibility()
        if gate_eligibility is not None:
            message = pending["message"]
            self.pending = None
            self._cleanup_attempt(pending["attempt_paths"])
            self._reject(message, gate_eligibility)
            return False
        match = self.ledger.matching_submit_response(
            turn_id=pending["turn_id"],
            call_id=pending["call_id"],
            candidate_path=pending["candidate_path"],
            expected_wire=pending["wire"],
        )
        if match is None:
            containing_response = any(
                response.get("thread_id") == self.ledger.root_thread_id
                and response.get("turn_id") == pending["turn_id"]
                and any(
                    isinstance(item, Mapping)
                    and item.get("call_id") == pending["call_id"]
                    for item in response.get("raw_items", [])
                )
                for response in self.ledger.responses.values()
            )
            later_root_response = any(
                response.get("thread_id") == self.ledger.root_thread_id
                and response.get("turn_id") == pending["turn_id"]
                and response.get("sequence", 0)
                > pending["captured_notification_sequence"]
                for response in self.ledger.responses.values()
            )
            if containing_response or later_root_response:
                message = pending["message"]
                self.pending = None
                self._cleanup_attempt(pending["attempt_paths"])
                self._reject(
                    message,
                    "exec must be the sole tool call in the separate final response, "
                    f"with exact source {NESTED_SUBMISSION_EXEC_SOURCE!r}",
                )
            return False
        response_id, response, wire = match
        if pending["captured_response_id"] not in (None, response_id):
            message = pending["message"]
            self.pending = None
            self._cleanup_attempt(pending["attempt_paths"])
            self._reject(message, "submission response identity changed after capture")
            return False
        eligibility = self.ledger.boundary_eligible(
            turn_id=pending["turn_id"], submit_response_id=response_id
        )
        if eligibility is not None:
            message = pending["message"]
            self.pending = None
            self._cleanup_attempt(pending["attempt_paths"])
            self._reject(message, eligibility)
            return False
        candidate_path = pending["candidate_path"]
        candidate = pending["candidate"]
        paths = pending["attempt_paths"]
        snapshot_path = paths["snapshot"]
        candidate_sha256 = pending["candidate_sha256"]
        boundary_usage = self.ledger.provider_boundary_usage()
        captured_monotonic_ns = pending["captured_at_monotonic_ns"]
        response_monotonic_ns = response["observed_at_monotonic_ns"]
        inner_started_monotonic_ns = wire[
            "inner_dynamic_item_started_at_monotonic_ns"
        ]
        if (
            inner_started_monotonic_ns <= captured_monotonic_ns
            < response_monotonic_ns
        ):
            submission_event_order = SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
            dynamic_call_before_response = True
            response_before_dynamic_call = False
        elif (
            response_monotonic_ns < inner_started_monotonic_ns
            <= captured_monotonic_ns
        ):
            submission_event_order = SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER
            dynamic_call_before_response = False
            response_before_dynamic_call = True
        else:
            message = pending["message"]
            self.pending = None
            self._cleanup_attempt(pending["attempt_paths"])
            self._reject(message, "submission event order is not strictly observable")
            return False
        request = authenticated_record(
            {
                "schema_version": SUBMISSION_BARRIER_SCHEMA_VERSION,
                "kind": "highambench_submission_request",
                "sequence": self.sequence,
                "challenge_sha256": self.challenge["challenge_sha256"],
                "call_sha256": pending["call_record"]["call_sha256"],
                "attempt_nonce": self.challenge["attempt_nonce"],
                "run_id": self.challenge.get("run_id"),
                "validator_contract_sha256": self.challenge.get(
                    "validator_contract_sha256"
                ),
                "jsonrpc_request_id": pending["request_id"],
                "call_id": pending["call_id"],
                "submission_transport": wire["submission_transport"],
                "outer_raw_item_id": wire["outer_raw_item_id"],
                "outer_raw_item_type": wire["outer_raw_item_type"],
                "outer_exec_name": wire["outer_exec_name"],
                "outer_exec_call_id": wire.get("outer_exec_call_id"),
                "outer_exec_program": wire.get("outer_exec_program"),
                "outer_exec_program_bytes": wire.get("outer_exec_program_bytes"),
                "outer_exec_program_sha256": wire.get("outer_exec_program_sha256"),
                **{
                    field: wire.get(field)
                    for field in nested_submission_exec_yield_record()
                },
                "outer_raw_item_observed_at_monotonic_ns": wire[
                    "outer_raw_item_observed_at_monotonic_ns"
                ],
                "inner_dynamic_item_started_at_monotonic_ns": wire[
                    "inner_dynamic_item_started_at_monotonic_ns"
                ],
                "outer_raw_item_observed_before_inner_dynamic_call": True,
                "inner_dynamic_call_id": pending["call_id"],
                "inner_dynamic_tool_name": SUBMISSION_TOOL_NAME,
                "inner_dynamic_arguments": {"candidate_path": candidate_path},
                "thread_id": pending["thread_id"],
                "turn_id": pending["turn_id"],
                "response_id": response_id,
                "raw_response_notification_sequence": response["sequence"],
                "raw_response_observed_at_unix_ns": response["observed_at_unix_ns"],
                "raw_response_observed_at_monotonic_ns": response[
                    "observed_at_monotonic_ns"
                ],
                "candidate_path": candidate_path,
                "candidate_sha256": candidate_sha256,
                "candidate_size_bytes": len(candidate),
                "snapshot_name": snapshot_path.name,
                "captured_at_unix_ns": pending["captured_at_unix_ns"],
                "captured_at_monotonic_ns": pending["captured_at_monotonic_ns"],
                "request_published_at_unix_ns": time.time_ns(),
                "request_published_at_monotonic_ns": time.monotonic_ns(),
                "boundary_usage": boundary_usage,
                "raw_response_completed_before_boundary_publication": True,
                "submission_event_order": submission_event_order,
                "dynamic_call_observed_before_raw_response_completed": (
                    dynamic_call_before_response
                ),
                "raw_response_completed_before_dynamic_call_observed": (
                    response_before_dynamic_call
                ),
                "candidate_captured_at_dynamic_call": True,
                "root_only": True,
                "descendants_quiescent": True,
                "sole_model_tool_call_in_response": True,
                "outer_exec_final_raw_item": True,
                "inner_dynamic_call_observed": True,
                "inner_dynamic_item_started": True,
                "inner_submit_invocation_exact": True,
                "inner_submit_only_nested_tool_call": True,
            },
            "request_sha256",
        )
        try:
            _write_json_exclusive(paths["request"], request)
        except BaseException:
            self._cleanup_attempt(paths)
            raise
        ack = self._wait_for_ack(request)
        if ack["decision"] == "reject":
            message = pending["message"]
            self.pending = None
            self._cleanup_attempt(paths)
            self._reject(message, ack["note"])
            return False

        gate_close: dict[str, Any] | None = None
        if self.provider_gate is not None:
            gate_close = dict(self.provider_gate.close_for_accepted_submission())
            gate_state = _provider_gate_state_view(self.provider_gate.snapshot())
            if (
                gate_close.get("won") is not True
                or gate_close.get("effective_reason")
                != PROVIDER_GATE_CLOSE_ACCEPTED_SUBMISSION
                or gate_close.get("phase") != "CLOSED"
                or gate_state.get("open_request_ids") != []
                or gate_state.get("all_complete") is not True
            ):
                self._cleanup_attempt(paths)
                raise RuntimeError(
                    "provider-token gate could not atomically close an exact proof boundary"
                )

        boundary = {
            "schema_version": SUBMISSION_BARRIER_SCHEMA_VERSION,
            "authenticated": True,
            "status": "accepted",
            "exact": True,
            "sequence": self.sequence,
            "challenge_sha256": request["challenge_sha256"],
            "call_sha256": request["call_sha256"],
            "attempt_nonce": request["attempt_nonce"],
            "run_id": request.get("run_id"),
            "validator_contract_sha256": request.get(
                "validator_contract_sha256"
            ),
            "request_sha256": request["request_sha256"],
            "ack_sha256": ack["ack_sha256"],
            "jsonrpc_request_id": pending["request_id"],
            "call_id": pending["call_id"],
            "submission_transport": request["submission_transport"],
            "outer_raw_item_id": request["outer_raw_item_id"],
            "outer_raw_item_type": request["outer_raw_item_type"],
            "outer_exec_name": request["outer_exec_name"],
            "outer_exec_call_id": request.get("outer_exec_call_id"),
            "outer_exec_program": request.get("outer_exec_program"),
            "outer_exec_program_bytes": request.get("outer_exec_program_bytes"),
            "outer_exec_program_sha256": request.get("outer_exec_program_sha256"),
            **{
                field: request.get(field)
                for field in nested_submission_exec_yield_record()
            },
            "outer_raw_item_observed_at_monotonic_ns": request[
                "outer_raw_item_observed_at_monotonic_ns"
            ],
            "inner_dynamic_item_started_at_monotonic_ns": request[
                "inner_dynamic_item_started_at_monotonic_ns"
            ],
            "outer_raw_item_observed_before_inner_dynamic_call": True,
            "inner_dynamic_call_id": request["inner_dynamic_call_id"],
            "inner_dynamic_tool_name": request["inner_dynamic_tool_name"],
            "inner_dynamic_arguments": request["inner_dynamic_arguments"],
            "thread_id": pending["thread_id"],
            "turn_id": pending["turn_id"],
            "response_id": response_id,
            "raw_response_notification_sequence": response["sequence"],
            "candidate_path": candidate_path,
            "candidate_sha256": candidate_sha256,
            "candidate_size_bytes": len(candidate),
            "request_published_at_unix_ns": request["request_published_at_unix_ns"],
            "request_published_at_monotonic_ns": request[
                "request_published_at_monotonic_ns"
            ],
            "validator_accepted_at_unix_ns": ack.get("validator_accepted_at_unix_ns"),
            "validator_accepted_elapsed_seconds": ack.get(
                "validator_accepted_elapsed_seconds"
            ),
            "raw_response_completed_before_boundary_publication": True,
            "submission_event_order": request["submission_event_order"],
            "dynamic_call_observed_before_raw_response_completed": request[
                "dynamic_call_observed_before_raw_response_completed"
            ],
            "raw_response_completed_before_dynamic_call_observed": request[
                "raw_response_completed_before_dynamic_call_observed"
            ],
            "candidate_captured_at_dynamic_call": True,
            "current_response_cumulative_required": False,
            "root_only": True,
            "descendants_quiescent": True,
            "sole_model_tool_call_in_response": True,
            "outer_exec_final_raw_item": True,
            "inner_dynamic_call_observed": True,
            "inner_dynamic_item_started": True,
            "inner_submit_invocation_exact": True,
            "inner_submit_only_nested_tool_call": True,
            "inner_dynamic_call_left_blocked": True,
            "inner_dynamic_tool_response_sent": False,
            "outer_exec_output_emitted": False,
            "later_model_response_possible": False,
        }
        if gate_close is not None:
            boundary["provider_gate_close"] = gate_close
        self.ledger.accept_submission_boundary(boundary)
        self.accepted = True
        self.pending = None
        raise _SubmissionAccepted


def positive_int(raw: str) -> int:
    try:
        value = int(raw)
    except ValueError as error:
        raise argparse.ArgumentTypeError("must be an integer") from error
    if value <= 0:
        raise argparse.ArgumentTypeError("must be positive")
    return value


def _below(root: Path, path: Path) -> Path:
    root = root.resolve()
    path = path.resolve()
    try:
        path.relative_to(root)
    except ValueError as error:
        raise ValueError(f"path must stay below workspace {root}: {path}") from error
    return path


def _read_required(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except OSError as error:
        raise RuntimeError(f"cannot read fixed prompt input {path}: {error}") from error


def build_prompt(
    prompt_file: Path,
    context_file: Path,
    target_file: Path,
    condition_prompt_file: Path | None = None,
) -> str:
    sections = [_read_required(prompt_file).rstrip()]
    if condition_prompt_file is not None:
        sections.append(_read_required(condition_prompt_file).rstrip())
    sections.extend(
        (
            "## Task context\n\n" + _read_required(context_file).rstrip(),
            "## Fixed Lean target\n\n```lean\n"
            + _read_required(target_file).rstrip()
            + "\n```",
        )
    )
    return "\n\n".join(sections) + "\n"


def validated_condition_prompt(
    condition: str,
    condition_prompt_file: Path | None,
    condition_prompt_sha256: str | None,
) -> Path | None:
    """Fail closed unless L receives exactly one authenticated supplement."""

    if condition == "N":
        if condition_prompt_file is not None or condition_prompt_sha256 is not None:
            raise RuntimeError("condition N must not receive condition-L prompt material")
        return None
    if condition != "L":
        raise RuntimeError(f"unsupported benchmark condition: {condition!r}")
    if condition_prompt_file is None or condition_prompt_sha256 is None:
        raise RuntimeError(
            "condition L requires a frozen condition prompt file and SHA-256"
        )
    if not re.fullmatch(r"[0-9a-f]{64}", condition_prompt_sha256):
        raise RuntimeError("condition prompt SHA-256 is invalid")
    if condition_prompt_file.is_symlink() or not condition_prompt_file.is_file():
        raise RuntimeError("condition prompt must be a regular non-symlink file")
    actual_condition_prompt_sha256 = hashlib.sha256(
        condition_prompt_file.read_bytes()
    ).hexdigest()
    if actual_condition_prompt_sha256 != condition_prompt_sha256:
        raise RuntimeError("condition prompt does not match its frozen SHA-256")
    return condition_prompt_file


def canonical_protocol_wire(message: Mapping[str, Any]) -> bytes:
    return (
        json.dumps(message, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")


def prompt_turn_start_request(
    *, prompt: str, root_thread_id: str, model: str, reasoning_effort: str
) -> dict[str, Any]:
    """Return the exact frozen root turn/start request released by the adapter."""

    return {
        "id": TURN_START_REQUEST_ID,
        "method": "turn/start",
        "params": {
            "approvalPolicy": "never",
            "cwd": "/workspace",
            "effort": reasoning_effort,
            "input": [{"type": "text", "text": prompt}],
            "model": model,
            "sandboxPolicy": {"type": "dangerFullAccess"},
            "threadId": root_thread_id,
        },
    }


class PromptReleaseHandshake:
    """Hold turn/start until a trusted runner authorizes exact prompt release."""

    _COMMON_FIELDS = (
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

    def __init__(
        self,
        *,
        args: argparse.Namespace,
        workspace: Path,
        usage_output: Path,
        prompt: str,
    ) -> None:
        self.args = args
        self.prompt = prompt
        self.prompt_bytes = prompt.encode("utf-8")
        self.expected_paths = prompt_handshake_paths(usage_output)
        raw_paths = {
            "ready": getattr(args, "prompt_ready_output", None),
            "go": getattr(args, "prompt_go_input", None),
            "release": getattr(args, "prompt_release_output", None),
        }
        if any(not isinstance(path, Path) for path in raw_paths.values()):
            raise RuntimeError("all prompt-handshake paths are required")
        self.paths: dict[str, Path] = {}
        trusted_parent = usage_output.parent.resolve(strict=True)
        for name, raw in raw_paths.items():
            assert isinstance(raw, Path)
            if not raw.is_absolute():
                raise RuntimeError(f"prompt-{name} path must be absolute")
            if raw.parent != trusted_parent:
                raise RuntimeError(
                    f"prompt-{name} path must be a direct child of trusted logs"
                )
            expected = self.expected_paths[name]
            if raw != expected:
                raise RuntimeError(
                    f"prompt-{name} path does not match the usage-bound path"
                )
            try:
                raw.lstat()
            except FileNotFoundError:
                pass
            else:
                raise RuntimeError(f"prompt-{name} artifact already exists")
            try:
                raw.relative_to(workspace)
            except ValueError:
                pass
            else:
                raise RuntimeError(
                    f"prompt-{name} artifact must be outside the model workspace"
                )
            self.paths[name] = raw
        if len(set(self.paths.values())) != 3 or usage_output in self.paths.values():
            raise RuntimeError("prompt-handshake paths are not distinct")
        nonce = getattr(args, "prompt_handshake_nonce", None)
        if not isinstance(nonce, str) or re.fullmatch(r"[0-9a-f]{64}", nonce) is None:
            raise RuntimeError("prompt-handshake nonce must be 64 lowercase hex digits")
        run_id = getattr(args, "prompt_run_id", None)
        if not isinstance(run_id, str) or not run_id or len(run_id.encode("utf-8")) > 512:
            raise RuntimeError("prompt run id is invalid")
        self.common: dict[str, Any] = {
            "schema_version": PROMPT_RELEASE_SCHEMA_VERSION,
            "protocol_version": PROMPT_RELEASE_PROTOCOL_VERSION,
            "handshake_nonce": nonce,
            "run_id": run_id,
            "condition": args.condition,
            "model": args.model,
            "reasoning_effort": args.reasoning_effort,
            "root_thread_id": None,
            "turn_start_request_id": TURN_START_REQUEST_ID,
            "effective_prompt_sha256": hashlib.sha256(self.prompt_bytes).hexdigest(),
            "effective_prompt_bytes": len(self.prompt_bytes),
            "adapter_name": PROMPT_RELEASE_ADAPTER_NAME,
            "adapter_version": PROMPT_RELEASE_ADAPTER_VERSION,
            "app_server_client_name": APP_SERVER_CLIENT_NAME,
            "app_server_client_version": APP_SERVER_CLIENT_VERSION,
            "elapsed_clock": "CLOCK_MONOTONIC",
        }
        self.ready: dict[str, Any] | None = None
        self.go: dict[str, Any] | None = None
        self.released: dict[str, Any] | None = None

    @staticmethod
    def _require_exact_record(
        record: Mapping[str, Any], expected: Mapping[str, Any], hash_field: str
    ) -> None:
        if set(record) != set(expected) | {hash_field}:
            raise RuntimeError("prompt-handshake record has unexpected fields")
        for field, value in expected.items():
            if record.get(field) != value:
                raise RuntimeError(
                    f"prompt-handshake record has the wrong {field}"
                )

    def publish_ready(self, root_thread_id: str) -> dict[str, Any]:
        if self.ready is not None:
            raise RuntimeError("prompt READY was published twice")
        if not isinstance(root_thread_id, str) or not root_thread_id:
            raise RuntimeError("prompt READY lacks the root thread id")
        self.common["root_thread_id"] = root_thread_id
        ready_at_monotonic_ns = time.monotonic_ns()
        ready_at_unix_ns = time.time_ns()
        ready_unsigned = {
            **self.common,
            "kind": PROMPT_READY_KIND,
            "turn_start_write_state": "not_started",
            "ready_at_monotonic_ns": ready_at_monotonic_ns,
            "ready_at_unix_ns": ready_at_unix_ns,
        }
        self.ready = write_authenticated_record_atomic(
            self.paths["ready"], ready_unsigned, "ready_sha256"
        )
        return dict(self.ready)

    def wait_for_go(self) -> dict[str, Any]:
        if self.ready is None:
            raise RuntimeError("cannot wait for GO before READY")
        if self.go is not None:
            return dict(self.go)
        expected = {
            **self.common,
            "kind": PROMPT_GO_KIND,
            "ready_sha256": self.ready["ready_sha256"],
            "turn_start_write_authorized": True,
        }
        while True:
            try:
                candidate = read_authenticated_record_file(
                    self.paths["go"], "go_sha256"
                )
            except FileNotFoundError:
                time.sleep(PROMPT_HANDSHAKE_POLL_SECONDS)
                continue
            self._require_exact_record(
                candidate,
                {
                    **expected,
                    "authorized_at_monotonic_ns": candidate.get(
                        "authorized_at_monotonic_ns"
                    ),
                    "authorized_at_unix_ns": candidate.get("authorized_at_unix_ns"),
                },
                "go_sha256",
            )
            authorized_monotonic = candidate.get("authorized_at_monotonic_ns")
            authorized_unix = candidate.get("authorized_at_unix_ns")
            if (
                not isinstance(authorized_monotonic, int)
                or isinstance(authorized_monotonic, bool)
                or authorized_monotonic <= 0
                or not isinstance(authorized_unix, int)
                or isinstance(authorized_unix, bool)
                or authorized_unix <= 0
                or authorized_monotonic < self.ready["ready_at_monotonic_ns"]
            ):
                raise RuntimeError("prompt GO has invalid authorization timestamps")
            self.go = candidate
            return dict(candidate)

    def release_turn_start(
        self, stream: TextIO, message: Mapping[str, Any]
    ) -> dict[str, Any]:
        if self.ready is None or self.go is None:
            raise RuntimeError("turn/start cannot be released before READY/GO")
        if self.released is not None:
            raise RuntimeError("turn/start was released twice")
        if message.get("id") != TURN_START_REQUEST_ID or message.get("method") != "turn/start":
            raise RuntimeError("prompt release attempted for the wrong protocol request")
        params = message.get("params")
        if not isinstance(params, Mapping):
            raise RuntimeError("turn/start request lacks params")
        expected_input = [{"type": "text", "text": self.prompt}]
        if (
            params.get("threadId") != self.common["root_thread_id"]
            or params.get("model") != self.common["model"]
            or params.get("effort") != self.common["reasoning_effort"]
            or params.get("input") != expected_input
        ):
            raise RuntimeError("turn/start request disagrees with prompt READY identity")
        wire = canonical_protocol_wire(message)
        released_at_monotonic_ns = time.monotonic_ns()
        released_at_unix_ns = time.time_ns()
        written = stream.write(wire.decode("utf-8"))
        if written != len(wire.decode("utf-8")):
            raise RuntimeError("short write while releasing turn/start")
        stream.flush()
        flushed_at_monotonic_ns = time.monotonic_ns()
        flushed_at_unix_ns = time.time_ns()
        release_unsigned = {
            **self.common,
            "kind": PROMPT_RELEASED_KIND,
            "ready_sha256": self.ready["ready_sha256"],
            "go_sha256": self.go["go_sha256"],
            "turn_start_write_state": "flushed",
            "timestamp_capture_point": "immediately_before_turn_start_write",
            "turn_start_request_sha256": hashlib.sha256(wire).hexdigest(),
            "turn_start_request_bytes": len(wire),
            "released_at_monotonic_ns": released_at_monotonic_ns,
            "released_at_unix_ns": released_at_unix_ns,
            "turn_start_flushed_at_monotonic_ns": flushed_at_monotonic_ns,
            "turn_start_flushed_at_unix_ns": flushed_at_unix_ns,
        }
        self.released = write_authenticated_record_atomic(
            self.paths["release"], release_unsigned, "release_sha256"
        )
        return dict(self.released)


def normalized_usage(event: Mapping[str, Any]) -> dict[str, Any] | None:
    """Return cumulative app-server usage in the benchmark's stable JSON shape."""

    if event.get("method") != "thread/tokenUsage/updated":
        return None
    params = event.get("params")
    if not isinstance(params, Mapping):
        return None
    token_usage = params.get("tokenUsage")
    if not isinstance(token_usage, Mapping):
        return None
    usage = token_usage.get("total")
    if not isinstance(usage, Mapping):
        return None
    fields = ("inputTokens", "cachedInputTokens", "outputTokens", "totalTokens")
    if not all(
        isinstance(usage.get(field), int)
        and not isinstance(usage[field], bool)
        and usage[field] >= 0
        for field in fields
    ):
        return None
    input_tokens = int(usage["inputTokens"])
    cached_input_tokens = int(usage["cachedInputTokens"])
    output_tokens = int(usage["outputTokens"])
    if cached_input_tokens > input_tokens:
        return None
    if int(usage["totalTokens"]) != input_tokens + output_tokens:
        return None
    return {
        "input_tokens": input_tokens,
        "cached_input_tokens": cached_input_tokens,
        "output_tokens": output_tokens,
        "measurement_source": TOKEN_USAGE_MEASUREMENT_SOURCE,
        "live_cumulative": True,
        "input_includes_cached": True,
    }


def _normalized_breakdown(value: Any) -> dict[str, int] | None:
    """Normalize one app-server token breakdown without double-counting cache."""

    if not isinstance(value, Mapping):
        return None
    required = (
        "inputTokens",
        "cachedInputTokens",
        "outputTokens",
        "reasoningOutputTokens",
        "totalTokens",
    )
    if not all(
        isinstance(value.get(field), int)
        and not isinstance(value[field], bool)
        and value[field] >= 0
        for field in required
    ):
        return None
    cache_write = value.get("cacheWriteInputTokens", 0)
    if (
        not isinstance(cache_write, int)
        or isinstance(cache_write, bool)
        or cache_write < 0
    ):
        return None
    input_tokens = int(value["inputTokens"])
    cached_input_tokens = int(value["cachedInputTokens"])
    output_tokens = int(value["outputTokens"])
    reasoning_output_tokens = int(value["reasoningOutputTokens"])
    total_tokens = int(value["totalTokens"])
    if cached_input_tokens > input_tokens:
        return None
    if cache_write > input_tokens:
        return None
    if reasoning_output_tokens > output_tokens:
        return None
    if total_tokens != input_tokens + output_tokens:
        return None
    return {
        "input_tokens": input_tokens,
        "cached_input_tokens": cached_input_tokens,
        "cache_write_input_tokens": int(cache_write),
        "output_tokens": output_tokens,
        "reasoning_output_tokens": reasoning_output_tokens,
        "total_tokens": total_tokens,
    }


def normalized_raw_response(
    event: Mapping[str, Any],
) -> tuple[str, str, str, dict[str, int]] | None:
    """Return one exact upstream response usage event, or ``None`` if unrelated."""

    if event.get("method") != ULTRA_USAGE_NOTIFICATION:
        return None
    params = event.get("params")
    if not isinstance(params, Mapping):
        raise RuntimeError("Codex app-server emitted malformed raw response usage")
    response_id = params.get("responseId")
    thread_id = params.get("threadId")
    turn_id = params.get("turnId")
    if not all(isinstance(item, str) and item for item in (response_id, thread_id, turn_id)):
        raise RuntimeError("Codex app-server raw response usage lacks an identity")
    usage = _normalized_breakdown(params.get("usage"))
    if usage is None:
        raise RuntimeError(
            "Codex app-server raw response usage is null or malformed"
        )
    return str(response_id), str(thread_id), str(turn_id), usage


class AttemptUsageLedger:
    """Exact completed-response ledger for one rooted Ultra agent tree.

    Raw response IDs are the canonical deduplication boundary.  Cumulative
    per-thread totals are recorded only to check that every completed response
    appeared on the raw stream; they are never added across threads.
    """

    _SUM_FIELDS = (
        "input_tokens",
        "cached_input_tokens",
        "cache_write_input_tokens",
        "output_tokens",
        "reasoning_output_tokens",
        "total_tokens",
    )

    def __init__(
        self,
        output: Path,
        token_limit: int,
        root_thread_id: str,
        *,
        fork_policy: Mapping[str, Any] | None = None,
        provider_gate: ProviderTokenGate | None = None,
        provider_gate_artifact_path: Path | None = None,
    ) -> None:
        if token_limit <= 0:
            raise RuntimeError("token limit must be positive")
        if not root_thread_id:
            raise RuntimeError("root thread id must be nonempty")
        self.output = output
        self.token_limit = token_limit
        self.root_thread_id = root_thread_id
        self.root_turn_id: str | None = None
        self.root_prompt_turn_status: str | None = None
        self.compaction_canary_authorized = False
        self.compaction_turn_id: str | None = None
        self.compaction_turn_status: str | None = None
        self.compaction_response_id: str | None = None
        self.threads: dict[str, dict[str, Any]] = {}
        # A child can be reactivated by a later collaboration message after an
        # earlier turn was explicitly interrupted.  The mutable per-thread
        # lifecycle fields below describe only the current/latest turn, so
        # retain every terminal turn independently for historical evidence.
        self.terminal_turn_lifecycles: dict[
            tuple[str, str], dict[str, Any]
        ] = {}
        self.responses: dict[str, dict[str, Any]] = {}
        self.aggregate = {field: 0 for field in self._SUM_FIELDS}
        self.notification_sequence = 0
        self.first_crossing: dict[str, Any] | None = None
        self.stop_reason: str | None = None
        self.interrupt_requested = False
        self.interrupt_request_ids: set[int] = set()
        self.invalid_reasons: list[str] = []
        self.raw_items_pending: dict[tuple[str, str], list[dict[str, Any]]] = {}
        self.raw_item_observations: dict[str, dict[str, Any]] = {}
        self.final_answer_agent_messages: dict[str, dict[str, Any]] = {}
        self.collaboration_message_observations: dict[str, dict[str, Any]] = {}
        self.suppressed_collaboration_wait_evidence: dict[str, dict[str, Any]] = {}
        self.superseded_by_collaboration_message_evidence: dict[
            str, dict[str, Any]
        ] = {}
        self.discarded_after_explicit_child_interrupt_evidence: dict[
            str, dict[str, Any]
        ] = {}
        self.dynamic_tool_starts: dict[str, dict[str, Any]] = {}
        self.raw_function_calls: dict[str, dict[str, Any]] = {}
        self.raw_custom_tool_calls: dict[str, dict[str, Any]] = {}
        self.delayed_tool_outputs: dict[tuple[str, str], dict[str, Any]] = {}
        self.raw_spawn_calls: dict[str, dict[str, Any]] = {}
        self.canonical_spawn_failures: dict[str, dict[str, Any]] = {}
        self.collab_spawn_calls: dict[str, dict[str, Any]] = {}
        self.subagent_activities: dict[str, dict[str, Any]] = {}
        self.subagent_interrupt_activities: dict[str, dict[str, Any]] = {}
        self.fork_policy_static: dict[str, Any] | None = None
        if fork_policy is not None:
            copied_policy = json.loads(json.dumps(fork_policy, ensure_ascii=False))
            if not isinstance(copied_policy, dict):
                raise RuntimeError("Ultra fork-policy record is not an object")
            expected_keys = set(ultra_fork_policy_static_record())
            if set(copied_policy) != expected_keys:
                raise RuntimeError("Ultra fork-policy record has the wrong fields")
            source_path = copied_policy.get("source_path")
            if not isinstance(source_path, str):
                raise RuntimeError("Ultra fork-policy source path is malformed")
            inside_home = str(PurePosixPath(source_path).parent.parent)
            if copied_policy != ultra_fork_policy_static_record(inside_home):
                raise RuntimeError("Ultra fork-policy record is not canonical")
            self.fork_policy_static = copied_policy
        self.fork_hook_started: dict[str, list[dict[str, Any]]] = {}
        self.fork_hook_completed: dict[str, list[dict[str, Any]]] = {}
        self.fork_hook_invalid_call_ids: set[str] = set()
        self.fork_hook_invalid_reasons: list[str] = []
        self.submission_boundary: dict[str, Any] | None = None
        self.provider_gate = provider_gate
        self.provider_gate_artifact_path = provider_gate_artifact_path
        self.provider_gate_final: dict[str, Any] | None = None
        self.provider_gate_terminal_snapshot: dict[str, Any] | None = None
        self.provider_gate_exact_for_usage = False
        self.provider_usage_reconciliation: dict[str, Any] | None = None
        self.adapter_teardown: dict[str, Any] | None = None
        self._reconciling_explicit_child_interrupts = False
        self._register_thread(root_thread_id, parent_id=None, agent_path="root")

    def _register_thread(
        self,
        thread_id: str,
        *,
        parent_id: str | None,
        agent_path: str | None,
    ) -> None:
        existing = self.threads.get(thread_id)
        if existing is not None:
            existing_parent = existing.get("parent_id")
            if parent_id is not None:
                if existing_parent not in (None, parent_id):
                    raise RuntimeError("Codex child thread was assigned two parents")
                existing["parent_id"] = parent_id
                existing["provisional"] = False
            if agent_path is not None:
                prior_path = existing.get("agent_path")
                if prior_path not in (None, agent_path):
                    raise RuntimeError("Codex child thread changed agent path")
                existing["agent_path"] = agent_path
            self._assert_acyclic(thread_id)
            return
        self.threads[thread_id] = {
            "parent_id": parent_id,
            "agent_path": agent_path,
            "provisional": parent_id is None and thread_id != self.root_thread_id,
            "spawn_call_id": None,
            "spawn_parent_turn_id": None,
            "spawn_parent_response_id": None,
            "spawn_fork_turns": None,
            "spawn_fork_semantics": None,
            "spawn_binding_status": (
                "root_zero" if thread_id == self.root_thread_id else "unresolved"
            ),
            "expected_cumulative_baseline": (
                {field: 0 for field in self._SUM_FIELDS}
                if thread_id == self.root_thread_id
                else None
            ),
            "turn_seen": False,
            "active_turn_id": None,
            "turn_status": None,
            "terminal_turn_id": None,
            "turn_completed_at_unix_ns": None,
            "turn_completed_at_monotonic_ns": None,
            "turn_completed_event_unix_ns": None,
            "thread_status": None,
            "response_ids": [],
            "raw_sum": {field: 0 for field in self._SUM_FIELDS},
            "last_cumulative": None,
            "cumulative_observation_count": 0,
        }
        self._assert_acyclic(thread_id)

    def _provisional_thread(self, thread_id: str) -> dict[str, Any]:
        if thread_id not in self.threads:
            self._register_thread(thread_id, parent_id=None, agent_path=None)
        return self.threads[thread_id]

    def _assert_acyclic(self, start: str) -> None:
        seen: set[str] = set()
        current: str | None = start
        while current is not None:
            if current in seen:
                raise RuntimeError("Codex subagent thread graph contains a cycle")
            seen.add(current)
            entry = self.threads.get(current)
            current = entry.get("parent_id") if entry is not None else None

    def _link_child(self, parent_id: str, child_id: str, agent_path: Any) -> None:
        if not parent_id or not child_id or parent_id == child_id:
            raise RuntimeError("Codex app-server emitted an invalid subagent edge")
        self._provisional_thread(parent_id)
        normalized_path = agent_path if isinstance(agent_path, str) and agent_path else None
        self._register_thread(
            child_id,
            parent_id=parent_id,
            agent_path=normalized_path,
        )

    def _invalidate(self, reason: str) -> None:
        if reason not in self.invalid_reasons:
            self.invalid_reasons.append(reason)

    @classmethod
    def _usage_add(
        cls, left: Mapping[str, int], right: Mapping[str, int]
    ) -> dict[str, int]:
        return {field: int(left[field]) + int(right[field]) for field in cls._SUM_FIELDS}

    @classmethod
    def _usage_subtract(
        cls, left: Mapping[str, int], right: Mapping[str, int]
    ) -> dict[str, int]:
        result = {field: int(left[field]) - int(right[field]) for field in cls._SUM_FIELDS}
        if any(value < 0 for value in result.values()):
            raise RuntimeError("response usage exceeds its thread raw-response sum")
        return result

    @classmethod
    def _valid_usage_breakdown(cls, value: Mapping[str, int]) -> bool:
        """Return whether a derived snake-case usage value is normalized."""

        return bool(
            all(
                isinstance(value.get(field), int)
                and not isinstance(value[field], bool)
                and value[field] >= 0
                for field in cls._SUM_FIELDS
            )
            and value["cached_input_tokens"] <= value["input_tokens"]
            and value["cache_write_input_tokens"] <= value["input_tokens"]
            and value["reasoning_output_tokens"] <= value["output_tokens"]
            and value["total_tokens"]
            == value["input_tokens"] + value["output_tokens"]
        )

    @staticmethod
    def _normalize_spawn_fork(arguments: Any) -> tuple[str | None, str]:
        """Return the frozen fork value and its auditable accounting semantics."""

        try:
            parsed = json.loads(arguments) if isinstance(arguments, str) else None
        except json.JSONDecodeError:
            return None, "invalid_arguments"
        if not isinstance(parsed, Mapping):
            return None, "invalid_arguments"
        fork_turns = parsed.get("fork_turns", "all")
        if fork_turns == "none":
            return "none", "no_history_zero"
        if fork_turns == "all":
            return "all", "full_history_parent_pre_response"
        if (
            isinstance(fork_turns, str)
            and re.fullmatch(r"[1-9][0-9]*", fork_turns) is not None
        ):
            # The app-server exposes no per-turn token projection from which a
            # positive suffix can be reconstructed exactly.  Never guess it.
            return fork_turns, "unsupported_positive_turn_suffix"
        return None, "invalid_fork_turns"

    def _fork_hook_run_prefix(self) -> str | None:
        if self.fork_policy_static is None:
            return None
        return (
            f"pre-tool-use:{ULTRA_FORK_POLICY_DISPLAY_ORDER}:"
            f"{self.fork_policy_static['source_path']}:"
        )

    def _record_fork_hook_invalid(self, call_id: str | None, reason: str) -> None:
        if isinstance(call_id, str) and call_id:
            self.fork_hook_invalid_call_ids.add(call_id)
        if reason not in self.fork_hook_invalid_reasons:
            self.fork_hook_invalid_reasons.append(reason)
        self._invalidate(reason)

    def _observe_fork_policy_hook(
        self, method: str, params: Any
    ) -> bool:
        """Authenticate one pinned hook lifecycle event and retain its call edge."""

        if self.fork_policy_static is None:
            return False
        if method not in (
            ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION,
            ULTRA_FORK_POLICY_HOOK_NOTIFICATION,
        ):
            return False
        if not isinstance(params, Mapping) or not isinstance(params.get("run"), Mapping):
            self._record_fork_hook_invalid(None, "malformed Ultra fork-policy hook event")
            return True
        run = params["run"]
        expected_source_path = self.fork_policy_static["source_path"]
        prefix = self._fork_hook_run_prefix()
        assert prefix is not None
        run_id = run.get("id")
        source_path = run.get("sourcePath")
        relevant = source_path == expected_source_path or (
            isinstance(run_id, str) and run_id.startswith(prefix)
        )
        if not relevant:
            return False
        call_id = run_id[len(prefix) :] if isinstance(run_id, str) and run_id.startswith(prefix) else None
        exact_identity = bool(
            isinstance(call_id, str)
            and re.fullmatch(r"call_[A-Za-z0-9_-]{1,120}", call_id) is not None
            and run.get("eventName") == ULTRA_FORK_POLICY_HOOK_EVENT_NAME
            and run.get("executionMode") == ULTRA_FORK_POLICY_EXECUTION_MODE
            and run.get("handlerType") == ULTRA_FORK_POLICY_HANDLER_TYPE
            and run.get("scope") == ULTRA_FORK_POLICY_SCOPE
            and run.get("source") == ULTRA_FORK_POLICY_SOURCE
            and source_path == expected_source_path
            and run.get("displayOrder") == ULTRA_FORK_POLICY_DISPLAY_ORDER
            and run.get("statusMessage") is None
        )
        thread_id = params.get("threadId")
        turn_id = params.get("turnId")
        started_at = run.get("startedAt")
        entries = run.get("entries")
        if (
            not exact_identity
            or not isinstance(thread_id, str)
            or not thread_id
            or not isinstance(turn_id, str)
            or not turn_id
            or isinstance(started_at, bool)
            or not isinstance(started_at, int)
            or started_at < 0
            or not isinstance(entries, list)
        ):
            self._record_fork_hook_invalid(
                call_id, f"fork-policy hook {call_id or 'unknown'} has malformed identity"
            )
            return True
        status = run.get("status")
        completed_at = run.get("completedAt")
        duration_ms = run.get("durationMs")
        if method == ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION:
            exact_phase = (
                status == "running"
                and entries == []
                and completed_at is None
                and duration_ms is None
            )
        else:
            exact_phase = bool(
                status in (
                    ULTRA_FORK_POLICY_ALLOW_STATUS,
                    ULTRA_FORK_POLICY_BLOCK_STATUS,
                    "failed",
                    "stopped",
                )
                and not isinstance(completed_at, bool)
                and isinstance(completed_at, int)
                and completed_at >= started_at
                and not isinstance(duration_ms, bool)
                and isinstance(duration_ms, int)
                and duration_ms >= 0
            )
        if not exact_phase:
            self._record_fork_hook_invalid(
                call_id, f"fork-policy hook {call_id} has malformed {method} state"
            )
            return True
        record = {
            "call_id": call_id,
            "run_id": run_id,
            "source_path": source_path,
            "thread_id": thread_id,
            "turn_id": turn_id,
            "status": status,
            "entries": json.loads(json.dumps(entries, ensure_ascii=False)),
            "started_at": started_at,
            "completed_at": completed_at,
            "duration_ms": duration_ms,
        }
        destination = (
            self.fork_hook_started
            if method == ULTRA_FORK_POLICY_HOOK_STARTED_NOTIFICATION
            else self.fork_hook_completed
        )
        destination.setdefault(str(call_id), []).append(record)
        if len(destination[str(call_id)]) != 1:
            self._record_fork_hook_invalid(
                str(call_id), f"fork-policy hook {call_id} was observed more than once"
            )
        self._resolve_spawn_links()
        return True

    def _fork_policy_call_evidence(
        self, call_id: str, raw: Mapping[str, Any]
    ) -> dict[str, Any]:
        started = self.fork_hook_started.get(call_id, [])
        completed = self.fork_hook_completed.get(call_id, [])
        started_record = started[0] if len(started) == 1 else None
        completed_record = completed[0] if len(completed) == 1 else None
        identity_record = completed_record or started_record
        hook_status = completed_record.get("status") if completed_record else None
        feedback: str | None = None
        decision: str | None = None
        expected_feedback = ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
            call_id=call_id
        )
        if completed_record is not None:
            entries = completed_record.get("entries")
            if hook_status == ULTRA_FORK_POLICY_ALLOW_STATUS and entries == []:
                decision = ULTRA_FORK_POLICY_ALLOW_DECISION
            elif hook_status == ULTRA_FORK_POLICY_BLOCK_STATUS and entries == [
                {"kind": "feedback", "text": expected_feedback}
            ]:
                decision = ULTRA_FORK_POLICY_BLOCK_DECISION
                feedback = expected_feedback
        exact_counts = len(started) == 1 and len(completed) == 1
        exact_pair = bool(
            exact_counts
            and started_record is not None
            and completed_record is not None
            and all(
                started_record.get(field) == completed_record.get(field)
                for field in (
                    "call_id",
                    "run_id",
                    "source_path",
                    "thread_id",
                    "turn_id",
                    "started_at",
                )
            )
            and started_record.get("thread_id") == raw.get("parent_thread_id")
            and started_record.get("turn_id") == raw.get("parent_turn_id")
        )
        expects_allow = raw.get("fork_semantics") in (
            "no_history_zero",
            "full_history_parent_pre_response",
        )
        child_activity = call_id in self.subagent_activities
        collab_activity = call_id in self.collab_spawn_calls
        decision_mismatch = decision is not None and (
            (decision == ULTRA_FORK_POLICY_ALLOW_DECISION) != expects_allow
        )
        invalid = bool(
            call_id in self.fork_hook_invalid_call_ids
            or (completed_record is not None and decision is None)
            or (exact_counts and not exact_pair)
            or decision_mismatch
        )
        if decision == ULTRA_FORK_POLICY_BLOCK_DECISION and (
            child_activity or collab_activity
        ):
            invalid = True
        if invalid:
            resolution_status = ULTRA_FORK_POLICY_INVALID_RESOLUTION_STATUS
        elif not exact_pair or decision is None:
            resolution_status = ULTRA_FORK_POLICY_AWAITING_HOOK_STATUS
        elif decision == ULTRA_FORK_POLICY_BLOCK_DECISION:
            resolution_status = ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS
        else:
            raw_resolution = raw.get("resolution_status")
            resolution_status = (
                raw_resolution
                if raw_resolution in ("resolved_child", "failed_without_child")
                else ULTRA_FORK_POLICY_ALLOWED_RESOLUTION_STATUS
            )
        return {
            "call_id": call_id,
            "parent_thread_id": raw.get("parent_thread_id"),
            "parent_turn_id": raw.get("parent_turn_id"),
            "parent_response_id": raw.get("parent_response_id"),
            "fork_turns": raw.get("fork_turns"),
            "fork_semantics": raw.get("fork_semantics"),
            "hook_run_id": identity_record.get("run_id") if identity_record else None,
            "hook_source_path": (
                identity_record.get("source_path") if identity_record else None
            ),
            "hook_thread_id": identity_record.get("thread_id") if identity_record else None,
            "hook_turn_id": identity_record.get("turn_id") if identity_record else None,
            "hook_started_observed": len(started) > 0,
            "hook_started_count": len(started),
            "hook_completed_observed": len(completed) > 0,
            "hook_completed_count": len(completed),
            "hook_status": hook_status,
            "decision": decision,
            "feedback": feedback,
            "resolution_status": resolution_status,
            "child_activity_observed": child_activity or collab_activity,
        }

    def _index_raw_function_calls(
        self, response_id: str, response: Mapping[str, Any]
    ) -> None:
        raw_items = response.get("raw_items")
        if not isinstance(raw_items, list):
            raise RuntimeError("raw response record lacks its response items")
        for item in raw_items:
            if not isinstance(item, Mapping) or item.get("type") != "function_call":
                continue
            item_id = item.get("id")
            call_id = item.get("call_id")
            name = item.get("name")
            namespace = item.get("namespace")
            if (
                not isinstance(item_id, str)
                or not item_id
                or not isinstance(call_id, str)
                or not call_id
                or item_id == call_id
                or not isinstance(name, str)
                or not name
            ):
                raise RuntimeError("Codex raw function call lacks an identity")
            record = {
                "call_type": "function_call",
                "item_id": item_id,
                "call_id": call_id,
                "name": name,
                "namespace": namespace,
                "arguments": item.get("arguments"),
                "parent_thread_id": response["thread_id"],
                "parent_turn_id": response["turn_id"],
                "parent_response_id": response_id,
                "parent_response_sequence": response["sequence"],
                "parent_pre_response_raw_sum": dict(
                    response["pre_response_raw_sum"]
                ),
            }
            prior = self.raw_function_calls.get(call_id)
            if prior is not None:
                if prior != record:
                    raise RuntimeError("Codex reused a raw function-call id inconsistently")
                continue
            if call_id in self.raw_custom_tool_calls:
                raise RuntimeError("Codex reused a call id across raw tool-call types")
            self.raw_function_calls[call_id] = record
            is_spawn_name = name in ("spawn_agent", "collaboration.spawn_agent")
            if not is_spawn_name:
                continue
            fork_turns, fork_semantics = self._normalize_spawn_fork(
                item.get("arguments")
            )
            spawn_record = {
                **record,
                "fork_turns": fork_turns,
                "fork_semantics": fork_semantics,
                "namespace_supported": namespace in (None, "", "collaboration"),
                "resolution_status": "awaiting_subagent_activity",
            }
            self.raw_spawn_calls[call_id] = spawn_record

    def _index_raw_custom_tool_calls(
        self, response_id: str, response: Mapping[str, Any]
    ) -> None:
        """Index completed outer calls so delayed outputs can be segmented safely."""

        raw_items = response.get("raw_items")
        if not isinstance(raw_items, list):
            raise RuntimeError("raw response record lacks its response items")
        for item in raw_items:
            if not isinstance(item, Mapping) or item.get("type") != "custom_tool_call":
                continue
            item_id = item.get("id")
            call_id = item.get("call_id")
            name = item.get("name")
            if (
                not isinstance(item_id, str)
                or not item_id
                or not isinstance(call_id, str)
                or not call_id
                or item_id == call_id
                or not isinstance(name, str)
                or not name
                or item.get("status") != "completed"
            ):
                raise RuntimeError("Codex raw custom tool call lacks a completed identity")
            record = {
                "call_type": "custom_tool_call",
                "item_id": item_id,
                "call_id": call_id,
                "name": name,
                "namespace": item.get("namespace"),
                "parent_thread_id": response["thread_id"],
                "parent_turn_id": response["turn_id"],
                "parent_response_id": response_id,
                "parent_response_sequence": response["sequence"],
            }
            prior = self.raw_custom_tool_calls.get(call_id)
            if prior is not None:
                if prior != record:
                    raise RuntimeError(
                        "Codex reused a raw custom-tool call id inconsistently"
                    )
                continue
            if call_id in self.raw_function_calls:
                raise RuntimeError("Codex reused a call id across raw tool-call types")
            self.raw_custom_tool_calls[call_id] = record

    def _consume_delayed_tool_output(
        self,
        *,
        thread_id: str,
        turn_id: str,
        item: Mapping[str, Any],
        observed_at_unix_ns: int,
        observed_at_monotonic_ns: int,
    ) -> None:
        """Consume only a prior completed response's uniquely bound tool output."""

        output_type = item.get("type")
        item_id = item.get("id")
        call_id = item.get("call_id")
        if (
            not isinstance(item_id, str)
            or not item_id
            or not isinstance(call_id, str)
            or not call_id
            or item_id == call_id
        ):
            raise RuntimeError("delayed tool output lacks distinct identities")
        if output_type == "custom_tool_call_output":
            prior_call = self.raw_custom_tool_calls.get(call_id)
            expected_call_type = "custom_tool_call"
        elif output_type == "function_call_output":
            prior_call = self.raw_function_calls.get(call_id)
            expected_call_type = "function_call"
        else:
            raise RuntimeError("unsupported delayed tool-output type")
        if (
            not isinstance(prior_call, Mapping)
            or prior_call.get("call_type") != expected_call_type
            or prior_call.get("parent_thread_id") != thread_id
            or prior_call.get("parent_turn_id") != turn_id
            or prior_call.get("parent_response_id") not in self.responses
            or prior_call.get("parent_response_sequence", 0)
            > self.notification_sequence
        ):
            raise RuntimeError(
                "delayed tool output is not bound to a prior completed response"
            )
        metadata = item.get("internal_chat_message_metadata_passthrough")
        if metadata is not None and (
            not isinstance(metadata, Mapping) or metadata.get("turn_id") != turn_id
        ):
            raise RuntimeError("delayed tool output has mismatched turn metadata")
        if item.get("name") not in (None, prior_call.get("name")):
            raise RuntimeError("delayed tool output has a mismatched tool name")
        if self.raw_items_pending.get((thread_id, turn_id)):
            raise RuntimeError(
                "delayed tool output arrived after the next raw response began"
            )
        output_key = (str(output_type), call_id)
        if output_key in self.delayed_tool_outputs:
            raise RuntimeError("duplicate delayed tool output")
        self.delayed_tool_outputs[output_key] = {
            "output_type": output_type,
            "item_id": item_id,
            "call_id": call_id,
            "prior_call_item_id": prior_call["item_id"],
            "prior_response_id": prior_call["parent_response_id"],
            "prior_response_sequence": prior_call["parent_response_sequence"],
            "thread_id": thread_id,
            "turn_id": turn_id,
            "item_sha256": hashlib.sha256(
                json.dumps(
                    item, sort_keys=True, separators=(",", ":"), ensure_ascii=False
                ).encode("utf-8")
            ).hexdigest(),
            "observed_at_unix_ns": observed_at_unix_ns,
            "observed_at_monotonic_ns": observed_at_monotonic_ns,
        }
        if (
            output_type == "function_call_output"
            and call_id in self.raw_spawn_calls
            and item.get("output") == ULTRA_SPAWN_AGENT_THREAD_LIMIT_FAILURE_OUTPUT
        ):
            self.canonical_spawn_failures[call_id] = {
                "call_id": call_id,
                "failure_kind": ULTRA_SPAWN_AGENT_THREAD_LIMIT_FAILURE_KIND,
                "output_item_id": item_id,
                "output_item_sha256": self.delayed_tool_outputs[output_key][
                    "item_sha256"
                ],
                "prior_call_item_id": prior_call["item_id"],
                "prior_response_id": prior_call["parent_response_id"],
                "thread_id": thread_id,
                "turn_id": turn_id,
            }
        self._resolve_spawn_links()

    def _observe_collab_spawn(
        self, method: str, params: Mapping[str, Any], item: Mapping[str, Any]
    ) -> None:
        call_id = item.get("id")
        sender = item.get("senderThreadId")
        receivers = item.get("receiverThreadIds")
        turn_id = params.get("turnId")
        event_thread_id = params.get("threadId")
        status = item.get("status")
        if (
            not isinstance(call_id, str)
            or not call_id
            or not isinstance(sender, str)
            or not sender
            or not isinstance(turn_id, str)
            or not turn_id
            or event_thread_id != sender
            or not isinstance(receivers, list)
            or any(not isinstance(value, str) or not value for value in receivers)
            or len(set(receivers)) != len(receivers)
            or status not in ("inProgress", "completed", "failed")
        ):
            raise RuntimeError("Codex app-server emitted malformed spawnAgent activity")
        if method == "item/started" and status != "inProgress":
            raise RuntimeError("started spawnAgent item has a terminal status")
        if method == "item/completed" and status not in ("completed", "failed"):
            raise RuntimeError("completed spawnAgent item lacks a terminal status")
        if len(receivers) > 1:
            self._invalidate(f"spawn call {call_id} named multiple receiver threads")
        record = self.collab_spawn_calls.get(call_id)
        canonical = {
            "call_id": call_id,
            "sender_thread_id": sender,
            "parent_turn_id": turn_id,
            "receiver_thread_ids": list(receivers),
            "status": status,
            "completed_observed": method == "item/completed",
        }
        if record is None:
            record = canonical
            self.collab_spawn_calls[call_id] = record
        else:
            if (
                record["sender_thread_id"] != sender
                or record["parent_turn_id"] != turn_id
                or (
                    record["receiver_thread_ids"]
                    and receivers
                    and record["receiver_thread_ids"] != receivers
                )
            ):
                raise RuntimeError("Codex spawnAgent item changed identity")
            if receivers:
                record["receiver_thread_ids"] = list(receivers)
            if method == "item/completed":
                record["completed_observed"] = True
                record["status"] = status
        if len(record["receiver_thread_ids"]) == 1:
            self._link_child(
                sender,
                str(record["receiver_thread_ids"][0]),
                agent_path=None,
            )
        self._resolve_spawn_links()

    def _resolve_spawn_links(self) -> None:
        """Resolve the pinned V2 raw-call/activity edge through nested ancestry.

        Pinned 0.146 runtime evidence establishes that a successful V2 spawn is
        normalized as ``subAgentActivity`` with ``item.id == call_id``.  A
        schema-backed ``collabAgentToolCall`` spawn record is accepted only as
        optional corroboration; pinned V2 does not normally emit one.
        """

        changed = True
        while changed:
            changed = False
            for call_id in sorted(
                set(self.raw_spawn_calls)
                | set(self.canonical_spawn_failures)
                | set(self.subagent_activities)
                | set(self.collab_spawn_calls)
            ):
                raw = self.raw_spawn_calls.get(call_id)
                canonical_failure = self.canonical_spawn_failures.get(call_id)
                activity = self.subagent_activities.get(call_id)
                collab = self.collab_spawn_calls.get(call_id)
                if (
                    raw is None
                    and (activity is not None or collab is not None)
                    and call_id in self.raw_function_calls
                ):
                    self._invalidate(
                        f"spawn activity {call_id} is bound to a non-spawn raw call"
                    )
                if raw is None:
                    continue
                if self.fork_policy_static is not None:
                    policy_evidence = self._fork_policy_call_evidence(call_id, raw)
                    policy_status = policy_evidence["resolution_status"]
                    if policy_status == ULTRA_FORK_POLICY_INVALID_RESOLUTION_STATUS:
                        raw["resolution_status"] = policy_status
                        self._record_fork_hook_invalid(
                            call_id,
                            f"spawn call {call_id} lacks exact fork-policy enforcement",
                        )
                        continue
                    if policy_status == ULTRA_FORK_POLICY_AWAITING_HOOK_STATUS:
                        raw["resolution_status"] = policy_status
                        continue
                    if policy_status == ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS:
                        raw["resolution_status"] = policy_status
                        continue
                    if raw.get("resolution_status") in (
                        "awaiting_subagent_activity",
                        ULTRA_FORK_POLICY_AWAITING_HOOK_STATUS,
                        ULTRA_FORK_POLICY_ALLOWED_RESOLUTION_STATUS,
                    ):
                        raw["resolution_status"] = (
                            ULTRA_FORK_POLICY_ALLOWED_RESOLUTION_STATUS
                        )
                if canonical_failure is not None:
                    consistent_collab_failure = bool(
                        collab is None
                        or (
                            collab["completed_observed"]
                            and collab["status"] == "failed"
                            and collab["sender_thread_id"]
                            == raw["parent_thread_id"]
                            and collab["parent_turn_id"] == raw["parent_turn_id"]
                            and collab["receiver_thread_ids"] == []
                        )
                    )
                    if activity is not None or not consistent_collab_failure:
                        raw["resolution_status"] = (
                            "invalid_failed_spawn_child_activity"
                        )
                        self._invalidate(
                            f"failed spawn call {call_id} produced contradictory "
                            "child activity"
                        )
                    elif not raw["namespace_supported"]:
                        raw["resolution_status"] = "unsupported_namespace"
                        self._invalidate(
                            f"failed spawn call {call_id} used an unsupported namespace"
                        )
                    elif raw["fork_semantics"] in (
                        "invalid_arguments",
                        "invalid_fork_turns",
                        "unsupported_positive_turn_suffix",
                    ):
                        raw["resolution_status"] = raw["fork_semantics"]
                        self._invalidate(
                            f"failed spawn call {call_id} has non-projectable "
                            "fork semantics"
                        )
                    else:
                        raw["resolution_status"] = "failed_without_child"
                    continue
                if (
                    activity is None
                    and collab is not None
                    and collab["completed_observed"]
                    and collab["status"] == "failed"
                ):
                    if collab["receiver_thread_ids"]:
                        self._invalidate(
                            f"failed spawn call {call_id} named a receiver thread"
                        )
                        raw["resolution_status"] = "invalid_failed_receiver"
                    else:
                        raw["resolution_status"] = "failed_without_child"
                    continue
                if activity is None:
                    continue
                if (
                    raw["parent_thread_id"] != activity["parent_thread_id"]
                    or raw["parent_turn_id"] != activity["parent_turn_id"]
                ):
                    raw["resolution_status"] = "identity_mismatch"
                    self._invalidate(
                        f"spawn call {call_id} raw/activity parent identity mismatch"
                    )
                    continue
                child_id = str(activity["child_thread_id"])
                if collab is not None:
                    if not collab["completed_observed"]:
                        raw["resolution_status"] = "incomplete_collab_corroboration"
                        continue
                    if (
                        collab["status"] != "completed"
                        or collab["sender_thread_id"] != raw["parent_thread_id"]
                        or collab["parent_turn_id"] != raw["parent_turn_id"]
                        or collab["receiver_thread_ids"] != [child_id]
                    ):
                        raw["resolution_status"] = "collab_corroboration_mismatch"
                        self._invalidate(
                            f"spawn call {call_id} has contradictory collab evidence"
                        )
                        continue
                if not raw["namespace_supported"]:
                    raw["resolution_status"] = "unsupported_namespace"
                    self._invalidate(
                        f"spawn call {call_id} used an unsupported namespace"
                    )
                    continue
                semantics = raw["fork_semantics"]
                if semantics in (
                    "invalid_arguments",
                    "invalid_fork_turns",
                    "unsupported_positive_turn_suffix",
                ):
                    raw["resolution_status"] = semantics
                    self._invalidate(
                        f"spawn call {call_id} has non-projectable fork semantics"
                    )
                    continue
                parent = self.threads.get(str(raw["parent_thread_id"]))
                if parent is None:
                    raw["resolution_status"] = "unresolved_parent_thread"
                    continue
                parent_baseline = parent.get("expected_cumulative_baseline")
                if semantics == "no_history_zero":
                    expected = {field: 0 for field in self._SUM_FIELDS}
                elif isinstance(parent_baseline, Mapping):
                    expected = self._usage_add(
                        parent_baseline, raw["parent_pre_response_raw_sum"]
                    )
                else:
                    raw["resolution_status"] = "unresolved_parent_baseline"
                    continue
                self._link_child(
                    str(raw["parent_thread_id"]),
                    child_id,
                    activity.get("agent_path"),
                )
                child = self.threads[child_id]
                prior_call_id = child.get("spawn_call_id")
                if prior_call_id not in (None, call_id):
                    raise RuntimeError("Codex child thread was assigned two spawn calls")
                prior_expected = child.get("expected_cumulative_baseline")
                if prior_expected is not None and prior_expected != expected:
                    raise RuntimeError("Codex child inherited two token baselines")
                child.update(
                    {
                        "spawn_call_id": call_id,
                        "spawn_parent_turn_id": raw["parent_turn_id"],
                        "spawn_parent_response_id": raw["parent_response_id"],
                        "spawn_fork_turns": raw["fork_turns"],
                        "spawn_fork_semantics": semantics,
                        "spawn_binding_status": "resolved",
                        "expected_cumulative_baseline": expected,
                    }
                )
                if raw.get("resolution_status") != "resolved_child":
                    raw["resolution_status"] = "resolved_child"
                    changed = True

    def _observe_raw_response(self, event: Mapping[str, Any]) -> bool:
        parsed = normalized_raw_response(event)
        if parsed is None:
            return False
        response_id, thread_id, turn_id, usage = parsed
        if (
            thread_id == self.root_thread_id
            and self.root_turn_id is not None
            and turn_id != self.root_turn_id
        ):
            if (
                not self.compaction_canary_authorized
                or self.compaction_turn_id != turn_id
                or self.compaction_response_id is not None
            ):
                raise RuntimeError(
                    "Codex emitted an unauthenticated second root-turn response"
                )
            self.compaction_response_id = response_id
        thread = self._provisional_thread(thread_id)
        prior = self.responses.get(response_id)
        canonical = {
            "thread_id": thread_id,
            "turn_id": turn_id,
            "usage": usage,
        }
        if prior is not None:
            comparable = {
                "thread_id": prior["thread_id"],
                "turn_id": prior["turn_id"],
                "usage": prior["usage"],
            }
            if comparable != canonical:
                raise RuntimeError("Codex app-server reused a response id inconsistently")
            return False
        if self.provider_gate is not None:
            self.provider_gate.crossbind_appserver_response(
                response_id,
                usage,
                thread_id=thread_id,
                turn_id=turn_id,
                event_sequence=self.notification_sequence + 1,
            )
            self._reconcile_suppressed_waits_for_successor(
                thread_id=thread_id,
                turn_id=turn_id,
                successor_response_id=response_id,
            )
            self._reconcile_superseded_responses_for_successor(
                thread_id=thread_id,
                turn_id=turn_id,
                successor_response_id=response_id,
            )
        self.notification_sequence += 1
        record = {
            **canonical,
            "sequence": self.notification_sequence,
            "observed_at_unix_ns": time.time_ns(),
            "observed_at_monotonic_ns": time.monotonic_ns(),
            "raw_items": self.raw_items_pending.pop((thread_id, turn_id), []),
            "pre_response_raw_sum": dict(thread["raw_sum"]),
        }
        self.responses[response_id] = record
        self._index_raw_function_calls(response_id, record)
        self._index_raw_custom_tool_calls(response_id, record)
        thread["response_ids"].append(response_id)
        for field in self._SUM_FIELDS:
            thread["raw_sum"][field] += usage[field]
            self.aggregate[field] += usage[field]
        self._resolve_spawn_links()
        crossing_now = False
        crossing_tokens = self.aggregate["total_tokens"]
        gate_crossing: Mapping[str, Any] | None = None
        if self.provider_gate is not None:
            gate_state = _provider_gate_state_view(self.provider_gate.snapshot())
            candidate_crossing = gate_state.get("crossing")
            if isinstance(candidate_crossing, Mapping):
                gate_crossing = candidate_crossing
                candidate_tokens = candidate_crossing.get("completed_tokens")
                if isinstance(candidate_tokens, int) and not isinstance(
                    candidate_tokens, bool
                ):
                    crossing_tokens = candidate_tokens
            self.reconcile_discarded_after_explicit_child_interrupts()
        if self.first_crossing is None and (
            (
                gate_crossing is not None
                and gate_crossing.get("response_id") == response_id
                and crossing_tokens >= self.token_limit
            )
            or (
                self.provider_gate is None
                and crossing_tokens >= self.token_limit
            )
        ):
            crossing_now = True
            self.first_crossing = {
                "response_id": response_id,
                "notification_sequence": self.notification_sequence,
                "observed_at_unix_ns": record["observed_at_unix_ns"],
                "tokens": crossing_tokens,
                "active_thread_ids": sorted(self.active_turns()),
            }
            self.stop_reason = "token_limit"
        return crossing_now

    def _observe_cumulative(self, event: Mapping[str, Any]) -> None:
        params = event.get("params")
        if not isinstance(params, Mapping):
            raise RuntimeError("Codex app-server emitted malformed cumulative usage")
        thread_id = params.get("threadId")
        turn_id = params.get("turnId")
        token_usage = params.get("tokenUsage")
        total = token_usage.get("total") if isinstance(token_usage, Mapping) else None
        if not isinstance(thread_id, str) or not thread_id or not isinstance(turn_id, str) or not turn_id:
            raise RuntimeError("Codex cumulative usage lacks a thread/turn identity")
        usage = _normalized_breakdown(total)
        if usage is None:
            raise RuntimeError("Codex app-server emitted malformed cumulative usage")
        thread = self._provisional_thread(thread_id)
        prior_cumulative = thread.get("last_cumulative")
        if isinstance(prior_cumulative, Mapping) and any(
            usage[field] < prior_cumulative[field] for field in self._SUM_FIELDS
        ):
            raise RuntimeError("thread cumulative usage moved backwards")
        thread["last_cumulative"] = usage
        thread["cumulative_observation_count"] += 1

    def _validated_collaboration_message_envelope(
        self,
        *,
        thread_id: str,
        turn_id: str,
        item: Mapping[str, Any],
    ) -> tuple[str, str, str, str, bool] | None:
        """Validate one routed ``MESSAGE``/``FINAL_ANSWER`` envelope.

        A child can legitimately finish with no textual payload.  The pinned
        app server still emits the exact routed ``FINAL_ANSWER`` header in
        that case.  Such an item is authenticated here but is not evidence
        that can explain a suppressed provider response or wait result.
        """

        if item.get("type") != "agent_message":
            return None
        content = item.get("content")
        first = content[0] if isinstance(content, list) and content else None
        text = first.get("text") if isinstance(first, Mapping) else None
        message_type = next(
            (
                candidate
                for candidate in ("MESSAGE", "FINAL_ANSWER")
                if isinstance(text, str)
                and text.startswith(f"Message Type: {candidate}\n")
            ),
            None,
        )
        # NEW_TASK and ordinary model messages are outside the collaboration
        # reconciliation channel.
        if message_type is None:
            return None

        item_id = item.get("id")
        author = item.get("author")
        recipient = item.get("recipient")
        if not all(
            isinstance(value, str) and value
            for value in (item_id, author, recipient)
        ):
            raise RuntimeError("Codex inbound collaboration message lacks routing")
        assert isinstance(item_id, str)
        assert isinstance(author, str)
        assert isinstance(recipient, str)

        routed_thread = self.threads.get(thread_id)
        routed_agent_path = (
            "/root"
            if thread_id == self.root_thread_id
            else routed_thread.get("agent_path")
            if isinstance(routed_thread, Mapping)
            else None
        )
        known_agent_paths = {"/root"} | {
            str(thread["agent_path"])
            for candidate_thread_id, thread in self.threads.items()
            if candidate_thread_id != self.root_thread_id
            and thread.get("provisional") is False
            and thread.get("spawn_binding_status") == "resolved"
            and isinstance(thread.get("agent_path"), str)
            and str(thread["agent_path"]).startswith("/root/")
        }
        author_thread_ids = {
            candidate_thread_id
            for candidate_thread_id, thread in self.threads.items()
            if (
                (candidate_thread_id == self.root_thread_id and author == "/root")
                or thread.get("agent_path") == author
            )
        }
        adjacent_route = bool(
            isinstance(routed_thread, Mapping)
            and (
                routed_thread.get("parent_id") in author_thread_ids
                or any(
                    child.get("parent_id") == thread_id
                    and child.get("agent_path") == author
                    for child in self.threads.values()
                )
            )
        )
        if (
            not isinstance(routed_agent_path, str)
            or recipient != routed_agent_path
            or author not in known_agent_paths
            or not adjacent_route
        ):
            raise RuntimeError(
                "Codex collaboration message is not routed within the resolved tree"
            )

        metadata = item.get("internal_chat_message_metadata_passthrough")
        if not isinstance(metadata, Mapping) or metadata.get("turn_id") != turn_id:
            raise RuntimeError("Codex collaboration message has mismatched turn metadata")
        if (
            message_type == "FINAL_ANSWER"
            and thread_id == self.root_thread_id
            and recipient == "/root"
            and turn_id != self.root_turn_id
        ):
            raise RuntimeError("Codex child FINAL_ANSWER envelope is not canonical")
        if not isinstance(content, list) or not content:
            raise RuntimeError("Codex collaboration message has malformed content")
        first = content[0]
        if (
            not isinstance(first, Mapping)
            or set(first) != {"type", "text"}
            or first.get("type") != "input_text"
            or not isinstance(first.get("text"), str)
        ):
            raise RuntimeError("Codex collaboration message has malformed envelope")
        text = str(first["text"])
        expected_prefix = (
            f"Message Type: {message_type}\n"
            f"Task name: {recipient}\n"
            f"Sender: {author}\n"
            "Payload:\n"
        )
        plaintext = len(content) == 1 and bool(text[len(expected_prefix) :].strip())
        encrypted = False
        if len(content) == 2 and text == expected_prefix:
            second = content[1]
            encrypted = bool(
                isinstance(second, Mapping)
                and set(second) == {"type", "encrypted_content"}
                and second.get("type") == "encrypted_content"
                and isinstance(second.get("encrypted_content"), str)
                and second.get("encrypted_content")
            )
        empty_final_answer = (
            message_type == "FINAL_ANSWER"
            and len(content) == 1
            and text == expected_prefix
        )
        if not text.startswith(expected_prefix) or not (
            plaintext or encrypted or empty_final_answer
        ):
            raise RuntimeError("Codex collaboration message envelope is not canonical")
        return message_type, item_id, author, recipient, empty_final_answer

    def _capture_final_answer_agent_message(
        self,
        *,
        thread_id: str,
        turn_id: str,
        item: Mapping[str, Any],
        observed_at_unix_ns: int,
        observed_at_monotonic_ns: int,
    ) -> None:
        """Retain independently observed child FINAL_ANSWER evidence.

        Collaboration delivery can replace a root ``wait_agent`` output before
        app-server emits its raw-response completion.  Only the exact routed
        FINAL_ANSWER envelope is eligible to explain that suppression.
        """

        envelope = self._validated_collaboration_message_envelope(
            thread_id=thread_id,
            turn_id=turn_id,
            item=item,
        )
        if envelope is None or envelope[0] != "FINAL_ANSWER":
            return
        _, item_id, author, recipient, empty_final_answer = envelope
        # This older, narrower record explains only a child result delivered
        # to a root wait.  Other rooted FINAL_ANSWER routes are authenticated
        # by the general collaboration-message record below.
        if thread_id != self.root_thread_id or recipient != "/root":
            return
        if empty_final_answer:
            return
        canonical_item = json.dumps(
            item,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        ).encode("utf-8")
        observation = {
            "thread_id": thread_id,
            "turn_id": turn_id,
            "item_id": item_id,
            "item_sha256": hashlib.sha256(canonical_item).hexdigest(),
            "author": author,
            "recipient": recipient,
            "observed_at_unix_ns": observed_at_unix_ns,
            "observed_at_monotonic_ns": observed_at_monotonic_ns,
        }
        prior = self.final_answer_agent_messages.get(str(item_id))
        if prior is not None and prior != observation:
            raise RuntimeError("Codex child FINAL_ANSWER item id was reused")
        self.final_answer_agent_messages[str(item_id)] = observation

    def _capture_collaboration_message(
        self,
        *,
        thread_id: str,
        turn_id: str,
        item: Mapping[str, Any],
        observed_at_unix_ns: int,
        observed_at_monotonic_ns: int,
    ) -> None:
        """Retain one canonical rooted message that can supersede a reply.

        The pinned app server can deliver a ``MESSAGE`` or ``FINAL_ANSWER``
        between committing one rooted response and admitting that thread's
        immediate successor request.  This includes both child-to-root results
        and root-to-child follow-ups.  In that ordering the provider response
        remains billable but its ``rawResponse/completed`` event is replaced by
        the collaboration delivery.  We retain the complete item hash and
        routing/timing identity without persisting decrypted content.
        """

        envelope = self._validated_collaboration_message_envelope(
            thread_id=thread_id,
            turn_id=turn_id,
            item=item,
        )
        if envelope is None:
            return
        _, item_id, author, recipient, empty_final_answer = envelope
        if empty_final_answer:
            return
        canonical_item = json.dumps(
            item,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        ).encode("utf-8")
        observation = {
            "item_id": item_id,
            "item_sha256": hashlib.sha256(canonical_item).hexdigest(),
            "author": author,
            "recipient": recipient,
            "observed_at_unix_ns": observed_at_unix_ns,
            "observed_at_monotonic_ns": observed_at_monotonic_ns,
        }
        if set(observation) != set(COLLABORATION_MESSAGE_EVIDENCE_KEYS):
            raise RuntimeError("internal collaboration-message evidence mismatch")
        prior = self.collaboration_message_observations.get(str(item_id))
        if prior is not None and prior != observation:
            raise RuntimeError("Codex collaboration message item id was reused")
        self.collaboration_message_observations[str(item_id)] = observation

    def _completed_child_results_for_suppressed_wait(
        self, candidate: Mapping[str, Any]
    ) -> list[dict[str, Any]]:
        """Return eligible completed-child FINAL results in one wait window."""

        commit_unix_ns = candidate.get("commit_unix_ns")
        commit_monotonic_ns = candidate.get("commit_monotonic_ns")
        successor_unix_ns = candidate.get("successor_admitted_unix_ns")
        successor_monotonic_ns = candidate.get("successor_admitted_monotonic_ns")
        if any(
            isinstance(value, bool) or not isinstance(value, int) or value <= 0
            for value in (
                commit_unix_ns,
                commit_monotonic_ns,
                successor_unix_ns,
                successor_monotonic_ns,
            )
        ) or not (
            commit_unix_ns < successor_unix_ns
            and commit_monotonic_ns < successor_monotonic_ns
        ):
            raise RuntimeError("suppressed wait has no later successor admission")
        matches: list[dict[str, Any]] = []
        already_used = {
            item["agent_message_item_id"]
            for item in self.suppressed_collaboration_wait_evidence.values()
        }
        for observation in self.final_answer_agent_messages.values():
            item_id = observation["item_id"]
            if item_id in already_used:
                continue
            if (
                observation["thread_id"] != candidate.get("thread_id")
                or observation["turn_id"] != candidate.get("turn_id")
                or not (
                    commit_unix_ns < observation["observed_at_unix_ns"]
                    and observation["observed_at_unix_ns"]
                    + APP_SERVER_EVENT_TIME_RESOLUTION_NS
                    <= successor_unix_ns
                )
            ):
                continue
            child_matches = [
                child
                for child in self.threads.values()
                if child.get("parent_id") == self.root_thread_id
                and child.get("agent_path") == observation["author"]
                and child.get("provisional") is False
                and child.get("spawn_binding_status") == "resolved"
                and child.get("turn_status") == "completed"
                and isinstance(child.get("terminal_turn_id"), str)
                and isinstance(child.get("turn_completed_at_unix_ns"), int)
                and isinstance(child.get("turn_completed_at_monotonic_ns"), int)
                and child["turn_completed_at_monotonic_ns"]
                <= observation["observed_at_monotonic_ns"]
            ]
            if len(child_matches) == 1:
                matches.append(observation)
        return matches

    def _child_result_for_suppressed_wait(
        self, candidate: Mapping[str, Any]
    ) -> dict[str, Any]:
        """Return the sole child result inside one suppressed-wait window."""

        matches = self._completed_child_results_for_suppressed_wait(candidate)
        if len(matches) != 1:
            raise RuntimeError(
                "suppressed collaboration wait lacks one unique completed-child result"
            )
        observation = matches[0]
        evidence = {
            "response_id": candidate.get("response_id"),
            "provider_call_id": candidate.get("call_id"),
            "thread_id": candidate.get("thread_id"),
            "turn_id": candidate.get("turn_id"),
            "successor_response_id": candidate.get("successor_response_id"),
            "successor_call_id": candidate.get("successor_call_id"),
            "agent_message_item_id": observation["item_id"],
            "agent_message_sha256": observation["item_sha256"],
            "agent_message_author": observation["author"],
            "agent_message_recipient": observation["recipient"],
            "agent_message_observed_at_unix_ns": observation[
                "observed_at_unix_ns"
            ],
            "agent_message_observed_at_monotonic_ns": observation[
                "observed_at_monotonic_ns"
            ],
        }
        if set(evidence) != set(SUPPRESSED_COLLABORATION_WAIT_EVIDENCE_KEYS) or any(
            not isinstance(evidence[field], str) or not evidence[field]
            for field in (
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
            )
        ):
            raise RuntimeError("suppressed collaboration wait evidence is malformed")
        return evidence

    def _reconcile_suppressed_waits_for_successor(
        self, *, thread_id: str, turn_id: str, successor_response_id: str
    ) -> None:
        if self.provider_gate is None:
            return
        candidates = self.provider_gate.suppressed_collaboration_wait_candidates(
            thread_id, turn_id
        )
        if not isinstance(candidates, list):
            raise RuntimeError("provider gate returned malformed suppressed-wait candidates")
        selected = [
            candidate
            for candidate in candidates
            if isinstance(candidate, Mapping)
            and candidate.get("successor_response_id") == successor_response_id
        ]
        for candidate in selected:
            response_id = candidate.get("response_id")
            if not isinstance(response_id, str) or not response_id:
                raise RuntimeError("provider gate suppressed-wait candidate lacks identity")
            if response_id in self.suppressed_collaboration_wait_evidence:
                raise RuntimeError("provider gate repeated a suppressed-wait candidate")
            # An exact collaboration wait can also be displaced by an interim
            # MESSAGE rather than by a completed child's nonempty FINAL_ANSWER.
            # Leave that zero-match shape untouched here so the immediately
            # following general collaboration-message reconciler can bind it.
            # Ambiguous (>1) FINAL results still fail closed in the strict
            # helper below.
            completed_results = self._completed_child_results_for_suppressed_wait(
                candidate
            )
            if not completed_results:
                continue
            # The direct successor can sit beyond a chain of ordinary
            # collaboration-message replacements.  In that shape the broad
            # wait window may contain both an interim MESSAGE for this wait
            # and a later FINAL_ANSWER for the next response.  Do not consume
            # that later final here: leave the wait for the immediate-successor
            # reconciler, which partitions the chain into exact windows.
            completed_result_ids = {
                result["item_id"] for result in completed_results
            }
            collaboration_messages = (
                self._collaboration_messages_in_superseded_response_window(
                    candidate
                )
            )
            if any(
                message["item_id"] not in completed_result_ids
                for message in collaboration_messages
            ):
                continue
            evidence = self._child_result_for_suppressed_wait(candidate)
            self.provider_gate.crossbind_suppressed_collaboration_wait(
                response_id,
                thread_id,
                turn_id,
                successor_response_id,
            )
            self.suppressed_collaboration_wait_evidence[response_id] = evidence

    def _collaboration_messages_in_superseded_response_window(
        self, candidate: Mapping[str, Any]
    ) -> list[dict[str, Any]]:
        """Return unused rooted messages wholly inside one replacement window."""

        commit_unix_ns = candidate.get("commit_unix_ns")
        commit_monotonic_ns = candidate.get("commit_monotonic_ns")
        successor_unix_ns = candidate.get("successor_admitted_unix_ns")
        successor_monotonic_ns = candidate.get("successor_admitted_monotonic_ns")
        if any(
            isinstance(value, bool) or not isinstance(value, int) or value <= 0
            for value in (
                commit_unix_ns,
                commit_monotonic_ns,
                successor_unix_ns,
                successor_monotonic_ns,
            )
        ) or not (
            commit_unix_ns < successor_unix_ns
            and commit_monotonic_ns < successor_monotonic_ns
        ):
            raise RuntimeError(
                "superseded response has no later same-turn successor admission"
            )
        already_used = {
            message["item_id"]
            for evidence in self.superseded_by_collaboration_message_evidence.values()
            for message in evidence["collaboration_messages"]
        } | {
            evidence["agent_message_item_id"]
            for evidence in self.suppressed_collaboration_wait_evidence.values()
        }
        candidate_thread_id = candidate.get("thread_id")
        candidate_thread = self.threads.get(str(candidate_thread_id))
        candidate_recipient = (
            "/root"
            if candidate_thread_id == self.root_thread_id
            else candidate_thread.get("agent_path")
            if isinstance(candidate_thread, Mapping)
            else None
        )
        if not isinstance(candidate_recipient, str) or not candidate_recipient:
            raise RuntimeError(
                "superseded response thread lacks a resolved agent route"
            )
        return sorted(
            (
                dict(observation)
                for observation in self.collaboration_message_observations.values()
                if observation["item_id"] not in already_used
                and observation["recipient"] == candidate_recipient
                and commit_unix_ns < observation["observed_at_unix_ns"]
                and observation["observed_at_unix_ns"]
                + APP_SERVER_EVENT_TIME_RESOLUTION_NS
                <= successor_unix_ns
            ),
            key=lambda item: (
                item["observed_at_unix_ns"],
                item["item_id"],
                item["observed_at_monotonic_ns"],
            ),
        )

    def _collaboration_messages_for_superseded_response(
        self, candidate: Mapping[str, Any]
    ) -> dict[str, Any]:
        """Authenticate the nonempty rooted-message batch in one replacement window."""

        messages = self._collaboration_messages_in_superseded_response_window(
            candidate
        )
        if not messages:
            raise RuntimeError(
                "superseded response lacks a nonempty collaboration-message batch"
            )
        evidence = {
            "response_id": candidate.get("response_id"),
            "provider_call_id": candidate.get("call_id"),
            "thread_id": candidate.get("thread_id"),
            "turn_id": candidate.get("turn_id"),
            "successor_response_id": candidate.get("successor_response_id"),
            "successor_call_id": candidate.get("successor_call_id"),
            "collaboration_messages": messages,
        }
        if set(evidence) != set(
            SUPERSEDED_BY_COLLABORATION_MESSAGE_EVIDENCE_KEYS
        ) or any(
            not isinstance(evidence[field], str) or not evidence[field]
            for field in (
                "response_id",
                "provider_call_id",
                "thread_id",
                "turn_id",
                "successor_response_id",
                "successor_call_id",
            )
        ):
            raise RuntimeError("superseded-response evidence is malformed")
        return evidence

    def _reconcile_superseded_responses_for_successor(
        self, *, thread_id: str, turn_id: str, successor_response_id: str
    ) -> None:
        """Bind each message-superseded chain reaching an authenticated delivery."""

        if self.provider_gate is None:
            return
        candidates = (
            self.provider_gate.superseded_by_collaboration_message_candidates(
                thread_id, turn_id
            )
        )
        if not isinstance(candidates, list):
            raise RuntimeError(
                "provider gate returned malformed superseded-response candidates"
            )
        remaining = [
            candidate
            for candidate in candidates
            if isinstance(candidate, Mapping)
            and candidate.get("response_id")
            not in self.superseded_by_collaboration_message_evidence
        ]
        frontier = {successor_response_id}
        # A response immediately preceding an exact suppressed wait does not
        # itself point at the later direct raw response.  Once that wait has
        # been independently authenticated above, its response ID is a safe
        # terminal frontier for partitioning the earlier, tighter MESSAGE
        # window.  Match the complete thread/turn/direct-successor identity;
        # unrelated or malformed evidence remains unusable and therefore
        # fails closed during final reconciliation.
        frontier.update(
            str(evidence["response_id"])
            for evidence in self.suppressed_collaboration_wait_evidence.values()
            if evidence.get("thread_id") == thread_id
            and evidence.get("turn_id") == turn_id
            and evidence.get("successor_response_id") == successor_response_id
            and isinstance(evidence.get("response_id"), str)
            and bool(evidence["response_id"])
        )
        selected: list[Mapping[str, Any]] = []
        while True:
            layer = [
                candidate
                for candidate in remaining
                if candidate.get("successor_response_id") in frontier
            ]
            if not layer:
                break
            layer.sort(
                key=lambda candidate: (
                    int(candidate.get("successor_admitted_monotonic_ns", 0)),
                    str(candidate.get("response_id", "")),
                ),
                reverse=True,
            )
            for candidate in layer:
                remaining.remove(candidate)
                selected.append(candidate)
                response_id = candidate.get("response_id")
                if isinstance(response_id, str) and response_id:
                    frontier.add(response_id)
        for candidate in selected:
            response_id = candidate.get("response_id")
            if not isinstance(response_id, str) or not response_id:
                raise RuntimeError(
                    "provider gate superseded-response candidate lacks identity"
                )
            evidence = self._collaboration_messages_for_superseded_response(
                candidate
            )
            self.provider_gate.crossbind_superseded_by_collaboration_message(
                response_id,
                thread_id,
                turn_id,
                str(candidate["successor_response_id"]),
            )
            self.superseded_by_collaboration_message_evidence[
                response_id
            ] = evidence

    @staticmethod
    def _exact_running_interrupt_output(value: Any) -> bool:
        if not isinstance(value, str):
            return False
        try:
            pairs = json.loads(value, object_pairs_hook=lambda entries: entries)
        except (json.JSONDecodeError, TypeError, ValueError):
            return False
        return pairs == [("previous_status", "running")]

    def _explicit_child_interrupt_evidence(
        self, candidate: Mapping[str, Any]
    ) -> dict[str, Any]:
        """Authenticate one frozen parent-interrupt/child-discard lifecycle."""

        required_strings = (
            "response_id",
            "call_id",
            "thread_id",
            "turn_id",
            "interrupting_response_id",
            "interrupting_call_id",
            "interrupt_parent_thread_id",
            "interrupt_parent_turn_id",
            "interrupt_function_item_id",
            "interrupt_function_call_id",
            "interrupt_function_arguments_sha256",
        )
        if any(
            not isinstance(candidate.get(field), str) or not candidate[field]
            for field in required_strings
        ):
            raise RuntimeError("explicit-child-interrupt candidate lacks identity")
        response_id = str(candidate["response_id"])
        thread_id = str(candidate["thread_id"])
        turn_id = str(candidate["turn_id"])
        interrupting_response_id = str(candidate["interrupting_response_id"])
        interrupt_call_id = str(candidate["interrupt_function_call_id"])
        parent_thread_id = str(candidate["interrupt_parent_thread_id"])
        parent_turn_id = str(candidate["interrupt_parent_turn_id"])

        child = self.threads.get(thread_id)
        parent = self.threads.get(parent_thread_id)
        interrupted_turn = self.terminal_turn_lifecycles.get(
            (thread_id, turn_id)
        )
        raw_call = self.raw_function_calls.get(interrupt_call_id)
        interrupting_response = self.responses.get(interrupting_response_id)
        function_observation = self.raw_item_observations.get(
            str(candidate["interrupt_function_item_id"])
        )
        activity = self.subagent_interrupt_activities.get(interrupt_call_id)
        delayed_output = self.delayed_tool_outputs.get(
            ("function_call_output", interrupt_call_id)
        )
        if not all(
            isinstance(item, Mapping)
            for item in (
                child,
                parent,
                interrupted_turn,
                raw_call,
                interrupting_response,
                function_observation,
                activity,
                delayed_output,
            )
        ):
            raise RuntimeError(
                "explicit child interrupt lacks a complete app-server lifecycle"
            )
        assert isinstance(child, Mapping)
        assert isinstance(interrupted_turn, Mapping)
        assert isinstance(raw_call, Mapping)
        assert isinstance(interrupting_response, Mapping)
        assert isinstance(function_observation, Mapping)
        assert isinstance(activity, Mapping)
        assert isinstance(delayed_output, Mapping)
        agent_path = child.get("agent_path")
        arguments = raw_call.get("arguments")
        try:
            parsed_arguments = (
                json.loads(arguments, object_pairs_hook=lambda entries: entries)
                if isinstance(arguments, str)
                else None
            )
        except (json.JSONDecodeError, TypeError, ValueError):
            parsed_arguments = None
        if (
            child.get("provisional") is not False
            or child.get("spawn_binding_status") != "resolved"
            or child.get("parent_id") != parent_thread_id
            or not isinstance(agent_path, str)
            or not agent_path.startswith("/root/")
            or parsed_arguments != [("target", agent_path)]
            or raw_call.get("call_type") != "function_call"
            or raw_call.get("item_id")
            != candidate["interrupt_function_item_id"]
            or raw_call.get("call_id") != interrupt_call_id
            or raw_call.get("name") != "interrupt_agent"
            or raw_call.get("namespace") != "collaboration"
            or raw_call.get("parent_thread_id") != parent_thread_id
            or raw_call.get("parent_turn_id") != parent_turn_id
            or raw_call.get("parent_response_id") != interrupting_response_id
            or interrupting_response.get("thread_id") != parent_thread_id
            or interrupting_response.get("turn_id") != parent_turn_id
            or candidate.get("interrupting_call_id") is None
            or hashlib.sha256(arguments.encode("utf-8")).hexdigest()
            != candidate["interrupt_function_arguments_sha256"]
        ):
            raise RuntimeError("explicit child interrupt function call is not exact")
        function_item = function_observation.get("item")
        output_observation = self.raw_item_observations.get(
            str(delayed_output.get("item_id"))
        )
        output_item = (
            output_observation.get("item")
            if isinstance(output_observation, Mapping)
            else None
        )
        if (
            function_observation.get("thread_id") != parent_thread_id
            or function_observation.get("turn_id") != parent_turn_id
            or not isinstance(function_item, Mapping)
            or function_item.get("id") != candidate["interrupt_function_item_id"]
            or function_item.get("call_id") != interrupt_call_id
            or function_item.get("name") != "interrupt_agent"
            or function_item.get("namespace") != "collaboration"
            or function_item.get("arguments") != arguments
            or activity.get("kind") != "interrupted"
            or activity.get("activity_id") != interrupt_call_id
            or activity.get("parent_thread_id") != parent_thread_id
            or activity.get("parent_turn_id") != parent_turn_id
            or activity.get("child_thread_id") != thread_id
            or activity.get("agent_path") != agent_path
            or not isinstance(output_observation, Mapping)
            or output_observation.get("thread_id") != parent_thread_id
            or output_observation.get("turn_id") != parent_turn_id
            or not isinstance(output_item, Mapping)
            or output_item.get("type") != "function_call_output"
            or output_item.get("call_id") != interrupt_call_id
            or output_item.get("id") != delayed_output.get("item_id")
            or not self._exact_running_interrupt_output(output_item.get("output"))
            or interrupted_turn.get("thread_id") != thread_id
            or interrupted_turn.get("turn_id") != turn_id
            or interrupted_turn.get("status") != "interrupted"
            or response_id in self.responses
        ):
            raise RuntimeError("explicit child interrupt delivery evidence is not exact")

        observations = {
            "interrupt_function": (
                function_observation.get("event_observed_at_unix_ns"),
                function_observation.get("observed_at_monotonic_ns"),
            ),
            "interrupt_activity": (
                activity.get("observed_at_unix_ns"),
                activity.get("observed_at_monotonic_ns"),
            ),
            "interrupt_output": (
                output_observation.get("event_observed_at_unix_ns"),
                output_observation.get("observed_at_monotonic_ns"),
            ),
            "interrupted_turn": (
                interrupted_turn.get("turn_completed_event_unix_ns"),
                interrupted_turn.get("turn_completed_at_monotonic_ns"),
            ),
        }
        admitted_unix_ns = candidate.get("admitted_unix_ns")
        commit_unix_ns = candidate.get("commit_unix_ns")
        commit_monotonic_ns = candidate.get("commit_monotonic_ns")
        unix_observations = [pair[0] for pair in observations.values()]
        monotonic_observations = [pair[1] for pair in observations.values()]
        if (
            isinstance(admitted_unix_ns, bool)
            or not isinstance(admitted_unix_ns, int)
            or isinstance(commit_unix_ns, bool)
            or not isinstance(commit_unix_ns, int)
            or isinstance(commit_monotonic_ns, bool)
            or not isinstance(commit_monotonic_ns, int)
            or any(
                isinstance(value, bool) or not isinstance(value, int) or value <= 0
                for pair in observations.values()
                for value in pair
            )
            or any(
                unix_ns + APP_SERVER_EVENT_TIME_RESOLUTION_NS > commit_unix_ns
                for unix_ns, monotonic_ns in observations.values()
            )
            or unix_observations != sorted(unix_observations)
            or any(
                earlier >= later
                for earlier, later in zip(
                    monotonic_observations, monotonic_observations[1:]
                )
            )
            or admitted_unix_ns
            >= observations["interrupt_function"][0]
        ):
            raise RuntimeError(
                "explicit child interrupt does not conservatively precede provider commit"
            )
        assert isinstance(output_item, Mapping)
        evidence = {
            "response_id": response_id,
            "provider_call_id": candidate["call_id"],
            "thread_id": thread_id,
            "turn_id": turn_id,
            "interrupting_response_id": interrupting_response_id,
            "interrupting_provider_call_id": candidate["interrupting_call_id"],
            "interrupt_function_item_id": candidate["interrupt_function_item_id"],
            "interrupt_function_call_id": interrupt_call_id,
            "interrupt_function_arguments_sha256": candidate[
                "interrupt_function_arguments_sha256"
            ],
            "interrupt_parent_thread_id": parent_thread_id,
            "interrupt_parent_turn_id": parent_turn_id,
            "interrupted_agent_path": agent_path,
            "interrupt_activity_item_sha256": activity["item_sha256"],
            "interrupt_output_item_id": output_item["id"],
            "interrupt_output_item_sha256": hashlib.sha256(
                json.dumps(
                    output_item,
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=False,
                ).encode("utf-8")
            ).hexdigest(),
            **{
                f"{name}_observed_at_unix_ns": pair[0]
                for name, pair in observations.items()
            },
            **{
                f"{name}_observed_at_monotonic_ns": pair[1]
                for name, pair in observations.items()
            },
        }
        if set(evidence) != set(
            DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_EVIDENCE_KEYS
        ):
            raise RuntimeError("internal explicit-child-interrupt evidence mismatch")
        return evidence

    def reconcile_discarded_after_explicit_child_interrupts(self) -> int:
        """Bind every complete interrupted-child discard visible at the gate."""

        if self.provider_gate is None:
            return 0
        candidates_for = getattr(
            self.provider_gate,
            "discarded_after_explicit_child_interrupt_candidates",
            None,
        )
        if not callable(candidates_for):
            return 0
        reconciled = 0
        for (thread_id, turn_id), lifecycle in sorted(
            self.terminal_turn_lifecycles.items()
        ):
            if lifecycle.get("status") != "interrupted":
                continue
            candidates = candidates_for(thread_id, turn_id)
            if not isinstance(candidates, list):
                raise RuntimeError(
                    "provider gate returned malformed explicit-child-interrupt candidates"
                )
            for candidate in candidates:
                if not isinstance(candidate, Mapping):
                    raise RuntimeError(
                        "provider gate returned malformed explicit-child-interrupt candidate"
                    )
                response_id = candidate.get("response_id")
                if not isinstance(response_id, str) or not response_id:
                    raise RuntimeError(
                        "explicit-child-interrupt candidate lacks response identity"
                    )
                if response_id in self.discarded_after_explicit_child_interrupt_evidence:
                    continue
                evidence = self._explicit_child_interrupt_evidence(candidate)
                self.provider_gate.crossbind_discarded_after_explicit_child_interrupt(
                    response_id,
                    thread_id,
                    turn_id,
                    str(candidate["interrupting_response_id"]),
                )
                self.discarded_after_explicit_child_interrupt_evidence[
                    response_id
                ] = evidence
                reconciled += 1
        if reconciled:
            self.publish()
        return reconciled

    def has_unreconciled_explicit_child_interrupt_lifecycle(self) -> bool:
        bound_call_ids = {
            evidence["interrupt_function_call_id"]
            for evidence in self.discarded_after_explicit_child_interrupt_evidence.values()
        }
        return any(
            call_id not in bound_call_ids
            and ("function_call_output", call_id) in self.delayed_tool_outputs
            and isinstance(self.threads.get(str(activity.get("child_thread_id"))), Mapping)
            and any(
                lifecycle.get("status") == "interrupted"
                for (thread_id, _turn_id), lifecycle in (
                    self.terminal_turn_lifecycles.items()
                )
                if thread_id == str(activity.get("child_thread_id"))
            )
            for call_id, activity in self.subagent_interrupt_activities.items()
        )

    def observe(self, message: Mapping[str, Any]) -> bool:
        """Consume one app-server message and report a new cap crossing."""

        method = message.get("method")
        params = message.get("params")
        if isinstance(method, str) and self._observe_fork_policy_hook(method, params):
            self.publish()
            return False
        if method == "rawResponseItem/completed":
            if not isinstance(params, Mapping):
                raise RuntimeError("Codex app-server emitted malformed raw response item")
            thread_id = params.get("threadId")
            turn_id = params.get("turnId")
            item = params.get("item")
            if (
                not isinstance(thread_id, str)
                or not thread_id
                or not isinstance(turn_id, str)
                or not turn_id
                or not isinstance(item, Mapping)
            ):
                raise RuntimeError("Codex app-server raw response item lacks an identity")
            self._provisional_thread(thread_id)
            # JSON round-tripping severs references to the mutable protocol object.
            copied = json.loads(json.dumps(item, ensure_ascii=False))
            received_at_unix_ns = time.time_ns()
            observed_at_monotonic_ns = time.monotonic_ns()
            emitted_at_ms = message.get("emittedAtMs")
            event_observed_at_unix_ns = (
                emitted_at_ms * APP_SERVER_EVENT_TIME_RESOLUTION_NS
                if isinstance(emitted_at_ms, int)
                and not isinstance(emitted_at_ms, bool)
                and emitted_at_ms > 0
                else None
            )
            if (
                event_observed_at_unix_ns is not None
                and event_observed_at_unix_ns > received_at_unix_ns
            ):
                raise RuntimeError(
                    "Codex raw response item event time follows local receipt"
                )
            observed_at_unix_ns = received_at_unix_ns
            if copied.get("type") == "agent_message":
                content = copied.get("content")
                first = (
                    content[0]
                    if isinstance(content, list) and content
                    else None
                )
                text = (
                    first.get("text")
                    if isinstance(first, Mapping)
                    else None
                )
                if isinstance(text, str) and text.startswith(
                    ("Message Type: MESSAGE\n", "Message Type: FINAL_ANSWER\n")
                ):
                    emitted_at_ms = message.get("emittedAtMs")
                    if (
                        not isinstance(emitted_at_ms, int)
                        or isinstance(emitted_at_ms, bool)
                        or emitted_at_ms <= 0
                    ):
                        raise RuntimeError(
                            "Codex collaboration message lacks a valid app-server event time"
                        )
                    observed_at_unix_ns = emitted_at_ms * 1_000_000
                    if observed_at_unix_ns > received_at_unix_ns:
                        raise RuntimeError(
                            "Codex collaboration message event time follows local receipt"
                        )
            raw_item_id = copied.get("id")
            if isinstance(raw_item_id, str) and raw_item_id:
                canonical_observation = {
                    "thread_id": thread_id,
                    "turn_id": turn_id,
                    "item": copied,
                    "observed_at_unix_ns": received_at_unix_ns,
                    "observed_at_monotonic_ns": observed_at_monotonic_ns,
                    "event_observed_at_unix_ns": event_observed_at_unix_ns,
                }
                prior_observation = self.raw_item_observations.get(raw_item_id)
                if prior_observation is not None:
                    comparable = {
                        key: prior_observation.get(key)
                        for key in ("thread_id", "turn_id", "item")
                    }
                    if comparable != {
                        key: canonical_observation[key]
                        for key in ("thread_id", "turn_id", "item")
                    }:
                        raise RuntimeError(
                            "Codex app-server reused a raw response item id inconsistently"
                        )
                else:
                    self.raw_item_observations[raw_item_id] = canonical_observation
            self._capture_final_answer_agent_message(
                thread_id=thread_id,
                turn_id=turn_id,
                item=copied,
                observed_at_unix_ns=observed_at_unix_ns,
                observed_at_monotonic_ns=observed_at_monotonic_ns,
            )
            self._capture_collaboration_message(
                thread_id=thread_id,
                turn_id=turn_id,
                item=copied,
                observed_at_unix_ns=observed_at_unix_ns,
                observed_at_monotonic_ns=observed_at_monotonic_ns,
            )
            if copied.get("type") in (
                "custom_tool_call_output",
                "function_call_output",
            ):
                self._consume_delayed_tool_output(
                    thread_id=thread_id,
                    turn_id=turn_id,
                    item=copied,
                    observed_at_unix_ns=observed_at_unix_ns,
                    observed_at_monotonic_ns=observed_at_monotonic_ns,
                )
                self.reconcile_discarded_after_explicit_child_interrupts()
                return False
            self.raw_items_pending.setdefault((thread_id, turn_id), []).append(copied)
            return False
        if method == ULTRA_USAGE_NOTIFICATION:
            crossing = self._observe_raw_response(message)
            self.publish()
            return crossing
        if method in ("item/started", "item/completed") and isinstance(params, Mapping):
            item = params.get("item")
            if (
                method == "item/started"
                and isinstance(item, Mapping)
                and item.get("type") == "dynamicToolCall"
            ):
                thread_id = params.get("threadId")
                turn_id = params.get("turnId")
                call_id = item.get("id")
                canonical_start = {
                    "thread_id": thread_id,
                    "turn_id": turn_id,
                    "call_id": call_id,
                    "namespace": item.get("namespace"),
                    "tool": item.get("tool"),
                    "arguments": item.get("arguments"),
                    "status": item.get("status"),
                    "observed_at_unix_ns": time.time_ns(),
                    "observed_at_monotonic_ns": time.monotonic_ns(),
                }
                if (
                    not isinstance(thread_id, str)
                    or not thread_id
                    or not isinstance(turn_id, str)
                    or not turn_id
                    or not isinstance(call_id, str)
                    or not call_id
                ):
                    raise RuntimeError(
                        "Codex app-server emitted malformed dynamic tool start"
                    )
                prior_start = self.dynamic_tool_starts.get(call_id)
                if prior_start is not None:
                    raise RuntimeError(
                        "Codex app-server emitted a duplicate dynamic tool item start"
                    )
                else:
                    self.dynamic_tool_starts[call_id] = canonical_start
                return False
            if (
                isinstance(item, Mapping)
                and item.get("type") == "collabAgentToolCall"
                and item.get("tool") == "spawnAgent"
            ):
                self._observe_collab_spawn(method, params, item)
                self.publish()
                return False
            if isinstance(item, Mapping) and item.get("type") == "subAgentActivity":
                parent = params.get("threadId")
                child = item.get("agentThreadId")
                activity_id = item.get("id")
                turn_id = params.get("turnId")
                kind = item.get("kind")
                agent_path = item.get("agentPath")
                if kind == "interacted":
                    # A completed collaboration send emits this ordinary
                    # lifecycle item.  It neither creates nor interrupts a
                    # child, so validate its identity and otherwise ignore it.
                    if (
                        method != "item/completed"
                        or not isinstance(parent, str)
                        or not parent
                        or not isinstance(child, str)
                        or not child
                        or not isinstance(activity_id, str)
                        or not activity_id
                        or not isinstance(turn_id, str)
                        or not turn_id
                        or not isinstance(agent_path, str)
                        or not agent_path
                    ):
                        raise RuntimeError(
                            "Codex app-server emitted malformed subagent activity"
                        )
                    return False
                if (
                    not isinstance(parent, str)
                    or not parent
                    or not isinstance(child, str)
                    or not child
                    or not isinstance(activity_id, str)
                    or not activity_id
                    or not isinstance(turn_id, str)
                    or not turn_id
                    or kind not in ("started", "interrupted")
                ):
                    raise RuntimeError("Codex app-server emitted malformed subagent activity")
                received_at_unix_ns = time.time_ns()
                observed_at_monotonic_ns = time.monotonic_ns()
                emitted_at_ms = message.get("emittedAtMs")
                event_observed_at_unix_ns = (
                    emitted_at_ms * APP_SERVER_EVENT_TIME_RESOLUTION_NS
                    if isinstance(emitted_at_ms, int)
                    and not isinstance(emitted_at_ms, bool)
                    and emitted_at_ms > 0
                    else None
                )
                if (
                    event_observed_at_unix_ns is not None
                    and event_observed_at_unix_ns > received_at_unix_ns
                ):
                    raise RuntimeError(
                        "Codex subagent activity event time follows local receipt"
                    )
                canonical_activity = {
                    "activity_id": activity_id,
                    "parent_thread_id": parent,
                    "parent_turn_id": turn_id,
                    "child_thread_id": child,
                    "agent_path": agent_path,
                }
                if kind == "interrupted":
                    canonical_activity.update(
                        {
                            "kind": kind,
                            "item_sha256": hashlib.sha256(
                                json.dumps(
                                    item,
                                    sort_keys=True,
                                    separators=(",", ":"),
                                    ensure_ascii=False,
                                ).encode("utf-8")
                            ).hexdigest(),
                            "observed_at_unix_ns": event_observed_at_unix_ns,
                            "observed_at_monotonic_ns": observed_at_monotonic_ns,
                        }
                    )
                destination = (
                    self.subagent_activities
                    if kind == "started"
                    else self.subagent_interrupt_activities
                )
                prior_activity = destination.get(activity_id)
                if prior_activity is not None and prior_activity != canonical_activity:
                    raise RuntimeError("Codex subagent activity id was reused inconsistently")
                destination[activity_id] = canonical_activity
                if kind == "started":
                    self._link_child(parent, child, item.get("agentPath"))
                    self._resolve_spawn_links()
                else:
                    self.reconcile_discarded_after_explicit_child_interrupts()
                self.publish()
            return False
        tracked = {
            "turn/started",
            "turn/completed",
            "thread/status/changed",
            "thread/tokenUsage/updated",
        }
        if method not in tracked:
            return False
        if not isinstance(params, Mapping):
            raise RuntimeError(f"Codex app-server emitted malformed {method}")
        thread_id = params.get("threadId")
        if not isinstance(thread_id, str) or not thread_id:
            raise RuntimeError(f"Codex app-server emitted {method} without a thread id")
        thread = self._provisional_thread(thread_id)
        if method == "turn/started":
            turn = params.get("turn")
            turn_id = turn.get("id") if isinstance(turn, Mapping) else None
            if not isinstance(turn_id, str) or not turn_id:
                raise RuntimeError("Codex app-server emitted malformed turn/started")
            active = thread.get("active_turn_id")
            if active not in (None, turn_id):
                raise RuntimeError("Codex thread started overlapping turns")
            thread["active_turn_id"] = turn_id
            thread["turn_seen"] = True
            thread["turn_status"] = "inProgress"
            if thread_id == self.root_thread_id:
                if self.root_turn_id in (None, turn_id):
                    self.root_turn_id = turn_id
                    self.root_prompt_turn_status = "inProgress"
                elif (
                    self.compaction_canary_authorized
                    and self.compaction_turn_id in (None, turn_id)
                ):
                    self.compaction_turn_id = turn_id
                    self.compaction_turn_status = "inProgress"
                else:
                    raise RuntimeError("Codex root emitted inconsistent turn ids")
        elif method == "turn/completed":
            turn = params.get("turn")
            turn_id = turn.get("id") if isinstance(turn, Mapping) else None
            status = turn.get("status") if isinstance(turn, Mapping) else None
            if not isinstance(turn_id, str) or not turn_id:
                raise RuntimeError("Codex app-server emitted malformed turn/completed")
            if status not in ("completed", "failed", "interrupted"):
                raise RuntimeError("Codex app-server emitted invalid terminal turn status")
            active = thread.get("active_turn_id")
            if active not in (None, turn_id):
                raise RuntimeError("Codex thread completed an unexpected turn")
            completed_at_unix_ns = time.time_ns()
            completed_at_monotonic_ns = time.monotonic_ns()
            emitted_at_ms = message.get("emittedAtMs")
            completed_event_unix_ns = (
                emitted_at_ms * APP_SERVER_EVENT_TIME_RESOLUTION_NS
                if isinstance(emitted_at_ms, int)
                and not isinstance(emitted_at_ms, bool)
                and emitted_at_ms > 0
                else None
            )
            if (
                completed_event_unix_ns is not None
                and completed_event_unix_ns > completed_at_unix_ns
            ):
                raise RuntimeError(
                    "Codex turn completion event time follows local receipt"
                )
            lifecycle_key = (thread_id, turn_id)
            if lifecycle_key in self.terminal_turn_lifecycles:
                raise RuntimeError(
                    "Codex app-server emitted duplicate terminal turn lifecycle"
                )
            self.terminal_turn_lifecycles[lifecycle_key] = {
                "thread_id": thread_id,
                "turn_id": turn_id,
                "status": status,
                "turn_completed_at_unix_ns": completed_at_unix_ns,
                "turn_completed_at_monotonic_ns": completed_at_monotonic_ns,
                "turn_completed_event_unix_ns": completed_event_unix_ns,
            }
            thread["active_turn_id"] = None
            thread["turn_status"] = status
            thread["terminal_turn_id"] = turn_id
            thread["turn_completed_at_unix_ns"] = completed_at_unix_ns
            thread["turn_completed_at_monotonic_ns"] = completed_at_monotonic_ns
            thread["turn_completed_event_unix_ns"] = completed_event_unix_ns
            if thread_id == self.root_thread_id:
                if self.root_turn_id in (None, turn_id):
                    self.root_turn_id = turn_id
                    self.root_prompt_turn_status = status
                elif (
                    self.compaction_canary_authorized
                    and self.compaction_turn_id == turn_id
                ):
                    self.compaction_turn_status = status
                else:
                    raise RuntimeError("Codex root completed another turn")
            self.reconcile_discarded_after_explicit_child_interrupts()
        elif method == "thread/status/changed":
            status = params.get("status")
            status_type = status.get("type") if isinstance(status, Mapping) else None
            if not isinstance(status_type, str) or not status_type:
                raise RuntimeError("Codex app-server emitted malformed thread status")
            thread["thread_status"] = status_type
        else:
            self._observe_cumulative(message)
        self.publish()
        return False

    def active_turns(self) -> dict[str, str]:
        return {
            thread_id: str(thread["active_turn_id"])
            for thread_id, thread in self.threads.items()
            if isinstance(thread.get("active_turn_id"), str)
        }

    def unresolved_thread_ids(self) -> list[str]:
        return sorted(
            thread_id
            for thread_id, thread in self.threads.items()
            if thread.get("provisional") is True
        )

    def root_terminal_status(self) -> str | None:
        return self.root_prompt_turn_status

    def authorize_provider_gate_compaction_canary(self) -> None:
        """Authorize exactly one adapter-originated root compaction turn."""

        if (
            self.provider_gate is None
            or self.compaction_canary_authorized
            or self.compaction_turn_id is not None
            or self.compaction_response_id is not None
            or self.first_crossing is not None
            or self.root_turn_id is None
            or self.root_terminal_status() != "completed"
            or not self.quiescent()
        ):
            raise RuntimeError(
                "provider-token gate compaction canary was authorized out of order"
            )
        self.compaction_canary_authorized = True

    def quiescent(self) -> bool:
        return (
            self.root_terminal_status() in ("completed", "failed", "interrupted")
            and not self.active_turns()
            and not self.unresolved_thread_ids()
            and not self.interrupt_request_ids
            and all(
                thread_id == self.root_thread_id or thread.get("turn_seen") is True
                for thread_id, thread in self.threads.items()
            )
        )

    def mark_interrupt_request(self, request_id: int) -> None:
        self.interrupt_requested = True
        self.interrupt_request_ids.add(request_id)
        self.publish()

    def observe_interrupt_response(self, message: Mapping[str, Any]) -> bool:
        request_id = message.get("id")
        if request_id not in self.interrupt_request_ids or "method" in message:
            return False
        if "error" in message:
            raise RuntimeError("Codex app-server rejected a turn interrupt")
        self.interrupt_request_ids.remove(int(request_id))
        self.publish()
        return True

    def _spawn_accounting_state(self) -> dict[str, Any]:
        raw_ids = set(self.raw_spawn_calls)
        activity_ids = set(self.subagent_activities)
        collab_ids = set(self.collab_spawn_calls)
        call_evidence = (
            [
                self._fork_policy_call_evidence(call_id, self.raw_spawn_calls[call_id])
                for call_id in sorted(raw_ids)
            ]
            if self.fork_policy_static is not None
            else []
        )
        hook_observed_ids = {
            str(item["call_id"])
            for item in call_evidence
            if item["hook_started_observed"] or item["hook_completed_observed"]
        }
        hook_allowed_ids = {
            str(item["call_id"])
            for item in call_evidence
            if item["decision"] == ULTRA_FORK_POLICY_ALLOW_DECISION
            and item["resolution_status"]
            not in (
                ULTRA_FORK_POLICY_AWAITING_HOOK_STATUS,
                ULTRA_FORK_POLICY_INVALID_RESOLUTION_STATUS,
            )
        }
        hook_blocked_ids = {
            str(item["call_id"])
            for item in call_evidence
            if item["decision"] == ULTRA_FORK_POLICY_BLOCK_DECISION
            and item["resolution_status"] == ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS
        }
        all_hook_ids = set(self.fork_hook_started) | set(self.fork_hook_completed)
        hook_invalid_ids = set(self.fork_hook_invalid_call_ids) | {
            str(item["call_id"])
            for item in call_evidence
            if item["resolution_status"] == ULTRA_FORK_POLICY_INVALID_RESOLUTION_STATUS
        }
        hook_invalid_ids |= all_hook_ids - raw_ids
        fork_policy_complete = bool(
            self.fork_policy_static is None
            or (
                not self.fork_hook_invalid_reasons
                and not hook_invalid_ids
                and all_hook_ids <= raw_ids
                and raw_ids == hook_allowed_ids | hook_blocked_ids
                and all(
                    item["hook_started_count"] == 1
                    and item["hook_completed_count"] == 1
                    for item in call_evidence
                )
            )
        )
        resolved_ids = {
            call_id
            for call_id, record in self.raw_spawn_calls.items()
            if record.get("resolution_status") == "resolved_child"
        }
        failed_ids = {
            call_id
            for call_id, record in self.raw_spawn_calls.items()
            if record.get("resolution_status") == "failed_without_child"
        }
        blocked_ids = {
            call_id
            for call_id, record in self.raw_spawn_calls.items()
            if record.get("resolution_status")
            == ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS
        }
        unsupported_ids = {
            call_id
            for call_id, record in self.raw_spawn_calls.items()
            if (
                record.get("resolution_status")
                in {
                    "invalid_arguments",
                    "invalid_fork_turns",
                    "unsupported_positive_turn_suffix",
                    "unsupported_namespace",
                    ULTRA_FORK_POLICY_INVALID_RESOLUTION_STATUS,
                }
                or (
                    record.get("fork_semantics")
                    in {
                        "invalid_arguments",
                        "invalid_fork_turns",
                        "unsupported_positive_turn_suffix",
                    }
                    and call_id not in blocked_ids
                )
                or not record.get("namespace_supported")
            )
        }
        terminal_ids = resolved_ids | failed_ids | blocked_ids
        unresolved_ids = (raw_ids | activity_ids | collab_ids) - terminal_ids
        child_threads = {
            thread_id
            for thread_id in self.threads
            if thread_id != self.root_thread_id
        }
        resolved_child_threads = {
            thread_id
            for thread_id, thread in self.threads.items()
            if thread_id != self.root_thread_id
            and thread.get("spawn_binding_status") == "resolved"
            and thread.get("spawn_call_id") in resolved_ids
        }
        linkage_complete = (
            raw_ids == terminal_ids
            and activity_ids == resolved_ids
            and collab_ids <= (resolved_ids | failed_ids)
            and not unsupported_ids
            and not unresolved_ids
            and child_threads == resolved_child_threads
            and len(resolved_ids) == len(resolved_child_threads)
            and fork_policy_complete
        )
        fork_policy = None
        if self.fork_policy_static is not None:
            fork_policy = {
                **self.fork_policy_static,
                "call_evidence": call_evidence,
                "complete": fork_policy_complete,
            }
        return {
            "spawn_binding_source": (
                "raw_function_call.call_id=subAgentActivity.id"
            ),
            "raw_spawn_call_ids": sorted(raw_ids),
            "activity_spawn_call_ids": sorted(activity_ids),
            "collab_spawn_call_ids": sorted(collab_ids),
            "resolved_spawn_call_ids": sorted(resolved_ids),
            "failed_spawn_call_ids": sorted(failed_ids | blocked_ids),
            "policy_blocked_spawn_call_ids": sorted(blocked_ids),
            "unresolved_spawn_call_ids": sorted(unresolved_ids),
            "unsupported_spawn_call_ids": sorted(unsupported_ids),
            "inference_child_thread_ids": sorted(child_threads),
            "hook_observed_spawn_call_ids": sorted(hook_observed_ids),
            "hook_allowed_spawn_call_ids": sorted(hook_allowed_ids),
            "hook_blocked_spawn_call_ids": sorted(hook_blocked_ids),
            "hook_invalid_spawn_call_ids": sorted(hook_invalid_ids),
            "fork_policy_complete": fork_policy_complete,
            "fork_policy": fork_policy,
            "spawn_linkage_complete": linkage_complete,
        }

    def _thread_projection(
        self,
        thread_id: str,
        *,
        exempt_response_id: str | None,
        allow_absent_zero: bool,
    ) -> dict[str, Any]:
        thread = self.threads[thread_id]
        baseline = thread.get("expected_cumulative_baseline")
        if not isinstance(baseline, Mapping):
            return {
                "expected_cumulative_projection": None,
                "full_cumulative_projection": None,
                "cumulative_projection_exempt_response_id": exempt_response_id,
                "cumulative_projection_exempt_response_usage": None,
                "observed_cumulative_baseline": None,
                "cumulative_baseline_matches_expected": False,
                "cumulative_projection_match": False,
                "cumulative_projection_status": "unresolved_expected_baseline",
            }
        full_projection = self._usage_add(baseline, thread["raw_sum"])
        projected_raw_sum = dict(thread["raw_sum"])
        exempt_usage: dict[str, int] | None = None
        if exempt_response_id is not None:
            response = self.responses.get(exempt_response_id)
            if response is None or response.get("thread_id") != thread_id:
                return {
                    "expected_cumulative_projection": None,
                    "full_cumulative_projection": full_projection,
                    "cumulative_projection_exempt_response_id": exempt_response_id,
                    "cumulative_projection_exempt_response_usage": None,
                    "observed_cumulative_baseline": None,
                    "cumulative_baseline_matches_expected": False,
                    "cumulative_projection_match": False,
                    "cumulative_projection_status": "invalid_exempt_response",
                }
            exempt_usage = dict(response["usage"])
            projected_raw_sum = self._usage_subtract(
                projected_raw_sum, exempt_usage
            )
        expected_projection = self._usage_add(baseline, projected_raw_sum)
        observed = thread.get("last_cumulative")
        observed_baseline: dict[str, int] | None = None
        baseline_matches = False
        projection_matches = False
        status = "missing_cumulative"
        if isinstance(observed, Mapping):
            comparison_raw_sum = projected_raw_sum
            if exempt_usage is not None and observed == full_projection:
                comparison_raw_sum = thread["raw_sum"]
                status = "matched_full_including_exempt_response"
            elif observed == expected_projection:
                status = (
                    "matched_pre_exempt_response"
                    if exempt_usage is not None
                    else "matched_full_projection"
                )
            else:
                status = "cumulative_projection_mismatch"
            differences = {
                field: int(observed[field]) - int(comparison_raw_sum[field])
                for field in self._SUM_FIELDS
            }
            if self._valid_usage_breakdown(differences):
                observed_baseline = differences
                baseline_matches = observed_baseline == dict(baseline)
            projection_matches = (
                observed in (expected_projection, full_projection)
                if exempt_usage is not None
                else observed == expected_projection
            ) and baseline_matches
        elif allow_absent_zero and not any(expected_projection.values()):
            # The sole exception is the blocked root submit response: before it,
            # a genuinely zero-usage root has no cumulative notification to emit.
            baseline_matches = dict(baseline) == {
                field: 0 for field in self._SUM_FIELDS
            }
            projection_matches = baseline_matches
            status = "zero_pre_response_without_cumulative_notification"
        return {
            "expected_cumulative_projection": expected_projection,
            "full_cumulative_projection": full_projection,
            "cumulative_projection_exempt_response_id": exempt_response_id,
            "cumulative_projection_exempt_response_usage": exempt_usage,
            "observed_cumulative_baseline": observed_baseline,
            "cumulative_baseline_matches_expected": baseline_matches,
            "cumulative_projection_match": projection_matches,
            "cumulative_projection_status": status,
        }

    def _accounting_state(
        self,
        *,
        boundary_response_id: str | None = None,
        pre_submission: bool = False,
    ) -> dict[str, Any]:
        spawn = self._spawn_accounting_state()
        projections: dict[str, dict[str, Any]] = {}
        thread_complete: dict[str, bool] = {}
        for thread_id, thread in self.threads.items():
            root = thread_id == self.root_thread_id
            projection = self._thread_projection(
                thread_id,
                exempt_response_id=(boundary_response_id if root else None),
                allow_absent_zero=root
                and (pre_submission or boundary_response_id is not None),
            )
            projections[thread_id] = projection
            binding_complete = (
                thread.get("spawn_binding_status") == "root_zero"
                if root
                else thread.get("spawn_binding_status") == "resolved"
            )
            thread_complete[thread_id] = bool(
                binding_complete and projection["cumulative_projection_match"]
            )
        descendants_complete = all(
            complete
            for thread_id, complete in thread_complete.items()
            if thread_id != self.root_thread_id
        )
        cumulative_complete = all(
            projection["cumulative_projection_match"]
            for projection in projections.values()
        )
        accounting_complete = bool(
            spawn["spawn_linkage_complete"]
            and cumulative_complete
            and all(thread_complete.values())
        )
        return {
            **spawn,
            "projections": projections,
            "thread_accounting_complete": thread_complete,
            "descendant_accounting_complete": descendants_complete,
            "cumulative_projection_complete": cumulative_complete,
            "accounting_complete": accounting_complete,
        }

    def attach_provider_gate_final(
        self,
        record: Mapping[str, Any],
        terminal_snapshot: Mapping[str, Any],
        *,
        exact_for_usage: bool,
        provider_usage_reconciliation: Mapping[str, Any] | None = None,
    ) -> None:
        """Bind one independently validated sealed gate artifact to this ledger."""

        if self.provider_gate is None or self.provider_gate_artifact_path is None:
            raise RuntimeError("cannot attach a provider gate to an ungated ledger")
        if self.provider_gate_final is not None:
            raise RuntimeError("provider-gate final artifact was attached twice")
        copied_record = json.loads(json.dumps(record, ensure_ascii=False))
        copied_snapshot = json.loads(json.dumps(terminal_snapshot, ensure_ascii=False))
        if not isinstance(copied_record, dict) or not isinstance(copied_snapshot, dict):
            raise RuntimeError("provider-gate final evidence is malformed")
        self.provider_gate_final = copied_record
        self.provider_gate_terminal_snapshot = copied_snapshot
        self.provider_gate_exact_for_usage = bool(exact_for_usage)
        if provider_usage_reconciliation is not None:
            copied_reconciliation = json.loads(
                json.dumps(provider_usage_reconciliation, ensure_ascii=False)
            )
            if (
                not isinstance(copied_reconciliation, dict)
                or set(copied_reconciliation)
                != set(PROVIDER_USAGE_RECONCILIATION_KEYS)
            ):
                raise RuntimeError("provider usage reconciliation is malformed")
            live_reconciliation = self.live_provider_usage_reconciliation()
            if live_reconciliation != copied_reconciliation:
                raise RuntimeError(
                    "sealed provider usage disagrees with the live reconciliation"
                )
            self.provider_usage_reconciliation = copied_reconciliation
        elif exact_for_usage:
            raise RuntimeError("exact provider usage lacks reconciliation")

    def attach_adapter_teardown(self, teardown: Mapping[str, Any]) -> None:
        """Record process-group teardown after the token endpoint is frozen."""

        if self.adapter_teardown is not None:
            raise RuntimeError("adapter teardown was attached twice")
        copied = json.loads(json.dumps(teardown, ensure_ascii=False))
        if not self._authenticated_adapter_teardown(copied):
            raise RuntimeError("adapter teardown evidence is malformed")
        self.adapter_teardown = copied

    @staticmethod
    def _authenticated_adapter_teardown(
        teardown: Any,
        *,
        required_immediate: bool | None = None,
    ) -> bool:
        """Validate the complete local process-group teardown contract."""

        if (
            not isinstance(teardown, Mapping)
            or set(teardown) != ULTRA_ADAPTER_TEARDOWN_KEYS
            or teardown.get("process_group_isolated") is not True
            or teardown.get("stdin_closed") is not True
            or teardown.get("completed") is not True
            or type(teardown.get("immediate")) is not bool
            or (
                required_immediate is not None
                and teardown.get("immediate") is not required_immediate
            )
            or type(teardown.get("returncode")) is not int
            or teardown.get("signal") not in (None, "SIGTERM", "SIGKILL")
        ):
            return False
        for clock in ("unix", "monotonic"):
            started = teardown.get(f"started_at_{clock}_ns")
            completed = teardown.get(f"completed_at_{clock}_ns")
            if (
                type(started) is not int
                or started <= 0
                or type(completed) is not int
                or completed < started
            ):
                return False
        return True

    def _provider_gate_call(self, response_id: str) -> dict[str, Any] | None:
        record = self.provider_gate_final
        calls = record.get("calls") if isinstance(record, Mapping) else None
        if not isinstance(calls, list):
            return None
        matches = [
            call
            for call in calls
            if isinstance(call, Mapping) and call.get("response_id") == response_id
        ]
        if len(matches) != 1:
            return None
        copied = json.loads(json.dumps(matches[0], ensure_ascii=False))
        return copied if isinstance(copied, dict) else None

    def _response_ledger(self) -> list[dict[str, Any]]:
        """Return ordered raw-event records, including their sealed gate edge."""

        ordered = sorted(
            self.responses.items(), key=lambda item: int(item[1]["sequence"])
        )
        return [
            {
                "response_id": response_id,
                "thread_id": response["thread_id"],
                "turn_id": response["turn_id"],
                "raw_response_notification_sequence": response["sequence"],
                "raw_response_observed_at_unix_ns": response["observed_at_unix_ns"],
                "raw_response_observed_at_monotonic_ns": response[
                    "observed_at_monotonic_ns"
                ],
                "usage": dict(response["usage"]),
                "provider_gate_call": self._provider_gate_call(response_id),
            }
            for response_id, response in ordered
        ]

    def ordered_response_ids(self) -> list[str]:
        """Return response identities in authenticated notification order."""

        return [
            response_id
            for response_id, _response in sorted(
                self.responses.items(), key=lambda item: int(item[1]["sequence"])
            )
        ]

    def provider_boundary_usage(self) -> dict[str, Any]:
        """Return the gate-authoritative completed usage at a proof boundary."""

        if self.provider_gate is None:
            return {
                **{field: self.aggregate[field] for field in self._SUM_FIELDS},
                "response_count": len(self.responses),
                "thread_count": len(self.threads),
                "notification_sequence": self.notification_sequence,
                "response_ids": self.ordered_response_ids(),
                "appserver_response_count": len(self.responses),
                "appserver_response_ids": self.ordered_response_ids(),
            }
        self.reconcile_discarded_after_explicit_child_interrupts()
        reconciliation = self.live_provider_usage_reconciliation()
        if reconciliation is None:
            raise RuntimeError("provider boundary usage is not exactly reconciled")
        provider_usage = reconciliation["provider_usage"]
        provider_ids = reconciliation["provider_response_ids"]
        appserver_ids = reconciliation["appserver_response_ids"]
        if provider_usage["total_tokens"] >= self.token_limit:
            raise RuntimeError("provider boundary usage reached the token limit")
        return {
            **provider_usage,
            "response_count": len(provider_ids),
            "thread_count": len(self.threads),
            "notification_sequence": self.notification_sequence,
            "response_ids": list(provider_ids),
            "appserver_response_count": len(appserver_ids),
            "appserver_response_ids": list(appserver_ids),
        }

    def live_provider_usage_reconciliation(self) -> dict[str, Any] | None:
        """Project the gate's safe metadata view without inventing raw events."""

        if self.provider_gate is None:
            return None
        snapshot = self.provider_gate.completed_response_usage_snapshot()
        if not isinstance(snapshot, list):
            raise RuntimeError("provider gate completed-usage snapshot is malformed")
        provider_ids: list[str] = []
        provider_usage = {field: 0 for field in self._SUM_FIELDS}
        direct_ids: list[str] = []
        suppressed_ids: list[str] = []
        superseded_ids: list[str] = []
        discarded_ids: list[str] = []
        usage_by_response: dict[str, dict[str, int]] = {}
        for index, item in enumerate(snapshot):
            if not isinstance(item, Mapping):
                raise RuntimeError("provider gate completed-usage item is malformed")
            response_id = item.get("response_id")
            usage = item.get("normalized_usage")
            if (
                not isinstance(response_id, str)
                or not response_id
                or response_id in provider_ids
                or not isinstance(usage, Mapping)
                or set(usage) != set(self._SUM_FIELDS)
                or any(
                    isinstance(usage[field], bool)
                    or not isinstance(usage[field], int)
                    or usage[field] < 0
                    for field in self._SUM_FIELDS
                )
            ):
                raise RuntimeError(
                    f"provider gate completed-usage item {index} is invalid"
                )
            provider_ids.append(response_id)
            usage_by_response[response_id] = {
                field: int(usage[field]) for field in self._SUM_FIELDS
            }
            for field in self._SUM_FIELDS:
                provider_usage[field] += int(usage[field])
            delivery_kind = item.get("appserver_delivery_kind")
            if delivery_kind == "direct_raw_response":
                direct_ids.append(response_id)
            elif delivery_kind == "suppressed_collaboration_wait":
                suppressed_ids.append(response_id)
            elif delivery_kind == "superseded_by_collaboration_message":
                superseded_ids.append(response_id)
            elif delivery_kind == "discarded_after_explicit_child_interrupt":
                discarded_ids.append(response_id)
            else:
                return None
        appserver_ids = self.ordered_response_ids()
        if (
            set(direct_ids) != set(appserver_ids)
            or set(suppressed_ids)
            != set(self.suppressed_collaboration_wait_evidence)
            or set(superseded_ids)
            != set(self.superseded_by_collaboration_message_evidence)
            or set(discarded_ids)
            != set(self.discarded_after_explicit_child_interrupt_evidence)
        ):
            return None
        suppressed_usage = {
            field: sum(usage_by_response[item][field] for item in suppressed_ids)
            for field in self._SUM_FIELDS
        }
        superseded_usage = {
            field: sum(usage_by_response[item][field] for item in superseded_ids)
            for field in self._SUM_FIELDS
        }
        discarded_usage = {
            field: sum(usage_by_response[item][field] for item in discarded_ids)
            for field in self._SUM_FIELDS
        }
        if any(
            provider_usage[field]
            != self.aggregate[field]
            + suppressed_usage[field]
            + superseded_usage[field]
            + discarded_usage[field]
            for field in self._SUM_FIELDS
        ):
            return None
        reconciliation = {
            "schema_version": PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION,
            "provider_response_count": len(provider_ids),
            "appserver_response_count": len(appserver_ids),
            "suppressed_collaboration_wait_response_count": len(suppressed_ids),
            "provider_usage": provider_usage,
            "appserver_usage": dict(self.aggregate),
            "suppressed_collaboration_wait_usage": suppressed_usage,
            "provider_response_ids": provider_ids,
            "appserver_response_ids": appserver_ids,
            "suppressed_collaboration_wait_response_ids": suppressed_ids,
            "suppressed_collaboration_wait_evidence": [
                dict(self.suppressed_collaboration_wait_evidence[response_id])
                for response_id in suppressed_ids
            ],
            "superseded_by_collaboration_message_response_count": len(
                superseded_ids
            ),
            "superseded_by_collaboration_message_usage": superseded_usage,
            "superseded_by_collaboration_message_response_ids": superseded_ids,
            "superseded_by_collaboration_message_evidence": [
                dict(
                    self.superseded_by_collaboration_message_evidence[
                        response_id
                    ]
                )
                for response_id in superseded_ids
            ],
            "discarded_after_explicit_child_interrupt_response_count": len(
                discarded_ids
            ),
            "discarded_after_explicit_child_interrupt_usage": discarded_usage,
            "discarded_after_explicit_child_interrupt_response_ids": discarded_ids,
            "discarded_after_explicit_child_interrupt_evidence": [
                dict(
                    self.discarded_after_explicit_child_interrupt_evidence[
                        response_id
                    ]
                )
                for response_id in discarded_ids
            ],
        }
        return (
            reconciliation
            if set(reconciliation) == set(PROVIDER_USAGE_RECONCILIATION_KEYS)
            else None
        )

    def _measurement_exact(self, drain_complete: bool) -> bool:
        boundary_response_id: str | None = None
        if self.submission_boundary is not None:
            candidate = self.submission_boundary.get("response_id")
            boundary_response_id = candidate if isinstance(candidate, str) else None
            accounting = self._accounting_state(
                boundary_response_id=boundary_response_id
            )
            return bool(
                self.submission_boundary.get("status") == "accepted"
                and accounting["accounting_complete"]
                and not self.invalid_reasons
                and not self.unresolved_thread_ids()
                and not self.interrupt_requested
                and not self.interrupt_request_ids
                and self.first_crossing is None
                and (
                    self.provider_gate is None
                    or self.provider_gate_exact_for_usage
                )
            )
        if self.first_crossing is not None and self.provider_gate is not None:
            terminal = (
                _provider_gate_state_view(self.provider_gate_terminal_snapshot)
                if isinstance(self.provider_gate_terminal_snapshot, Mapping)
                else None
            )
            crossing = terminal.get("crossing") if isinstance(terminal, Mapping) else None
            reconciled_usage = (
                self.provider_usage_reconciliation.get("provider_usage")
                if isinstance(self.provider_usage_reconciliation, Mapping)
                else None
            )
            return bool(
                self.provider_gate_exact_for_usage
                and isinstance(terminal, Mapping)
                and terminal.get("crossing_closed") is True
                and terminal.get("close_reason") == PROVIDER_GATE_CLOSE_TOKEN_LIMIT
                and isinstance(reconciled_usage, Mapping)
                and terminal.get("completed_tokens")
                == reconciled_usage.get("total_tokens")
                and isinstance(crossing, Mapping)
                and crossing.get("response_id")
                == self.first_crossing.get("response_id")
                and not self.invalid_reasons
                and not self.interrupt_requested
                and not self.interrupt_request_ids
                and self._authenticated_adapter_teardown(
                    self.adapter_teardown,
                    required_immediate=True,
                )
            )
        accounting = self._accounting_state()
        return (
            drain_complete
            and not self.interrupt_requested
            and not self.invalid_reasons
            and not self.unresolved_thread_ids()
            and accounting["accounting_complete"]
            and (
                self.provider_gate is None
                or self.provider_gate_exact_for_usage
            )
        )

    def snapshot(self, *, drain_complete: bool = False) -> dict[str, Any]:
        boundary_response_id: str | None = None
        if self.submission_boundary is not None:
            candidate = self.submission_boundary.get("response_id")
            boundary_response_id = candidate if isinstance(candidate, str) else None
        accounting = self._accounting_state(
            boundary_response_id=boundary_response_id
        )
        provider_gate_live = (
            self.provider_gate.snapshot() if self.provider_gate is not None else None
        )
        threads: list[dict[str, Any]] = []
        for thread_id in sorted(self.threads):
            thread = self.threads[thread_id]
            projection = accounting["projections"][thread_id]
            threads.append(
                {
                    "thread_id": thread_id,
                    "parent_thread_id": thread["parent_id"],
                    "agent_path": thread["agent_path"],
                    "provisional": thread["provisional"],
                    "spawn_call_id": thread["spawn_call_id"],
                    "spawn_parent_turn_id": thread["spawn_parent_turn_id"],
                    "spawn_parent_response_id": thread[
                        "spawn_parent_response_id"
                    ],
                    "spawn_fork_turns": thread["spawn_fork_turns"],
                    "spawn_fork_semantics": thread["spawn_fork_semantics"],
                    "spawn_binding_status": thread["spawn_binding_status"],
                    "turn_seen": thread["turn_seen"],
                    "active_turn_id": thread["active_turn_id"],
                    "turn_status": thread["turn_status"],
                    "thread_status": thread["thread_status"],
                    "response_count": len(thread["response_ids"]),
                    **thread["raw_sum"],
                    # Retain the old field name as a compatibility alias, but it
                    # is now a derived expectation, never an arbitrary observed
                    # cumulative-minus-raw residual.
                    "cumulative_baseline": thread[
                        "expected_cumulative_baseline"
                    ],
                    "expected_cumulative_baseline": thread[
                        "expected_cumulative_baseline"
                    ],
                    "last_cumulative": thread["last_cumulative"],
                    "cumulative_observation_count": thread[
                        "cumulative_observation_count"
                    ],
                    **projection,
                    "accounting_complete": accounting[
                        "thread_accounting_complete"
                    ][thread_id],
                }
            )
        result = {
            "schema_version": 1,
            "accounting_projection_schema_version": (
                ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION
            ),
            "measurement_source": ULTRA_USAGE_MEASUREMENT_SOURCE,
            "notification": ULTRA_USAGE_NOTIFICATION,
            "usage_scope": ULTRA_USAGE_SCOPE,
            "live_cumulative": True,
            "input_includes_cached": True,
            "root_thread_id": self.root_thread_id,
            "root_turn_id": self.root_turn_id,
            "thread_count": len(self.threads),
            "response_count": len(self.responses),
            **self.aggregate,
            "notification_sequence": self.notification_sequence,
            "observed_at_unix_ns": time.time_ns(),
            "first_crossing": self.first_crossing,
            "stop_reason": self.stop_reason,
            "interrupt_requested": self.interrupt_requested,
            "pending_interrupt_response_count": len(self.interrupt_request_ids),
            "active_thread_ids": sorted(self.active_turns()),
            "unresolved_thread_ids": self.unresolved_thread_ids(),
            "drain_complete": drain_complete,
            "measurement_exact": self._measurement_exact(drain_complete),
            "invalid_reasons": list(self.invalid_reasons),
            **{
                field: accounting[field]
                for field in (
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
                )
            },
            "threads": threads,
            "response_ids": self.ordered_response_ids(),
            "response_ledger": self._response_ledger(),
        }
        if self.provider_gate is not None:
            final_hash = None
            if isinstance(self.provider_gate_final, Mapping):
                candidate_hash = self.provider_gate_final.get("record_sha256")
                if isinstance(candidate_hash, str):
                    final_hash = candidate_hash
            result["provider_token_gate"] = {
                "enabled": True,
                "response_token_bound": PROVIDER_RESPONSE_TOKEN_BOUND,
                "artifact_path": (
                    str(self.provider_gate_artifact_path)
                    if self.provider_gate_artifact_path is not None
                    else None
                ),
                "record_sha256": final_hash,
                "final_attached": self.provider_gate_final is not None,
                "exact_for_usage": self.provider_gate_exact_for_usage,
                "live": provider_gate_live,
                "terminal": self.provider_gate_terminal_snapshot,
            }
            result["provider_usage_reconciliation"] = (
                dict(self.provider_usage_reconciliation)
                if self.provider_usage_reconciliation is not None
                else self.live_provider_usage_reconciliation()
            )
        if self.adapter_teardown is not None:
            result["adapter_teardown"] = dict(self.adapter_teardown)
        if self.submission_boundary is not None:
            result["submission_boundary"] = dict(self.submission_boundary)
        return result

    def _unindexed_fork_hook_call_ids(self) -> set[str]:
        """Return authenticated hook IDs awaiting their enclosing response.

        Pinned app-server ordering can expose a spawn ``rawResponseItem`` and
        its hook lifecycle before the matching ``rawResponse/completed``.  The
        raw spawn call cannot be indexed until that response supplies its
        identity and usage.  Publishing during this interval would therefore
        misrepresent the retained hook as an orphan even though its raw item is
        already pending internally.
        """

        hook_ids = set(self.fork_hook_started) | set(self.fork_hook_completed)
        return hook_ids - set(self.raw_spawn_calls)

    def _root_turn_start_notification_pending(self) -> bool:
        """Whether turn/start replied just before its lifecycle notification."""

        root = self.threads.get(self.root_thread_id)
        return bool(
            isinstance(self.root_turn_id, str)
            and self.root_turn_id
            and isinstance(root, Mapping)
            and root.get("turn_seen") is False
            and root.get("active_turn_id") is None
            and root.get("turn_status") is None
            and self.root_prompt_turn_status is None
            and len(self.threads) == 1
            and not self.responses
            and self.notification_sequence == 0
            and all(self.aggregate[field] == 0 for field in self._SUM_FIELDS)
            and self.first_crossing is None
            and self.submission_boundary is None
            and not self.invalid_reasons
            and not self.interrupt_requested
            and not self.interrupt_request_ids
        )

    def _provisional_child_binding_pending(self) -> bool:
        """Whether a discovered child is awaiting its parent-edge activity.

        The app server may emit a child's status notification immediately
        before the parent's matching ``subAgentActivity`` item.  Retain that
        status internally, but keep the last valid live snapshot until the
        activity supplies the authenticated parent edge.  Final drain is not
        deferred, so a genuinely orphaned child still fails closed.
        """

        return bool(self.unresolved_thread_ids())

    def _compaction_crossing_finalization_pending(self) -> bool:
        """Whether the crossing response is awaiting its sealed gate edge.

        The app server publishes ``rawResponse/completed`` just before the
        adapter seals and attaches the provider-gate record.  Publishing in
        that narrow gap exposes a real second response with a temporarily null
        gate edge, which the strict runner must reject.  Keep the previous live
        snapshot until finalization attaches the authoritative call.  Final
        drain is never deferred, so a failed attachment still surfaces.
        """

        crossing_response_id = (
            self.first_crossing.get("response_id")
            if isinstance(self.first_crossing, Mapping)
            else None
        )
        return bool(
            self.compaction_canary_authorized
            and isinstance(self.compaction_turn_id, str)
            and self.compaction_turn_id
            and isinstance(self.compaction_response_id, str)
            and self.compaction_response_id
            and crossing_response_id == self.compaction_response_id
            and self.provider_gate is not None
            and self.provider_gate_final is None
        )

    def publish(self, *, drain_complete: bool = False) -> None:
        if (
            self.provider_gate is not None
            and not self._reconciling_explicit_child_interrupts
        ):
            self._reconciling_explicit_child_interrupts = True
            try:
                self.reconcile_discarded_after_explicit_child_interrupts()
            finally:
                self._reconciling_explicit_child_interrupts = False
        # Keep the last atomically published snapshot stable across the valid
        # raw-item/hook/response race.  The matching raw response indexes the
        # spawn and immediately publishes the resulting partial or terminal
        # evidence.  At final drain we must not defer forever: a truly orphaned
        # hook is published and remains fail-closed through the existing
        # incomplete/inexact fork-policy projection.
        if not drain_complete and self._unindexed_fork_hook_call_ids():
            return
        # The app server can report the turn/start RPC result, then a thread
        # status change, and only then the matching turn/started notification.
        # Do not replace the last valid live snapshot during that short gap.
        # Final publication is never deferred, so a missing notification still
        # reaches the runner's strict parser and fails closed.
        if not drain_complete and self._root_turn_start_notification_pending():
            return
        if not drain_complete and self._provisional_child_binding_pending():
            return
        if (
            not drain_complete
            and self._compaction_crossing_finalization_pending()
        ):
            return
        _write_usage_atomic(self.output, self.snapshot(drain_complete=drain_complete))

    def non_root_quiescent(self) -> bool:
        """Whether every known descendant is resolved and terminal."""

        if self.unresolved_thread_ids() or self.interrupt_request_ids:
            return False
        for thread_id, thread in self.threads.items():
            if thread_id == self.root_thread_id:
                continue
            if thread.get("turn_seen") is not True:
                return False
            if thread.get("active_turn_id") is not None:
                return False
            if thread.get("turn_status") not in ("completed", "failed", "interrupted"):
                return False
        return True

    def _pending_submission_outer_exec(
        self,
        *,
        turn_id: str,
        call_id: str,
        candidate_path: str,
        canonical: bool,
    ) -> dict[str, Any] | None:
        """Bind one structurally exact outer/inner attempt by source class."""

        raw_items = self.raw_items_pending.get((self.root_thread_id, turn_id))
        if not isinstance(raw_items, list):
            return None
        allowed_types = {"message", "agent_message", "reasoning", "custom_tool_call"}
        if any(
            not isinstance(item, Mapping) or item.get("type") not in allowed_types
            for item in raw_items
        ):
            return None
        tool_items = [
            item for item in raw_items if item.get("type") == "custom_tool_call"
        ]
        if len(tool_items) != 1:
            return None
        item = tool_items[0]
        if not raw_items or raw_items[-1] is not item:
            return None
        outer_raw_item_id = item.get("id")
        outer_call_id = item.get("call_id")
        outer_input = item.get("input")
        if (
            item.get("name") != "exec"
            or item.get("namespace") not in (None, "")
            or item.get("status") != "completed"
            or not isinstance(outer_raw_item_id, str)
            or not outer_raw_item_id
            or not isinstance(outer_call_id, str)
            or not outer_call_id
            or len({outer_raw_item_id, outer_call_id, call_id}) != 3
            or not isinstance(outer_input, str)
            or is_canonical_nested_submit_exec_input(
                outer_input, candidate_path=candidate_path
            )
            != canonical
        ):
            return None
        outer_observation = self.raw_item_observations.get(outer_raw_item_id)
        if (
            not isinstance(outer_observation, Mapping)
            or outer_observation.get("thread_id") != self.root_thread_id
            or outer_observation.get("turn_id") != turn_id
            or outer_observation.get("item") != item
        ):
            return None
        inner_start = self.dynamic_tool_starts.get(call_id)
        if (
            not isinstance(inner_start, Mapping)
            or inner_start.get("thread_id") != self.root_thread_id
            or inner_start.get("turn_id") != turn_id
            or inner_start.get("call_id") != call_id
            or inner_start.get("namespace") not in (None, "")
            or inner_start.get("tool") != SUBMISSION_TOOL_NAME
            or inner_start.get("arguments") != {"candidate_path": candidate_path}
            or inner_start.get("status") != "inProgress"
        ):
            return None
        outer_observed_ns = outer_observation.get("observed_at_monotonic_ns")
        inner_started_ns = inner_start.get("observed_at_monotonic_ns")
        if (
            not isinstance(outer_observed_ns, int)
            or isinstance(outer_observed_ns, bool)
            or not isinstance(inner_started_ns, int)
            or isinstance(inner_started_ns, bool)
            or outer_observed_ns > inner_started_ns
        ):
            return None
        return {
            "outer_raw_item_id": outer_raw_item_id,
            "outer_exec_call_id": outer_call_id,
            "outer_exec_program": outer_input,
            "outer_raw_item_observed_at_monotonic_ns": outer_observed_ns,
            "inner_dynamic_item_started_at_monotonic_ns": inner_started_ns,
        }

    def pending_submission_wire(
        self, *, turn_id: str, call_id: str, candidate_path: str
    ) -> dict[str, Any] | None:
        """Bind the already-observed outer exec and inner dynamic-tool start."""

        outer = self._pending_submission_outer_exec(
            turn_id=turn_id,
            call_id=call_id,
            candidate_path=candidate_path,
            canonical=True,
        )
        if outer is None:
            return None
        outer_input = outer["outer_exec_program"]
        assert isinstance(outer_input, str)
        return {
            "submission_transport": NESTED_SUBMISSION_WIRE_FORMAT,
            "outer_raw_item_id": outer["outer_raw_item_id"],
            "outer_raw_item_type": "custom_tool_call",
            "outer_exec_name": "exec",
            "outer_exec_call_id": outer["outer_exec_call_id"],
            "outer_exec_program": outer_input,
            "outer_exec_program_bytes": len(outer_input.encode("utf-8")),
            "outer_exec_program_sha256": hashlib.sha256(
                outer_input.encode("utf-8")
            ).hexdigest(),
            **nested_submission_exec_yield_record(),
            "outer_raw_item_observed_at_monotonic_ns": outer[
                "outer_raw_item_observed_at_monotonic_ns"
            ],
            "inner_dynamic_item_started_at_monotonic_ns": outer[
                "inner_dynamic_item_started_at_monotonic_ns"
            ],
            "outer_raw_item_observed_before_inner_dynamic_call": True,
        }

    def noncanonical_submission_wire_attempt(
        self, *, turn_id: str, call_id: str, candidate_path: str
    ) -> bool:
        """Whether the current exact outer/inner shape has the wrong source bytes."""

        pending_key = (self.root_thread_id, turn_id)
        if isinstance(self.raw_items_pending.get(pending_key), list):
            return self._pending_submission_outer_exec(
                turn_id=turn_id,
                call_id=call_id,
                candidate_path=candidate_path,
                canonical=False,
            ) is not None
        if not self.responses:
            return False
        _response_id, response = max(
            self.responses.items(), key=lambda entry: int(entry[1].get("sequence", 0))
        )
        if (
            response.get("sequence") != self.notification_sequence
            or response.get("thread_id") != self.root_thread_id
            or response.get("turn_id") != turn_id
            or any(
                pending
                for (thread_id, _pending_turn_id), pending in self.raw_items_pending.items()
                if thread_id == self.root_thread_id
            )
        ):
            return False
        raw_items = response.get("raw_items")
        if not isinstance(raw_items, list):
            return False
        self.raw_items_pending[pending_key] = raw_items
        try:
            return self._pending_submission_outer_exec(
                turn_id=turn_id,
                call_id=call_id,
                candidate_path=candidate_path,
                canonical=False,
            ) is not None
        finally:
            self.raw_items_pending.pop(pending_key, None)

    def matching_submit_response(
        self,
        *,
        turn_id: str,
        call_id: str,
        candidate_path: str,
        expected_wire: Mapping[str, Any],
    ) -> tuple[str, dict[str, Any], dict[str, Any]] | None:
        """Find the completed raw response whose sole tool call is this submit."""

        match = self.completed_submission_response(
            turn_id=turn_id,
            call_id=call_id,
            candidate_path=candidate_path,
        )
        if match is None or dict(match[2]) != dict(expected_wire):
            return None
        return match

    def completed_submission_response(
        self, *, turn_id: str, call_id: str, candidate_path: str
    ) -> tuple[str, dict[str, Any], dict[str, Any]] | None:
        """Bind only the latest completed response to an exact nested submit wire.

        This supports both app-server orders: the inner dynamic request can be
        observed either before or after ``rawResponse/completed``.  A completed
        response is eligible only when it is the globally latest response, the
        latest root response, and no later root raw item has begun.  We never
        search backwards past an unrelated response or projection gap.
        """

        if not self.responses:
            return None
        response_id, response = max(
            self.responses.items(), key=lambda entry: int(entry[1].get("sequence", 0))
        )
        if (
            response.get("sequence") != self.notification_sequence
            or response.get("thread_id") != self.root_thread_id
            or response.get("turn_id") != turn_id
            or any(
                pending
                for (thread_id, _pending_turn_id), pending in self.raw_items_pending.items()
                if thread_id == self.root_thread_id
            )
        ):
            return None
        raw_items = response.get("raw_items")
        if not isinstance(raw_items, list):
            return None
        pending_key = (self.root_thread_id, turn_id)
        prior_pending = self.raw_items_pending.get(pending_key)
        self.raw_items_pending[pending_key] = raw_items
        try:
            wire = self.pending_submission_wire(
                turn_id=turn_id,
                call_id=call_id,
                candidate_path=candidate_path,
            )
        finally:
            if prior_pending is None:
                self.raw_items_pending.pop(pending_key, None)
            else:
                self.raw_items_pending[pending_key] = prior_pending
        if wire is None:
            return None
        return response_id, response, wire

    def boundary_eligible(
        self, *, turn_id: str, submit_response_id: str | None = None
    ) -> str | None:
        """Return a fail-closed reason unless submit is an exact model boundary."""

        if self.submission_boundary is not None:
            return "a submission boundary was already accepted"
        completed_tokens = self.aggregate["total_tokens"]
        if self.provider_gate is not None:
            gate_state = _provider_gate_state_view(self.provider_gate.snapshot())
            candidate_tokens = gate_state.get("completed_tokens")
            if isinstance(candidate_tokens, int) and not isinstance(
                candidate_tokens, bool
            ):
                completed_tokens = candidate_tokens
        if self.first_crossing is not None or completed_tokens >= self.token_limit:
            return "the exact model-token cap has been reached"
        if self.interrupt_requested or self.interrupt_request_ids:
            return "the rooted tree has been interrupted"
        if self.invalid_reasons:
            return "the rooted-tree usage ledger is invalid"
        if not self.non_root_quiescent():
            return "all descendant threads must be terminal before submission"
        accounting = self._accounting_state(
            boundary_response_id=submit_response_id,
            pre_submission=submit_response_id is None,
        )
        if not accounting["spawn_linkage_complete"]:
            return "all descendant spawn links must be schema-bound before submission"
        if not accounting["descendant_accounting_complete"]:
            return "all descendant token projections must be complete before submission"
        if not accounting["accounting_complete"]:
            return "the root token projection is incomplete at submission"
        active = self.active_turns()
        if active != {self.root_thread_id: turn_id}:
            return "only the submitting root turn may remain active"
        return None

    def accept_submission_boundary(self, boundary: Mapping[str, Any]) -> None:
        """Publish the immutable first-valid ledger before killing app-server."""

        if self.submission_boundary is not None:
            raise RuntimeError("submission boundary cannot be replaced")
        response_id = boundary.get("response_id")
        if not isinstance(response_id, str) or not self._accounting_state(
            boundary_response_id=response_id
        )["accounting_complete"]:
            raise RuntimeError("submission boundary has incomplete token accounting")
        self.submission_boundary = dict(boundary)
        self.stop_reason = "first_valid_proof"
        self.publish(drain_complete=False)


def _write_usage_atomic(path: Path, usage: Mapping[str, Any]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_suffix(path.suffix + ".tmp")
    temporary.write_text(json.dumps(usage, sort_keys=True) + "\n", encoding="utf-8")
    os.replace(temporary, path)


def _write_protocol_message(stream: TextIO, message: Mapping[str, Any]) -> None:
    stream.write(
        json.dumps(message, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    )
    stream.flush()


def _read_protocol_message(stream: TextIO) -> dict[str, Any]:
    """Read one JSON object while copying every server stdout line to the audit log."""

    while True:
        line = stream.readline()
        if line == "":
            raise RuntimeError("Codex app-server ended before the turn completed")
        sys.stdout.write(line)
        sys.stdout.flush()
        try:
            message = json.loads(line)
        except json.JSONDecodeError:
            # App-server diagnostics share stdout because stderr is deliberately
            # merged into it.  Preserve them verbatim, but they are not protocol.
            continue
        if not isinstance(message, dict):
            raise RuntimeError("Codex app-server emitted a non-object JSON message")
        return message


def _response_result(message: Mapping[str, Any], request_id: int, label: str) -> Any:
    if message.get("id") != request_id or "method" in message:
        raise RuntimeError(f"internal protocol error while waiting for {label}")
    if "error" in message:
        raise RuntimeError(
            f"Codex app-server rejected {label}: "
            + json.dumps(message["error"], sort_keys=True, ensure_ascii=False)
        )
    if "result" not in message:
        raise RuntimeError(f"Codex app-server returned no result for {label}")
    return message["result"]


def _request(
    stdin: TextIO,
    stdout: TextIO,
    *,
    request_id: int,
    method: str,
    params: Mapping[str, Any],
    on_notification: Callable[[dict[str, Any]], None],
) -> Any:
    _write_protocol_message(
        stdin,
        {"id": request_id, "method": method, "params": dict(params)},
    )
    return _await_response(
        stdout,
        request_id=request_id,
        method=method,
        on_notification=on_notification,
    )


def _await_response(
    stdout: TextIO,
    *,
    request_id: int,
    method: str,
    on_notification: Callable[[dict[str, Any]], None],
) -> Any:
    while True:
        message = _read_protocol_message(stdout)
        if message.get("id") == request_id and "method" not in message:
            return _response_result(message, request_id, method)
        on_notification(message)


class _ProtocolReader:
    """Give Ultra one stdout reader so buffered JSONL cannot evade polling."""

    def __init__(self, stream: TextIO) -> None:
        self.stream = stream
        self.messages: queue.Queue[dict[str, Any] | BaseException] = queue.Queue()
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()

    def _run(self) -> None:
        try:
            while True:
                self.messages.put(_read_protocol_message(self.stream))
        except BaseException as error:
            self.messages.put(error)

    def get(self, timeout: float | None = None) -> dict[str, Any]:
        item = self.messages.get(timeout=timeout)
        if isinstance(item, BaseException):
            raise item
        return item

    def get_nowait(self) -> dict[str, Any]:
        return self.get(timeout=0.0)


def _request_queued(
    stdin: TextIO,
    reader: _ProtocolReader,
    *,
    request_id: int,
    method: str,
    params: Mapping[str, Any],
    on_notification: Callable[[dict[str, Any]], None],
) -> Any:
    _write_protocol_message(
        stdin, {"id": request_id, "method": method, "params": dict(params)}
    )
    return _await_response_queued(
        reader,
        request_id=request_id,
        method=method,
        on_notification=on_notification,
    )


def _await_response_queued(
    reader: _ProtocolReader,
    *,
    request_id: int,
    method: str,
    on_notification: Callable[[dict[str, Any]], None],
) -> Any:
    while True:
        message = reader.get()
        if message.get("id") == request_id and "method" not in message:
            return _response_result(message, request_id, method)
        on_notification(message)


def _thread_id_from_result(result: Any, label: str) -> str:
    if not isinstance(result, Mapping) or not isinstance(result.get("thread"), Mapping):
        raise RuntimeError(f"Codex app-server returned malformed {label} result")
    thread_id = result["thread"].get("id")
    if not isinstance(thread_id, str) or not thread_id:
        raise RuntimeError(f"Codex app-server returned no thread id for {label}")
    return thread_id


def _turn_id_from_result(result: Any, label: str) -> str:
    if not isinstance(result, Mapping) or not isinstance(result.get("turn"), Mapping):
        raise RuntimeError(f"Codex app-server returned malformed {label} result")
    turn_id = result["turn"].get("id")
    if not isinstance(turn_id, str) or not turn_id:
        raise RuntimeError(f"Codex app-server returned no turn id for {label}")
    return turn_id


def _require_materialized_thread(result: Any) -> None:
    """Fail closed unless app-server honored the disposable persisted root."""

    if not isinstance(result, Mapping) or not isinstance(result.get("thread"), Mapping):
        raise RuntimeError("Codex app-server omitted the thread record")
    if result["thread"].get("ephemeral") is not False:
        raise RuntimeError(
            "Codex app-server did not attest a materialized root thread"
        )


def _remove_state_root(state_root: Path) -> None:
    """Remove one exact attempt state tree or fail the adapter closed."""

    last_error: OSError | None = None
    for attempt in range(STATE_CLEANUP_ATTEMPTS):
        try:
            shutil.rmtree(state_root)
        except FileNotFoundError:
            return
        except OSError as error:
            last_error = error
        if not state_root.exists() and not state_root.is_symlink():
            return
        if attempt + 1 < STATE_CLEANUP_ATTEMPTS:
            time.sleep(STATE_CLEANUP_RETRY_SECONDS)
    detail = str(last_error) if last_error is not None else "path still exists"
    raise RuntimeError(f"could not remove temporary Codex state directory: {detail}")


def _stop_child(
    process: subprocess.Popen[str],
    *,
    process_group: bool = False,
    immediate: bool = False,
) -> dict[str, Any]:
    """Stop one app-server and, when isolated, its complete tool process group."""

    started_unix_ns = time.time_ns()
    started_monotonic_ns = time.monotonic_ns()
    if process.stdin is not None:
        with contextlib.suppress(OSError, ValueError):
            process.stdin.close()

    signal_name: str | None = None

    def send_group_or_child(sig: signal.Signals) -> None:
        nonlocal signal_name
        signal_name = sig.name
        if process_group:
            pid = getattr(process, "pid", None)
            if isinstance(pid, int) and pid > 1:
                pgid = os.getpgid(pid)
                if pgid != pid:
                    raise RuntimeError(
                        "isolated Codex app-server is not its process-group leader"
                    )
                os.killpg(pgid, sig)
                return
        if sig == signal.SIGTERM:
            process.terminate()
        else:
            process.kill()

    if process.poll() is None and not immediate:
        try:
            process.wait(timeout=0.25)
        except subprocess.TimeoutExpired:
            pass
    if process.poll() is None:
        with contextlib.suppress(ProcessLookupError):
            send_group_or_child(signal.SIGTERM)
        try:
            process.wait(timeout=2.0)
        except subprocess.TimeoutExpired:
            with contextlib.suppress(ProcessLookupError):
                send_group_or_child(signal.SIGKILL)
            try:
                process.wait(timeout=2.0)
            except subprocess.TimeoutExpired as error:
                raise RuntimeError("could not stop isolated Codex process group") from error
    returncode = process.poll()
    return {
        "process_group_isolated": process_group,
        "immediate": immediate,
        "stdin_closed": True,
        "signal": signal_name,
        "returncode": returncode,
        "completed": returncode is not None,
        "started_at_unix_ns": started_unix_ns,
        "started_at_monotonic_ns": started_monotonic_ns,
        "completed_at_unix_ns": time.time_ns(),
        "completed_at_monotonic_ns": time.monotonic_ns(),
    }


def _bind(command: list[str], source: Path, destination: str, *, writable: bool) -> None:
    source = source.resolve()
    if not source.exists():
        raise RuntimeError(f"required bind source does not exist: {source}")
    command.extend(("--bind" if writable else "--ro-bind", str(source), destination))


def _provider_gate_config(base_url: str) -> str:
    """Return the exact HTTP-only custom OpenAI provider inline table."""

    if not isinstance(base_url, str) or not base_url:
        raise RuntimeError("Ultra requires a started provider-token gate")
    parsed = urlsplit(base_url)
    try:
        port = parsed.port
    except ValueError as error:
        raise RuntimeError("provider-token gate returned an invalid port") from error
    if (
        parsed.scheme != "http"
        or parsed.hostname != "127.0.0.1"
        or port is None
        or not 0 < port < 65_536
        or parsed.username is not None
        or parsed.password is not None
        or parsed.query
        or parsed.fragment
        or not parsed.path.endswith("/backend-api/codex")
    ):
        raise RuntimeError("provider-token gate returned an unsafe base URL")
    return (
        "{"
        'name="OpenAI",'
        f"base_url={json.dumps(base_url)},"
        'wire_api="responses",'
        "requires_openai_auth=true,"
        "supports_websockets=false,"
        "request_max_retries=0,"
        "stream_max_retries=0"
        "}"
    )


def bubblewrap_command(args: argparse.Namespace, state_home: Path) -> list[str]:
    if args.token_limit <= 0:
        raise RuntimeError("token limit must be positive")
    advisory_rollout_budget_limit = getattr(
        args, "advisory_rollout_budget_limit", None
    )
    if advisory_rollout_budget_limit is None:
        advisory_rollout_budget_limit = args.token_limit
    if advisory_rollout_budget_limit <= 0:
        raise RuntimeError("advisory rollout-budget limit must be positive")
    marker = getattr(args, "network_violation_marker", None)
    if not isinstance(marker, Path):
        raise RuntimeError("a per-run network-violation marker is required")
    marker = _below(args.workspace, marker)
    if marker.is_symlink() or not marker.is_file():
        raise RuntimeError("network-violation marker must be a regular file")
    marker_relative = marker.relative_to(args.workspace.resolve())
    marker_inside = "/workspace/" + marker_relative.as_posix()
    fork_policy_artifacts: tuple[Path, Path, dict[str, Any]] | None = None
    provider_config: str | None = None
    if args.reasoning_effort == ULTRA_REASONING_EFFORT:
        provider_response_bound = getattr(args, "provider_response_bound", None)
        if provider_response_bound != PROVIDER_RESPONSE_TOKEN_BOUND:
            raise RuntimeError(
                "Ultra provider response bound must equal the frozen model bound"
            )
        fork_policy_artifacts = _prepare_ultra_fork_policy(
            state_home.parent, args.inside_home
        )
        provider_config = _provider_gate_config(
            getattr(args, "provider_gate_base_url", None)
        )
    command = [
        str(args.bwrap.resolve()),
        "--unshare-all",
        "--share-net",
        "--die-with-parent",
        "--ro-bind",
        "/usr",
        "/usr",
        "--ro-bind",
        "/bin",
        "/bin",
        "--ro-bind",
        "/lib",
        "/lib",
        "--ro-bind",
        "/lib64",
        "/lib64",
        "--ro-bind",
        "/etc",
        "/etc",
        "--proc",
        "/proc",
        "--dev",
        "/dev",
        "--tmpfs",
        "/tmp",
        "--dir",
        "/run",
        "--dir",
        "/run/systemd",
    ]
    _bind(command, args.resolver_root, "/run/systemd/resolve", writable=False)
    command.extend(("--dir", "/u501"))
    _bind(command, state_home, args.inside_home, writable=True)
    if fork_policy_artifacts is not None:
        hooks_path, helper_path, policy_record = fork_policy_artifacts
        _bind(
            command,
            hooks_path,
            str(policy_record["source_path"]),
            writable=False,
        )
        helper_inside = str(
            PurePosixPath(args.inside_home)
            / ".codex"
            / ULTRA_FORK_POLICY_HELPER_FILENAME
        )
        _bind(command, helper_path, helper_inside, writable=False)
    _bind(command, args.workspace, "/workspace", writable=True)
    if args.controlled_relative:
        controlled = _below(args.workspace, args.workspace / args.controlled_relative)
        _bind(command, controlled, f"/workspace/{args.controlled_relative}", writable=False)
    _bind(command, args.codex, "/codex", writable=False)
    _bind(command, args.offline_shell, "/offline-bash", writable=False)
    _bind(command, args.toolchain_root, "/lean", writable=False)
    _bind(command, args.packages_root, "/packages", writable=False)
    if args.shared_olean_root is not None:
        _bind(command, args.shared_olean_root, "/shared-olean", writable=False)

    # Trusted, frozen paths must win module-name resolution.  The writable
    # workspace is deliberately last so a generated file cannot shadow a
    # controlled definition, NumStability, mathlib, or the Lean toolchain.
    lean_paths: list[str] = []
    if args.shared_olean_root is not None:
        lean_paths.append("/shared-olean")
    if args.shared_root_relative:
        lean_paths.append(f"/workspace/{args.shared_root_relative}")
    if args.condition == "L":
        lean_paths.append("/library-olean")
    lean_paths.append("/packages/mathlib/.lake/build/lib/lean")
    for package in sorted(args.packages_root.iterdir(), key=lambda item: item.name):
        build_path = package / ".lake" / "build" / "lib" / "lean"
        if package.name != "mathlib" and build_path.is_dir():
            lean_paths.append(f"/packages/{package.name}/.lake/build/lib/lean")
    lean_paths.append("/lean/lib/lean")
    lean_paths.append("/workspace")

    if args.condition == "L":
        if args.library_source is None or args.library_olean is None:
            raise RuntimeError("condition L requires --library-source and --library-olean")
        command.extend(("--dir", "/library"))
        _bind(command, args.library_source, "/library/NumStability", writable=False)
        if args.library_root_file is not None:
            _bind(command, args.library_root_file, "/library/NumStability.lean", writable=False)
        _bind(command, args.library_olean, "/library-olean", writable=False)
    command.extend(
        (
            "--setenv",
            "PATH",
            "/lean/bin:/usr/bin:/bin",
            "--setenv",
            "HOME",
            args.inside_home,
            "--setenv",
            "LEAN_PATH",
            ":".join(lean_paths),
            "--setenv",
            "SHELL",
            "/offline-bash",
            "--setenv",
            NETWORK_VIOLATION_MARKER_ENV,
            marker_inside,
            "--chdir",
            "/workspace",
            "/codex",
        )
    )
    if args.reasoning_effort == ULTRA_REASONING_EFFORT:
        command.append(ULTRA_FORK_POLICY_TRUST_BYPASS_CLI_FLAG)
    command.extend(
        (
            "app-server",
            "--stdio",
            "--strict-config",
            "--config",
            f'model="{args.model}"',
            "--config",
            f'model_reasoning_effort="{args.reasoning_effort}"',
            "--config",
            'approval_policy="never"',
            "--config",
            'sandbox_mode="danger-full-access"',
            "--config",
            'history.persistence="none"',
            "--config",
            "memories.use_memories=false",
            "--config",
            "memories.generate_memories=false",
            "--config",
            "features.rollout_budget=true",
            "--config",
            "features.rollout_budget.limit_tokens="
            f"{advisory_rollout_budget_limit}",
            "--config",
            "features.rollout_budget.prefill_token_weight=1",
            "--config",
            "features.rollout_budget.sampling_token_weight=1",
        )
    )
    if args.reasoning_effort == ULTRA_REASONING_EFFORT:
        assert provider_config is not None
        command.extend(
            (
                "--config",
                f'model_provider="{PROVIDER_GATE_PROVIDER_ID}"',
                "--config",
                f"model_providers.{PROVIDER_GATE_PROVIDER_ID}={provider_config}",
                "--config",
                f"model_context_window={provider_response_bound}",
                "--config",
                f'agents.default_subagent_model="{args.model}"',
                "--config",
                "agents.default_subagent_reasoning_effort=\"ultra\"",
                "--config",
                "features.multi_agent_v2.expose_spawn_agent_model_overrides=false",
                "--config",
                "features.multi_agent_v2.hide_spawn_agent_metadata=true",
                "--config",
                "features.multi_agent_v2.max_concurrent_threads_per_session=4",
                "--config",
                "features.multi_agent_v2.usage_hint_enabled=true",
                "--config",
                "features.multi_agent_v2.usage_hint_text="
                + json.dumps(ULTRA_FORK_USAGE_HINT, ensure_ascii=False),
            )
        )
    for feature in DISABLED_FEATURES:
        command.extend(("--disable", feature))
    if args.reasoning_effort == ULTRA_REASONING_EFFORT:
        command.extend(
            (
                "--disable",
                "enable_request_compression",
                "--enable",
                "remote_compaction_v2",
                "--enable",
                "hooks",
                "--enable",
                "multi_agent",
            )
        )
    else:
        command.extend(("--disable", "multi_agent"))
    return command


def _sanitized_environment() -> dict[str, str]:
    allowed = ("HOME", "LANG", "LC_ALL", "LOGNAME", "TERM", "TZ", "USER")
    environment = {key: os.environ[key] for key in allowed if key in os.environ}
    environment["PATH"] = "/usr/bin:/bin"
    return environment


def _provider_gate_matches_ledger(
    record: Mapping[str, Any],
    terminal_snapshot: Mapping[str, Any],
    ledger: AttemptUsageLedger,
    *,
    close_reason: str,
) -> dict[str, Any] | None:
    """Build the exact provider/app-server delivery reconciliation."""

    state = _provider_gate_state_view(terminal_snapshot)
    recorded_state = record.get("state")
    calls = record.get("calls")
    invariants = record.get("invariants")
    if (
        not isinstance(recorded_state, Mapping)
        or dict(recorded_state) != dict(state)
        or not isinstance(calls, list)
        or not isinstance(invariants, Mapping)
        or not invariants
        or any(value is not True for value in invariants.values())
        or state.get("phase") != "CLOSED"
        or state.get("close_reason") != close_reason
        or state.get("open_request_ids") != []
        or state.get("all_complete") is not True
        or state.get("no_post_close_upstream") is not True
        or state.get("poisoned") is not False
        or state.get("poison_reasons") != []
    ):
        return None
    completed_calls = [
        call
        for call in calls
        if isinstance(call, Mapping)
        and isinstance(call.get("normalized_usage"), Mapping)
    ]
    if len(completed_calls) != len(calls):
        return None
    try:
        provider_calls = sorted(
            completed_calls,
            key=lambda call: (int(call["commit_monotonic_ns"]), int(call["sequence"])),
        )
    except (KeyError, TypeError, ValueError):
        return None
    by_response: dict[str, Mapping[str, Any]] = {}
    for call in provider_calls:
        response_id = call.get("response_id")
        if not isinstance(response_id, str) or not response_id or response_id in by_response:
            return None
        by_response[response_id] = call
    direct_calls: list[Mapping[str, Any]] = []
    suppressed_calls: list[Mapping[str, Any]] = []
    superseded_calls: list[Mapping[str, Any]] = []
    discarded_calls: list[Mapping[str, Any]] = []
    manifest_keys = {
        "schema_version",
        "response_id",
        "output_item_count",
        "action_capable_item_count",
        "items",
    }
    manifest_item_keys = {
        "index",
        "id",
        "type",
        "name",
        "namespace",
        "call_id",
        "payload_sha256",
        "payload_bytes",
        "arguments_sha256",
        "arguments_bytes",
        "wait_timeout_ms",
    }
    delivery_keys = {
        "kind",
        "successor_call_id",
        "successor_response_id",
        "bind_unix_ns",
        "bind_monotonic_ns",
    }
    for call in provider_calls:
        delivery = call.get("appserver_delivery")
        if not isinstance(delivery, Mapping) or set(delivery) != delivery_keys:
            return None
        if any(
            isinstance(delivery.get(field), bool)
            or not isinstance(delivery.get(field), int)
            or delivery[field] <= 0
            for field in ("bind_unix_ns", "bind_monotonic_ns")
        ):
            return None
        if delivery.get("kind") == "direct_raw_response":
            if (
                call.get("error") is not None
                or call.get("client_release_complete") is not True
                or
                delivery.get("successor_call_id") is not None
                or delivery.get("successor_response_id") is not None
                or not isinstance(call.get("appserver_crossbind"), Mapping)
            ):
                return None
            direct_calls.append(call)
            continue
        if delivery.get("kind") == "superseded_by_collaboration_message":
            manifest = call.get("response_output_manifest")
            items = manifest.get("items") if isinstance(manifest, Mapping) else None
            if not isinstance(items, list) or any(
                not isinstance(item, Mapping)
                or set(item) != manifest_item_keys
                or item.get("index") != index
                or not isinstance(item.get("type"), str)
                or not isinstance(item.get("payload_sha256"), str)
                or re.fullmatch(r"[0-9a-f]{64}", item["payload_sha256"])
                is None
                or isinstance(item.get("payload_bytes"), bool)
                or not isinstance(item.get("payload_bytes"), int)
                or item["payload_bytes"] <= 0
                for index, item in enumerate(items or [])
            ):
                return None
            if (
                call.get("appserver_crossbind") is not None
                or call.get("crossed_cap") is not False
                or call.get("release_kind") != "byte_identity"
                or call.get("released_body_sha256")
                != call.get("upstream_body_sha256")
                or call.get("released_body_bytes")
                != call.get("upstream_body_bytes")
                or call.get("client_release_complete") is not True
                or call.get("error") is not None
                or not isinstance(call.get("request_metadata"), Mapping)
                or call["request_metadata"].get("request_kind") != "turn"
                or not isinstance(manifest, Mapping)
                or set(manifest) != manifest_keys
                or manifest.get("schema_version") != 1
                or manifest.get("response_id") != call.get("response_id")
                or not isinstance(items, list)
                or manifest.get("output_item_count") != len(items)
                or not isinstance(delivery.get("successor_call_id"), str)
                or not delivery.get("successor_call_id")
                or not isinstance(delivery.get("successor_response_id"), str)
                or not delivery.get("successor_response_id")
            ):
                return None
            superseded_calls.append(call)
            continue
        if delivery.get("kind") == "discarded_after_explicit_child_interrupt":
            if (
                call.get("appserver_crossbind") is not None
                or call.get("crossed_cap") is not False
                or call.get("release_kind") != "byte_identity"
                or call.get("released_body_sha256")
                != call.get("upstream_body_sha256")
                or call.get("released_body_bytes")
                != call.get("upstream_body_bytes")
                or call.get("client_release_complete") is not False
                or call.get("error") is not None
                or not isinstance(call.get("request_metadata"), Mapping)
                or call["request_metadata"].get("request_kind") != "turn"
                or not isinstance(delivery.get("successor_call_id"), str)
                or not delivery.get("successor_call_id")
                or not isinstance(delivery.get("successor_response_id"), str)
                or not delivery.get("successor_response_id")
            ):
                return None
            discarded_calls.append(call)
            continue
        if delivery.get("kind") != "suppressed_collaboration_wait":
            return None
        manifest = call.get("response_output_manifest")
        items = manifest.get("items") if isinstance(manifest, Mapping) else None
        if (
            call.get("appserver_crossbind") is not None
            or call.get("crossed_cap") is not False
            or call.get("release_kind") != "byte_identity"
            or call.get("released_body_sha256") != call.get("upstream_body_sha256")
            or call.get("released_body_bytes") != call.get("upstream_body_bytes")
            or call.get("client_release_complete") is not True
            or call.get("error") is not None
            or not isinstance(manifest, Mapping)
            or set(manifest) != manifest_keys
            or manifest.get("schema_version") != 1
            or manifest.get("response_id") != call.get("response_id")
            or not isinstance(items, list)
            or manifest.get("output_item_count") != len(items)
            or manifest.get("action_capable_item_count") != 1
        ):
            return None
        waits: list[Mapping[str, Any]] = []
        for index, item in enumerate(items):
            if (
                not isinstance(item, Mapping)
                or set(item) != manifest_item_keys
                or item.get("index") != index
                or not isinstance(item.get("type"), str)
                or not isinstance(item.get("payload_sha256"), str)
                or re.fullmatch(r"[0-9a-f]{64}", item["payload_sha256"]) is None
                or isinstance(item.get("payload_bytes"), bool)
                or not isinstance(item.get("payload_bytes"), int)
                or item["payload_bytes"] <= 0
            ):
                return None
            if item.get("wait_timeout_ms") is not None:
                waits.append(item)
            elif item.get("type") != "reasoning":
                return None
        if (
            len(waits) != 1
            or waits[0].get("type") != "function_call"
            or waits[0].get("name") != "wait_agent"
            or waits[0].get("namespace") != "collaboration"
            or not isinstance(waits[0].get("id"), str)
            or not isinstance(waits[0].get("call_id"), str)
            or isinstance(waits[0].get("wait_timeout_ms"), bool)
            or not isinstance(waits[0].get("wait_timeout_ms"), int)
        ):
            return None
        suppressed_calls.append(call)
    if {str(call["response_id"]) for call in direct_calls} != set(ledger.responses):
        return None
    for response_id, response in ledger.responses.items():
        call = by_response[response_id]
        crossbind = call.get("appserver_crossbind")
        if (
            dict(call["normalized_usage"]) != dict(response["usage"])
            or call.get("client_release_complete") is not True
            or not isinstance(crossbind, Mapping)
        ):
            return None
        expected = {
            "thread_id": response["thread_id"],
            "turn_id": response["turn_id"],
            "event_sequence": response["sequence"],
        }
        if any(crossbind.get(field) != value for field, value in expected.items()):
            return None
        bound_usage = crossbind.get("normalized_usage", crossbind.get("usage"))
        if not isinstance(bound_usage, Mapping) or dict(bound_usage) != dict(
            response["usage"]
        ):
            return None
        delivery = call["appserver_delivery"]
        if (
            delivery.get("kind") != "direct_raw_response"
            or delivery.get("bind_unix_ns") != crossbind.get("bind_unix_ns")
            or delivery.get("bind_monotonic_ns")
            != crossbind.get("bind_monotonic_ns")
        ):
            return None
    evidence_by_response = ledger.suppressed_collaboration_wait_evidence
    if set(evidence_by_response) != {
        str(call["response_id"]) for call in suppressed_calls
    }:
        return None
    direct_by_id = {str(call["response_id"]): call for call in direct_calls}
    used_messages: set[str] = set()
    evidence: list[dict[str, Any]] = []
    for call in suppressed_calls:
        response_id = str(call["response_id"])
        item = evidence_by_response.get(response_id)
        delivery = call["appserver_delivery"]
        successor_id = delivery.get("successor_response_id")
        successor = direct_by_id.get(successor_id) if isinstance(successor_id, str) else None
        metadata = call.get("request_metadata")
        successor_metadata = (
            successor.get("request_metadata") if isinstance(successor, Mapping) else None
        )
        if (
            not isinstance(item, Mapping)
            or set(item) != set(SUPPRESSED_COLLABORATION_WAIT_EVIDENCE_KEYS)
            or item.get("response_id") != response_id
            or item.get("provider_call_id") != call.get("call_id")
            or item.get("successor_response_id") != successor_id
            or item.get("successor_call_id") != delivery.get("successor_call_id")
            or not isinstance(successor, Mapping)
            or successor.get("call_id") != delivery.get("successor_call_id")
            or not isinstance(metadata, Mapping)
            or not isinstance(successor_metadata, Mapping)
            or item.get("thread_id") != metadata.get("thread_id")
            or item.get("turn_id") != metadata.get("turn_id")
            or metadata.get("thread_id") != successor_metadata.get("thread_id")
            or metadata.get("turn_id") != successor_metadata.get("turn_id")
            or item.get("agent_message_item_id") in used_messages
        ):
            return None
        message_ns = item.get("agent_message_observed_at_monotonic_ns")
        message_unix_ns = item.get("agent_message_observed_at_unix_ns")
        if (
            isinstance(message_ns, bool)
            or not isinstance(message_ns, int)
            or isinstance(message_unix_ns, bool)
            or not isinstance(message_unix_ns, int)
            or not call["commit_unix_ns"] < message_unix_ns
            or message_unix_ns + APP_SERVER_EVENT_TIME_RESOLUTION_NS
            > successor["admitted_unix_ns"]
        ):
            return None
        later_direct = [
            candidate
            for candidate in direct_calls
            if candidate.get("commit_monotonic_ns") > call.get("commit_monotonic_ns")
            and isinstance(candidate.get("request_metadata"), Mapping)
            and candidate["request_metadata"].get("thread_id")
            == metadata.get("thread_id")
            and candidate["request_metadata"].get("turn_id") == metadata.get("turn_id")
        ]
        if not later_direct or min(
            later_direct,
            key=lambda candidate: (
                candidate["commit_monotonic_ns"],
                candidate["sequence"],
            ),
        ) is not successor:
            return None
        used_messages.add(str(item["agent_message_item_id"]))
        evidence.append(dict(item))

    superseded_evidence_by_response = (
        ledger.superseded_by_collaboration_message_evidence
    )
    if set(superseded_evidence_by_response) != {
        str(call["response_id"]) for call in superseded_calls
    }:
        return None
    superseded_evidence: list[dict[str, Any]] = []
    for call in superseded_calls:
        response_id = str(call["response_id"])
        item = superseded_evidence_by_response.get(response_id)
        delivery = call["appserver_delivery"]
        successor_id = delivery.get("successor_response_id")
        successor = by_response.get(successor_id) if isinstance(successor_id, str) else None
        metadata = call.get("request_metadata")
        successor_metadata = (
            successor.get("request_metadata") if isinstance(successor, Mapping) else None
        )
        messages = item.get("collaboration_messages") if isinstance(item, Mapping) else None
        if (
            not isinstance(item, Mapping)
            or set(item)
            != set(SUPERSEDED_BY_COLLABORATION_MESSAGE_EVIDENCE_KEYS)
            or item.get("response_id") != response_id
            or item.get("provider_call_id") != call.get("call_id")
            or item.get("successor_response_id") != successor_id
            or item.get("successor_call_id") != delivery.get("successor_call_id")
            or not isinstance(successor, Mapping)
            or successor.get("call_id") != delivery.get("successor_call_id")
            or not isinstance(metadata, Mapping)
            or not isinstance(successor_metadata, Mapping)
            or metadata.get("request_kind") != "turn"
            or dict(metadata) != dict(successor_metadata)
            or item.get("thread_id") != metadata.get("thread_id")
            or item.get("turn_id") != metadata.get("turn_id")
            or not isinstance(messages, list)
            or not messages
        ):
            return None
        eligible_successors = [
            candidate
            for candidate in provider_calls
            if candidate is not call
            and isinstance(candidate.get("admitted_monotonic_ns"), int)
            and not isinstance(candidate.get("admitted_monotonic_ns"), bool)
            and candidate["admitted_monotonic_ns"] > call["commit_monotonic_ns"]
            and isinstance(candidate.get("request_metadata"), Mapping)
            and dict(candidate["request_metadata"]) == dict(metadata)
            and candidate["request_metadata"].get("request_kind") == "turn"
        ]
        if (
            not eligible_successors
            or min(
                eligible_successors,
                key=lambda candidate: (
                    candidate["admitted_monotonic_ns"],
                    candidate["sequence"],
                ),
            )
            is not successor
            or not isinstance(successor.get("appserver_delivery"), Mapping)
            or successor["appserver_delivery"].get("kind")
            not in (
                "direct_raw_response",
                "superseded_by_collaboration_message",
                "suppressed_collaboration_wait",
            )
        ):
            return None
        normalized_messages: list[dict[str, Any]] = []
        for message in messages:
            target_thread_id = metadata.get("thread_id")
            target_thread = ledger.threads.get(str(target_thread_id))
            target_path = (
                "/root"
                if target_thread_id == ledger.root_thread_id
                else target_thread.get("agent_path")
                if isinstance(target_thread, Mapping)
                else None
            )
            author_thread_ids = {
                candidate_thread_id
                for candidate_thread_id, thread in ledger.threads.items()
                if (
                    candidate_thread_id == ledger.root_thread_id
                    and message.get("author") == "/root"
                )
                or (
                    thread.get("agent_path") == message.get("author")
                    and thread.get("provisional") is False
                    and thread.get("spawn_binding_status") == "resolved"
                )
            }
            adjacent = bool(
                isinstance(target_thread, Mapping)
                and (
                    target_thread.get("parent_id") in author_thread_ids
                    or any(
                        thread.get("parent_id") == target_thread_id
                        and thread.get("agent_path") == message.get("author")
                        for thread in ledger.threads.values()
                    )
                )
            )
            if (
                not isinstance(message, Mapping)
                or set(message) != set(COLLABORATION_MESSAGE_EVIDENCE_KEYS)
                or not isinstance(message.get("item_id"), str)
                or not message.get("item_id")
                or message.get("item_id") in used_messages
                or not isinstance(message.get("item_sha256"), str)
                or re.fullmatch(r"[0-9a-f]{64}", message["item_sha256"])
                is None
                or message.get("recipient") != target_path
                or len(author_thread_ids) != 1
                or not adjacent
            ):
                return None
            message_ns = message.get("observed_at_monotonic_ns")
            message_unix_ns = message.get("observed_at_unix_ns")
            if (
                isinstance(message_ns, bool)
                or not isinstance(message_ns, int)
                or isinstance(message_unix_ns, bool)
                or not isinstance(message_unix_ns, int)
                or not call["commit_unix_ns"] < message_unix_ns
                or message_unix_ns + APP_SERVER_EVENT_TIME_RESOLUTION_NS
                > successor["admitted_unix_ns"]
            ):
                return None
            used_messages.add(str(message["item_id"]))
            normalized_messages.append(dict(message))
        if normalized_messages != sorted(
            normalized_messages,
            key=lambda message: (
                message["observed_at_unix_ns"],
                message["item_id"],
                message["observed_at_monotonic_ns"],
            ),
        ):
            return None
        superseded_evidence.append(dict(item))

    discarded_evidence_by_response = (
        ledger.discarded_after_explicit_child_interrupt_evidence
    )
    if set(discarded_evidence_by_response) != {
        str(call["response_id"]) for call in discarded_calls
    }:
        return None
    discarded_evidence: list[dict[str, Any]] = []
    for call in discarded_calls:
        response_id = str(call["response_id"])
        item = discarded_evidence_by_response.get(response_id)
        delivery = call["appserver_delivery"]
        interrupting = by_response.get(str(delivery.get("successor_response_id")))
        metadata = call.get("request_metadata")
        interrupt_metadata = (
            interrupting.get("request_metadata")
            if isinstance(interrupting, Mapping)
            else None
        )
        manifest = (
            interrupting.get("response_output_manifest")
            if isinstance(interrupting, Mapping)
            else None
        )
        manifest_items = manifest.get("items") if isinstance(manifest, Mapping) else None
        interrupt_functions = [
            manifest_item
            for manifest_item in manifest_items or []
            if isinstance(manifest_item, Mapping)
            and manifest_item.get("type") == "function_call"
            and manifest_item.get("name") == "interrupt_agent"
            and manifest_item.get("namespace") == "collaboration"
        ]
        if (
            not isinstance(item, Mapping)
            or set(item)
            != set(DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_EVIDENCE_KEYS)
            or not isinstance(metadata, Mapping)
            or not isinstance(interrupt_metadata, Mapping)
            or not isinstance(interrupting, Mapping)
            or interrupting.get("call_id") != delivery.get("successor_call_id")
            or not isinstance(manifest, Mapping)
            or not isinstance(manifest_items, list)
            or manifest.get("action_capable_item_count") != 1
            or len(interrupt_functions) != 1
            or any(
                manifest_item is not interrupt_functions[0]
                and manifest_item.get("type") != "reasoning"
                for manifest_item in manifest_items
                if isinstance(manifest_item, Mapping)
            )
            or item.get("response_id") != response_id
            or item.get("provider_call_id") != call.get("call_id")
            or item.get("thread_id") != metadata.get("thread_id")
            or item.get("turn_id") != metadata.get("turn_id")
            or item.get("interrupting_response_id")
            != interrupting.get("response_id")
            or item.get("interrupting_provider_call_id")
            != interrupting.get("call_id")
            or item.get("interrupt_function_item_id")
            != interrupt_functions[0].get("id")
            or item.get("interrupt_function_call_id")
            != interrupt_functions[0].get("call_id")
            or item.get("interrupt_function_arguments_sha256")
            != interrupt_functions[0].get("arguments_sha256")
            or item.get("interrupt_parent_thread_id")
            != interrupt_metadata.get("thread_id")
            or item.get("interrupt_parent_turn_id")
            != interrupt_metadata.get("turn_id")
            or response_id in ledger.responses
        ):
            return None
        child = ledger.threads.get(str(item.get("thread_id")))
        interrupted_turn = ledger.terminal_turn_lifecycles.get(
            (str(item.get("thread_id")), str(item.get("turn_id")))
        )
        if (
            not isinstance(child, Mapping)
            or not isinstance(interrupted_turn, Mapping)
            or child.get("parent_id") != item.get("interrupt_parent_thread_id")
            or child.get("agent_path") != item.get("interrupted_agent_path")
            or interrupted_turn.get("thread_id") != item.get("thread_id")
            or interrupted_turn.get("turn_id") != item.get("turn_id")
            or interrupted_turn.get("status") != "interrupted"
            or interrupted_turn.get("turn_completed_event_unix_ns")
            != item.get("interrupted_turn_observed_at_unix_ns")
            or interrupted_turn.get("turn_completed_at_monotonic_ns")
            != item.get("interrupted_turn_observed_at_monotonic_ns")
        ):
            return None
        for digest_field in (
            "interrupt_function_arguments_sha256",
            "interrupt_activity_item_sha256",
            "interrupt_output_item_sha256",
        ):
            digest = item.get(digest_field)
            if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
                return None
        for prefix in (
            "interrupt_function",
            "interrupt_activity",
            "interrupt_output",
            "interrupted_turn",
        ):
            wall_ns = item.get(f"{prefix}_observed_at_unix_ns")
            mono_ns = item.get(f"{prefix}_observed_at_monotonic_ns")
            if (
                isinstance(wall_ns, bool)
                or not isinstance(wall_ns, int)
                or isinstance(mono_ns, bool)
                or not isinstance(mono_ns, int)
                or wall_ns + APP_SERVER_EVENT_TIME_RESOLUTION_NS
                > call["commit_unix_ns"]
            ):
                return None
        discarded_evidence.append(dict(item))

    superseded_by_id = {
        str(call["response_id"]): call for call in superseded_calls
    }
    for origin in superseded_calls:
        seen: set[str] = set()
        cursor: Mapping[str, Any] = origin
        while cursor["appserver_delivery"]["kind"] in (
            "superseded_by_collaboration_message",
            "suppressed_collaboration_wait",
        ):
            cursor_id = str(cursor["response_id"])
            if cursor_id in seen:
                return None
            seen.add(cursor_id)
            successor_id = cursor["appserver_delivery"].get(
                "successor_response_id"
            )
            cursor = by_response.get(str(successor_id))  # type: ignore[assignment]
            if not isinstance(cursor, Mapping):
                return None
        if cursor["appserver_delivery"].get("kind") != "direct_raw_response":
            return None

    def usage_sum(selected: Iterable[Mapping[str, Any]]) -> dict[str, int]:
        result = {field: 0 for field in ledger._SUM_FIELDS}
        for selected_call in selected:
            usage = selected_call["normalized_usage"]
            for field in ledger._SUM_FIELDS:
                result[field] += int(usage[field])
        return result

    provider_usage = usage_sum(provider_calls)
    appserver_usage = dict(ledger.aggregate)
    suppressed_usage = usage_sum(suppressed_calls)
    superseded_usage = usage_sum(superseded_calls)
    discarded_usage = usage_sum(discarded_calls)
    if (
        state.get("completed_tokens") != provider_usage["total_tokens"]
        or any(
            provider_usage[field]
            != appserver_usage[field]
            + suppressed_usage[field]
            + superseded_usage[field]
            + discarded_usage[field]
            for field in ledger._SUM_FIELDS
        )
    ):
        return None
    reconciliation = {
        "schema_version": PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION,
        "provider_response_count": len(provider_calls),
        "appserver_response_count": len(ledger.responses),
        "suppressed_collaboration_wait_response_count": len(suppressed_calls),
        "provider_usage": provider_usage,
        "appserver_usage": appserver_usage,
        "suppressed_collaboration_wait_usage": suppressed_usage,
        "provider_response_ids": [str(call["response_id"]) for call in provider_calls],
        "appserver_response_ids": ledger.ordered_response_ids(),
        "suppressed_collaboration_wait_response_ids": [
            str(call["response_id"]) for call in suppressed_calls
        ],
        "suppressed_collaboration_wait_evidence": evidence,
        "superseded_by_collaboration_message_response_count": len(
            superseded_calls
        ),
        "superseded_by_collaboration_message_usage": superseded_usage,
        "superseded_by_collaboration_message_response_ids": [
            str(call["response_id"]) for call in superseded_calls
        ],
        "superseded_by_collaboration_message_evidence": superseded_evidence,
        "discarded_after_explicit_child_interrupt_response_count": len(
            discarded_calls
        ),
        "discarded_after_explicit_child_interrupt_usage": discarded_usage,
        "discarded_after_explicit_child_interrupt_response_ids": [
            str(call["response_id"]) for call in discarded_calls
        ],
        "discarded_after_explicit_child_interrupt_evidence": discarded_evidence,
    }
    if set(reconciliation) != set(PROVIDER_USAGE_RECONCILIATION_KEYS):
        return None
    crossing = state.get("crossing")
    if close_reason == PROVIDER_GATE_CLOSE_TOKEN_LIMIT:
        if not bool(
            state.get("crossing_closed") is True
            and isinstance(crossing, Mapping)
            and ledger.first_crossing is not None
            and crossing.get("response_id")
            == ledger.first_crossing.get("response_id")
            and crossing.get("completed_tokens")
            == ledger.first_crossing.get("tokens")
        ):
            return None
    elif crossing is not None or ledger.first_crossing is not None:
        return None
    return reconciliation


def _finalize_provider_gate_for_ledger(
    gate: ProviderTokenGate,
    ledger: AttemptUsageLedger,
    artifact_path: Path,
    *,
    close_reason: str,
    drain_complete: bool,
) -> dict[str, Any]:
    """Close, seal, validate, and attach one authoritative gate record."""

    _wait_for_explicit_child_interrupt_reconciliation(gate, ledger)

    if close_reason != PROVIDER_GATE_CLOSE_TOKEN_LIMIT:
        close_result = gate.close(close_reason)
        if (
            close_result.get("effective_reason") != close_reason
            or close_result.get("phase") != "CLOSED"
        ):
            raise RuntimeError("provider-token gate did not close at the requested boundary")
    pre_stop = _provider_gate_state_view(gate.snapshot())
    if pre_stop.get("close_reason") != close_reason:
        raise RuntimeError("provider-token gate closed for the wrong reason")
    gate.stop()
    record = gate.finalize()
    verified = validate_provider_gate_artifact(artifact_path)
    if dict(verified) != dict(record):
        raise RuntimeError("provider-token gate finalize/validation mismatch")
    terminal = gate.snapshot()
    reconciliation = _provider_gate_matches_ledger(
        verified,
        terminal,
        ledger,
        close_reason=close_reason,
    )
    if reconciliation is None:
        raise RuntimeError("provider-token gate delivery is not exactly reconciled")
    ledger.attach_provider_gate_final(
        verified,
        terminal,
        exact_for_usage=True,
        provider_usage_reconciliation=reconciliation,
    )
    ledger.publish(drain_complete=drain_complete)
    return dict(verified)


def _wait_for_explicit_child_interrupt_reconciliation(
    gate: ProviderTokenGate,
    ledger: AttemptUsageLedger,
) -> bool:
    """Use the bounded cleanup envelope for one in-flight interrupt discard.

    ``False`` means the lifecycle remained unresolved.  The caller deliberately
    proceeds to the ordinary gate close, whose incomplete-delivery checks poison
    and reject it; this helper never converts cleanup expiry into acceptance.
    """

    if ledger.has_unreconciled_explicit_child_interrupt_lifecycle():
        deadline = (
            time.monotonic()
            + EXPLICIT_CHILD_INTERRUPT_RECONCILIATION_GRACE_SECONDS
        )
        while True:
            ledger.reconcile_discarded_after_explicit_child_interrupts()
            if not ledger.has_unreconciled_explicit_child_interrupt_lifecycle():
                return True
            state = _provider_gate_state_view(gate.snapshot())
            if state.get("active_handler_count") == 0 or time.monotonic() >= deadline:
                return False
            time.sleep(EXPLICIT_CHILD_INTERRUPT_RECONCILIATION_POLL_SECONDS)
    return True


def _drive_provider_gate_compaction_canary(
    protocol_input: TextIO,
    protocol_reader: _ProtocolReader,
    ledger: AttemptUsageLedger,
    provider_gate: ProviderTokenGate,
    *,
    thread_id: str,
    token_limit: int,
    on_notification: Callable[[dict[str, Any]], None],
) -> None:
    """Drive the one explicit compact turn required by the live gate canary."""

    if ledger.root_terminal_status() != "completed":
        raise RuntimeError(
            "provider-token gate canary root did not complete before compaction"
        )
    pre_compaction_gate = _provider_gate_state_view(provider_gate.snapshot())
    completed_tokens = pre_compaction_gate.get("completed_tokens")
    if (
        pre_compaction_gate.get("phase") != PHASE_EXCLUSIVE
        or pre_compaction_gate.get("close_reason") is not None
        or not isinstance(completed_tokens, int)
        or isinstance(completed_tokens, bool)
        or not 0 < completed_tokens < token_limit
    ):
        raise RuntimeError(
            "provider-token gate canary did not reach the exact pre-compaction state"
        )
    ledger.authorize_provider_gate_compaction_canary()
    _write_protocol_message(
        protocol_input,
        {
            "id": THREAD_COMPACT_REQUEST_ID,
            "method": "thread/compact/start",
            "params": {"threadId": thread_id},
        },
    )
    compact_deadline = (
        time.monotonic() + PROVIDER_GATE_COMPACTION_CANARY_TIMEOUT_SECONDS
    )
    compact_response_observed = False
    while ledger.first_crossing is None:
        remaining = compact_deadline - time.monotonic()
        if remaining <= 0:
            raise RuntimeError(
                "provider-token gate compaction canary did not cross before its "
                "trusted timeout"
            )
        try:
            compact_message = protocol_reader.get(timeout=remaining)
        except queue.Empty as error:
            raise RuntimeError(
                "provider-token gate compaction canary did not cross before its "
                "trusted timeout"
            ) from error
        if (
            compact_message.get("id") == THREAD_COMPACT_REQUEST_ID
            and "method" not in compact_message
        ):
            _response_result(
                compact_message,
                THREAD_COMPACT_REQUEST_ID,
                "thread/compact/start",
            )
            compact_response_observed = True
            continue
        on_notification(compact_message)
        if provider_gate.snapshot().get("phase") == PHASE_POISONED:
            raise RuntimeError("provider-token gate compaction canary poisoned")
    if not compact_response_observed:
        raise RuntimeError(
            "provider-token gate compaction crossed before its app-server request "
            "was acknowledged"
        )
    compact_crossing = provider_gate.snapshot().get("crossing")
    if (
        not isinstance(compact_crossing, Mapping)
        or compact_crossing.get("request_kind") != "compaction"
        or compact_crossing.get("release_kind")
        != RELEASE_SANITIZED_COMPACTION_CROSSING
        or compact_crossing.get("response_id")
        != ledger.first_crossing.get("response_id")
    ):
        raise RuntimeError(
            "provider-token gate canary crossing was not an exact sanitized "
            "compaction"
        )


def run(args: argparse.Namespace) -> int:
    workspace = args.workspace.resolve()
    compaction_canary = bool(
        getattr(args, "provider_token_gate_compaction_canary", False)
    )
    if not workspace.is_dir():
        raise RuntimeError(f"workspace is not a directory: {workspace}")
    if args.token_limit <= 0:
        raise RuntimeError("token limit must be positive")
    if not args.usage_output.is_absolute():
        raise RuntimeError("usage output path must be absolute")
    usage_output = args.usage_output.resolve()
    try:
        usage_output.relative_to(workspace)
    except ValueError:
        pass
    else:
        raise RuntimeError(
            "usage output must be outside the model-writable workspace"
        )
    marker_raw = os.environ.get(NETWORK_VIOLATION_MARKER_ENV)
    if not marker_raw:
        raise RuntimeError(
            f"runner did not supply {NETWORK_VIOLATION_MARKER_ENV}"
        )
    marker_input = Path(marker_raw)
    if not marker_input.is_absolute():
        raise RuntimeError("network-violation marker path must be absolute")
    args.network_violation_marker = _below(workspace, marker_input)
    condition_prompt_file = validated_condition_prompt(
        args.condition,
        getattr(args, "condition_prompt_file", None),
        getattr(args, "condition_prompt_sha256", None),
    )
    prompt = build_prompt(
        args.prompt_file,
        args.context_file,
        args.target_file,
        condition_prompt_file,
    )
    prompt_handshake = PromptReleaseHandshake(
        args=args,
        workspace=workspace,
        usage_output=usage_output,
        prompt=prompt,
    )
    gate_paths: dict[str, Path] | None = None
    if compaction_canary and args.reasoning_effort != ULTRA_REASONING_EFFORT:
        raise RuntimeError(
            "the provider-token gate compaction canary requires Ultra"
        )
    if args.reasoning_effort == ULTRA_REASONING_EFFORT:
        gate_paths = _validated_provider_gate_paths(args, workspace, usage_output)
        if getattr(args, "provider_response_bound", None) != PROVIDER_RESPONSE_TOKEN_BOUND:
            raise RuntimeError(
                "--provider-response-bound must equal the frozen model response bound"
            )
        if compaction_canary and not args.token_limit < PROVIDER_RESPONSE_TOKEN_BOUND:
            raise RuntimeError(
                "the provider-token gate compaction canary requires token limit "
                "below the frozen response bound"
            )
        for label in ("model_catalog_sha256", "model_entry_sha256"):
            digest = getattr(args, label, None)
            if not isinstance(digest, str) or re.fullmatch(r"[0-9a-f]{64}", digest) is None:
                raise RuntimeError(
                    f"--{label.replace('_', '-')} must be a lowercase SHA-256 digest"
                )

    state_parent = args.state_parent.resolve()
    state_parent.mkdir(parents=True, exist_ok=True)
    state_root = Path(tempfile.mkdtemp(prefix="highambench-codex-", dir=state_parent))
    state_home = state_root / "home"
    codex_state = state_home / ".codex"
    codex_state.mkdir(parents=True)
    temporary_auth = codex_state / "auth.json"
    process: subprocess.Popen[str] | None = None
    provider_gate: ProviderTokenGate | None = None
    ultra_ledger: AttemptUsageLedger | None = None
    provider_gate_finalized = False
    provider_gate_close_reason: str | None = None
    provider_gate_drain_complete = False
    try:
        shutil.copyfile(args.auth_file, temporary_auth)
        temporary_auth.chmod(0o600)
        if gate_paths is not None:
            gate_candidate = ProviderTokenGate(
                gate_paths["live"],
                gate_paths["final"],
                token_limit=args.token_limit,
                response_bound=args.provider_response_bound,
                model_catalog_sha256=args.model_catalog_sha256,
                model_entry_sha256=args.model_entry_sha256,
            )
            args.provider_gate_base_url = gate_candidate.start()
            provider_gate = gate_candidate
        command = bubblewrap_command(args, state_home)
        process = subprocess.Popen(
            command,
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            text=True,
            bufsize=1,
            env=_sanitized_environment(),
            start_new_session=True,
        )
        assert process.stdin is not None and process.stdout is not None
        observed_thread_id: str | None = None

        def startup_notification(message: dict[str, Any]) -> None:
            nonlocal observed_thread_id
            if message.get("method") != "thread/started":
                return
            params = message.get("params")
            if isinstance(params, Mapping) and isinstance(params.get("thread"), Mapping):
                candidate = params["thread"].get("id")
                if isinstance(candidate, str) and candidate:
                    observed_thread_id = candidate
            # This notification proves thread creation, but turn/start has not
            # yet been sent, so credential removal is race-free.
            temporary_auth.unlink(missing_ok=True)

        initialize_result = _request(
            process.stdin,
            process.stdout,
            request_id=INITIALIZE_REQUEST_ID,
            method="initialize",
            params={
                "clientInfo": {
                    "name": APP_SERVER_CLIENT_NAME,
                    "version": APP_SERVER_CLIENT_VERSION,
                },
                "capabilities": {
                    "experimentalApi": (
                        args.reasoning_effort == ULTRA_REASONING_EFFORT
                    )
                },
            },
            on_notification=lambda _message: None,
        )
        if not isinstance(initialize_result, Mapping):
            raise RuntimeError("Codex app-server returned malformed initialize result")
        _write_protocol_message(process.stdin, {"method": "initialized"})

        thread_start_params: dict[str, Any] = {
            "approvalPolicy": "never",
            "cwd": "/workspace",
            # MultiAgentV2 in the frozen Codex 0.146 runtime cannot resolve an
            # ephemeral coordinator from its collaboration thread registry.
            # Materialize the root only inside this attempt's unique temporary
            # state directory; on normal adapter exit the finally block removes
            # that directory, and no state directory is ever reused or mounted
            # by another attempt.
            "ephemeral": False,
            "model": args.model,
            "sandbox": "danger-full-access",
        }
        if args.reasoning_effort == ULTRA_REASONING_EFFORT:
            thread_start_params["config"] = {
                ULTRA_FORK_POLICY_TRUST_BYPASS_CONFIG_KEY: True,
            }
            thread_start_params["experimentalRawEvents"] = True
            thread_start_params["historyMode"] = "legacy"
            thread_start_params["dynamicTools"] = [
                SubmissionBarrier.dynamic_tool_spec()
            ]
        thread_result = _request(
            process.stdin,
            process.stdout,
            request_id=THREAD_START_REQUEST_ID,
            method="thread/start",
            params=thread_start_params,
            on_notification=startup_notification,
        )
        thread_id = _thread_id_from_result(thread_result, "thread/start")
        _require_materialized_thread(thread_result)
        if observed_thread_id is not None and observed_thread_id != thread_id:
            raise RuntimeError("Codex app-server thread/start notification/result mismatch")

        # A response is also authoritative proof of thread creation.  This
        # unlink is deliberately completed before the turn request is written.
        temporary_auth.unlink(missing_ok=True)
        if temporary_auth.exists():
            raise RuntimeError("could not remove temporary Codex authentication")

        if args.reasoning_effort == ULTRA_REASONING_EFFORT:
            if not isinstance(thread_result, Mapping) or not isinstance(
                thread_result.get("thread"), Mapping
            ):
                raise RuntimeError("Codex app-server omitted the Ultra thread record")
            if thread_result.get("model") != args.model:
                raise RuntimeError("Codex app-server started the wrong Ultra model")
            if thread_result.get("reasoningEffort") != ULTRA_REASONING_EFFORT:
                raise RuntimeError("Codex app-server did not attest Ultra reasoning")
            if provider_gate is None:
                raise RuntimeError("Ultra provider-token gate was not started")
            provider_gate.bind_root(
                thread_id,
                run_id=args.prompt_run_id,
                model=args.model,
                reasoning_effort=args.reasoning_effort,
            )

        prompt_handshake.publish_ready(thread_id)
        prompt_handshake.wait_for_go()
        turn_start_message = prompt_turn_start_request(
            prompt=prompt,
            root_thread_id=thread_id,
            model=args.model,
            reasoning_effort=args.reasoning_effort,
        )

        if args.reasoning_effort == ULTRA_REASONING_EFFORT:
            assert provider_gate is not None and gate_paths is not None
            ledger = AttemptUsageLedger(
                usage_output,
                args.token_limit,
                thread_id,
                fork_policy=ultra_fork_policy_static_record(args.inside_home),
                provider_gate=provider_gate,
                provider_gate_artifact_path=gate_paths["final"],
            )
            ultra_ledger = ledger
            protocol_reader = _ProtocolReader(process.stdout)
            barrier = SubmissionBarrier(
                workspace=workspace,
                usage_output=usage_output,
                ledger=ledger,
                protocol_input=process.stdin,
                protocol_reader=protocol_reader,
                provider_gate=provider_gate,
            )

            def ultra_notification(message: dict[str, Any]) -> None:
                if barrier.capture(message):
                    # A dynamic request can race ahead of its raw-response usage.
                    # Never wait for the runner here unless the matching raw event
                    # was already persisted and all barrier checks now pass.
                    barrier.advance()
                    return
                if ledger.observe_interrupt_response(message):
                    return
                crossing_now = ledger.observe(message)
                if crossing_now:
                    # The gate committed this fully buffered response while it
                    # was the sole upstream request, quarantined every output
                    # item, and closed before exposing the sanitized completion.
                    # No turn/interrupt RPC is needed or permitted.
                    return
                barrier.advance()

            try:
                release_record = prompt_handshake.release_turn_start(
                    process.stdin,
                    turn_start_message,
                )
                provider_gate.bind_prompt_release(release_record)
                turn_result = _await_response_queued(
                    protocol_reader,
                    request_id=TURN_START_REQUEST_ID,
                    method="turn/start",
                    on_notification=ultra_notification,
                )
                turn_id = _turn_id_from_result(turn_result, "turn/start")
                if ledger.root_turn_id not in (None, turn_id):
                    raise RuntimeError(
                        "Codex app-server turn/start notification/result mismatch"
                    )
                ledger.root_turn_id = turn_id
                while ledger.first_crossing is None and not ledger.quiescent():
                    ultra_notification(protocol_reader.get())
                if ledger.first_crossing is not None:
                    if compaction_canary:
                        raise RuntimeError(
                            "provider-token gate canary crossed before explicit compaction"
                        )
                    _finalize_provider_gate_for_ledger(
                        provider_gate,
                        ledger,
                        gate_paths["final"],
                        close_reason=PROVIDER_GATE_CLOSE_TOKEN_LIMIT,
                        drain_complete=False,
                    )
                    provider_gate_finalized = True
                    provider_gate_close_reason = PROVIDER_GATE_CLOSE_TOKEN_LIMIT
                    provider_gate_drain_complete = False
                    return 0
                if compaction_canary:
                    _drive_provider_gate_compaction_canary(
                        process.stdin,
                        protocol_reader,
                        ledger,
                        provider_gate,
                        thread_id=thread_id,
                        token_limit=args.token_limit,
                        on_notification=ultra_notification,
                    )
                    _finalize_provider_gate_for_ledger(
                        provider_gate,
                        ledger,
                        gate_paths["final"],
                        close_reason=PROVIDER_GATE_CLOSE_TOKEN_LIMIT,
                        drain_complete=False,
                    )
                    provider_gate_finalized = True
                    provider_gate_close_reason = PROVIDER_GATE_CLOSE_TOKEN_LIMIT
                    provider_gate_drain_complete = False
                    return 0
                _finalize_provider_gate_for_ledger(
                    provider_gate,
                    ledger,
                    gate_paths["final"],
                    close_reason=PROVIDER_GATE_CLOSE_NATURAL_END,
                    drain_complete=True,
                )
                provider_gate_finalized = True
                provider_gate_close_reason = PROVIDER_GATE_CLOSE_NATURAL_END
                provider_gate_drain_complete = True
                return 0 if ledger.root_terminal_status() == "completed" else 1
            except _SubmissionAccepted:
                # The accepted tool request deliberately remains unresolved.  The
                # finally block kills app-server, so no tool result or inference
                # can occur after the exact first-valid boundary.
                _finalize_provider_gate_for_ledger(
                    provider_gate,
                    ledger,
                    gate_paths["final"],
                    close_reason=PROVIDER_GATE_CLOSE_ACCEPTED_SUBMISSION,
                    drain_complete=False,
                )
                provider_gate_finalized = True
                provider_gate_close_reason = PROVIDER_GATE_CLOSE_ACCEPTED_SUBMISSION
                provider_gate_drain_complete = False
                return 0

        observed_turn_id: str | None = None
        terminal_status: str | None = None
        notification_sequence = 0

        def turn_notification(message: dict[str, Any]) -> None:
            nonlocal observed_turn_id, terminal_status, notification_sequence
            method = message.get("method")
            params = message.get("params")
            if not isinstance(params, Mapping):
                if method in ("turn/started", "turn/completed", "thread/tokenUsage/updated"):
                    raise RuntimeError(f"Codex app-server emitted malformed {method}")
                return
            event_thread_id = params.get("threadId")
            if method in ("turn/started", "turn/completed", "thread/tokenUsage/updated"):
                if event_thread_id != thread_id:
                    raise RuntimeError(f"Codex app-server emitted {method} for another thread")
            if method == "turn/started":
                turn = params.get("turn")
                candidate = turn.get("id") if isinstance(turn, Mapping) else None
                if not isinstance(candidate, str) or not candidate:
                    raise RuntimeError("Codex app-server emitted malformed turn/started")
                if observed_turn_id is not None and observed_turn_id != candidate:
                    raise RuntimeError("Codex app-server emitted inconsistent turn ids")
                observed_turn_id = candidate
                return
            if method == "thread/tokenUsage/updated":
                candidate = params.get("turnId")
                if not isinstance(candidate, str) or not candidate:
                    raise RuntimeError("Codex app-server usage notification has no turn id")
                if observed_turn_id is not None and observed_turn_id != candidate:
                    raise RuntimeError("Codex app-server usage notification has another turn id")
                observed_turn_id = candidate
                usage = normalized_usage(message)
                if usage is None:
                    raise RuntimeError("Codex app-server emitted malformed cumulative token usage")
                notification_sequence += 1
                usage["notification_sequence"] = notification_sequence
                usage["observed_at_unix_ns"] = time.time_ns()
                _write_usage_atomic(usage_output, usage)
                if usage["input_tokens"] + usage["output_tokens"] >= args.token_limit:
                    # Freeze the trusted file at the first crossing.  This closes
                    # the polling race in which a later response could otherwise
                    # overwrite the one-response overshoot evidence before the
                    # outer runner observes it.
                    raise _TokenLimitReached
                return
            if method == "turn/completed":
                turn = params.get("turn")
                candidate = turn.get("id") if isinstance(turn, Mapping) else None
                status = turn.get("status") if isinstance(turn, Mapping) else None
                if not isinstance(candidate, str) or not candidate:
                    raise RuntimeError("Codex app-server emitted malformed turn/completed")
                if observed_turn_id is not None and observed_turn_id != candidate:
                    raise RuntimeError("Codex app-server completed another turn")
                if status not in ("completed", "failed", "interrupted"):
                    raise RuntimeError("Codex app-server emitted invalid terminal turn status")
                observed_turn_id = candidate
                terminal_status = status

        try:
            prompt_handshake.release_turn_start(
                process.stdin,
                turn_start_message,
            )
            turn_result = _await_response(
                process.stdout,
                request_id=TURN_START_REQUEST_ID,
                method="turn/start",
                on_notification=turn_notification,
            )
            turn_id = _turn_id_from_result(turn_result, "turn/start")
            if observed_turn_id is not None and observed_turn_id != turn_id:
                raise RuntimeError("Codex app-server turn/start notification/result mismatch")
            observed_turn_id = turn_id

            while terminal_status is None:
                turn_notification(_read_protocol_message(process.stdout))
            return 0 if terminal_status == "completed" else 1
        except _TokenLimitReached:
            return 0
    finally:
        temporary_auth.unlink(missing_ok=True)
        if (
            provider_gate is not None
            and not provider_gate_finalized
            and gate_paths is not None
            and gate_paths["final"].is_file()
        ):
            recovered_record = validate_provider_gate_artifact(gate_paths["final"])
            recovered_state = provider_gate.snapshot()
            if (
                ultra_ledger is not None
                and ultra_ledger.provider_gate_final is None
            ):
                ultra_ledger.attach_provider_gate_final(
                    recovered_record,
                    recovered_state,
                    exact_for_usage=False,
                )
            recovered_reason = recovered_state.get("close_reason")
            if isinstance(recovered_reason, str):
                provider_gate_close_reason = recovered_reason
            provider_gate_finalized = True
        if provider_gate is not None and not provider_gate_finalized:
            close_result = provider_gate.close(PROVIDER_GATE_CLOSE_SYSTEM_ERROR)
            effective_reason = close_result.get("effective_reason")
            provider_gate_close_reason = (
                effective_reason if isinstance(effective_reason, str) else None
            )
            provider_gate.stop()
            failure_record = provider_gate.finalize()
            if gate_paths is None:
                raise RuntimeError("provider-token gate paths disappeared during cleanup")
            verified_failure = validate_provider_gate_artifact(gate_paths["final"])
            if dict(failure_record) != dict(verified_failure):
                raise RuntimeError("provider-token gate failure artifact mismatch")
            if (
                ultra_ledger is not None
                and ultra_ledger.provider_gate_final is None
            ):
                ultra_ledger.attach_provider_gate_final(
                    verified_failure,
                    provider_gate.snapshot(),
                    exact_for_usage=False,
                )
            provider_gate_finalized = True
        teardown: dict[str, Any] | None = None
        if process is not None:
            teardown = _stop_child(
                process,
                process_group=True,
                immediate=(
                    provider_gate is not None
                    and provider_gate_close_reason
                    != PROVIDER_GATE_CLOSE_NATURAL_END
                ),
            )
        if ultra_ledger is not None and ultra_ledger.provider_gate_final is not None:
            if teardown is None:
                raise RuntimeError("Ultra adapter has no process teardown evidence")
            ultra_ledger.attach_adapter_teardown(teardown)
            ultra_ledger.publish(drain_complete=provider_gate_drain_complete)
        _remove_state_root(state_root)


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--condition", required=True, choices=("N", "L"))
    parser.add_argument("--workspace", required=True, type=Path)
    parser.add_argument("--controlled-relative", default="task")
    parser.add_argument("--shared-root-relative", default="task/shared")
    parser.add_argument("--prompt-file", required=True, type=Path)
    parser.add_argument("--condition-prompt-file", type=Path)
    parser.add_argument("--condition-prompt-sha256")
    parser.add_argument("--context-file", required=True, type=Path)
    parser.add_argument("--target-file", required=True, type=Path)
    parser.add_argument("--usage-output", required=True, type=Path)
    parser.add_argument("--provider-gate-live-output", type=Path)
    parser.add_argument("--provider-gate-output", type=Path)
    parser.add_argument("--model-catalog-sha256")
    parser.add_argument("--model-entry-sha256")
    parser.add_argument("--provider-response-bound", type=positive_int)
    parser.add_argument(
        "--provider-token-gate-compaction-canary",
        action="store_true",
        help=(
            "after one below-cap Ultra turn, request remote compaction and require "
            "that exact response to be the sanitized token-gate crossing"
        ),
    )
    parser.add_argument("--prompt-ready-output", required=True, type=Path)
    parser.add_argument("--prompt-go-input", required=True, type=Path)
    parser.add_argument("--prompt-release-output", required=True, type=Path)
    parser.add_argument("--prompt-handshake-nonce", required=True)
    parser.add_argument("--prompt-run-id", required=True)
    parser.add_argument("--codex", required=True, type=Path)
    parser.add_argument("--auth-file", required=True, type=Path)
    parser.add_argument("--offline-shell", required=True, type=Path)
    parser.add_argument("--toolchain-root", required=True, type=Path)
    parser.add_argument("--packages-root", required=True, type=Path)
    parser.add_argument("--shared-olean-root", type=Path)
    parser.add_argument("--library-source", type=Path)
    parser.add_argument("--library-root-file", type=Path)
    parser.add_argument("--library-olean", type=Path)
    parser.add_argument("--bwrap", type=Path, default=Path("/bin/bwrap"))
    parser.add_argument(
        "--resolver-root", type=Path, default=Path("/run/systemd/resolve")
    )
    parser.add_argument("--inside-home", default="/u501/m2fetrat")
    parser.add_argument("--state-parent", type=Path, default=Path("/tmp"))
    parser.add_argument("--model", default="gpt-5.6-sol")
    parser.add_argument("--reasoning-effort", default="ultra")
    parser.add_argument("--token-limit", type=positive_int, required=True)
    parser.add_argument(
        "--advisory-rollout-budget-limit",
        type=positive_int,
        help=(
            "advisory provider rollout_budget limit; defaults to --token-limit, "
            "but does not change live notification enforcement"
        ),
    )
    return parser


def main() -> int:
    try:
        return run(make_parser().parse_args())
    except (OSError, RuntimeError, ValueError) as error:
        print(f"isolated Codex adapter error: {error}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
