from __future__ import annotations

"""One paid, off-benchmark qualification turn for each frozen provider surface.

The qualification has its own namespace, never creates a pair or task index,
and is deliberately one-shot for a release manifest. An interrupted or failed
qualification is evidence, not permission to silently retry paid inference.
"""

import json
from pathlib import Path
import re
import secrets
from typing import Any, Mapping

from codex_driver import CodexDriver, TurnResult, command_cgroup_snapshot
from common import (
    BenchmarkError,
    assert_no_credentials_in_bytes,
    assert_no_credentials_in_tree,
    canonical_json_bytes,
    load_json,
    sha256_bytes,
    sha256_file,
    tree_manifest,
    utc_now,
    write_bytes_atomic,
    write_json_atomic,
)
from deployment import Deployment
from hardware import snapshot_hardware, verify_frozen_hardware_identity
from manifest_control import MANIFEST_PATH, verify_manifest


SCHEMA = "formalization-provider-qualification-3"
ROOT = Path(__file__).resolve().parents[1]
AUDIT_SCHEMAS = ROOT / "audit" / "schemas"
INPUT_NAME = "qualification_input.json"
OUTPUT_NAME = "qualification_result.json"
PROMPT = (
    "This is an off-benchmark interface check, not a benchmark task. "
    f"Use a workspace file-reading tool to read the entire {INPUT_NAME} file, "
    "including its probe_marker. Compute weighted_sum as the sum of cubes "
    "of odd_values minus the sum of cubes of even_values, and reverse "
    "uppercase_text character by character. "
    "Return only a JSON object with integer weighted_sum and string reversed_text."
)
CODE_MODE = re.compile(rb"\bcode[\s_-]*mode\b", re.IGNORECASE)
WARNING = re.compile(
    rb"\b(?:warn(?:ing)?|fail(?:ed|ure)?|error|unavailable|unable|missing|"
    rb"disabled|cannot|could\s+not|not\s+(?:found|started|initialized))\b",
    re.IGNORECASE,
)
TOOL_FAILURE = re.compile(
    rb"\b(?:tool execution failed|tool call failed|script error|"
    rb"error running tool|failed to execute tool)\b",
    re.IGNORECASE,
)
EXPECTED_OUTPUT = {"weighted_sum": 207, "reversed_text": "LACIREMUN"}
OUTPUT_SCHEMA = {
    "type": "object",
    "additionalProperties": False,
    "required": ["weighted_sum", "reversed_text"],
    "properties": {
        "weighted_sum": {"type": "integer"},
        "reversed_text": {"type": "string"},
    },
}
SYNTHETIC_SEMANTIC_SHA256 = "0" * 64
SYNTHETIC_PAPER_SHA256 = "1" * 64
AUDIT_SCHEMA_PROBES = (
    (
        "blind-translation",
        "blind_translation.schema.json",
        {
            "role": "blind-translation",
            "semantic_sha256": SYNTHETIC_SEMANTIC_SHA256,
            "translation": "Synthetic identity statement: each natural number equals itself.",
            "ambiguities": [],
            "vacuity_risks": [],
        },
    ),
    (
        "direct-judge",
        "judgment.schema.json",
        {
            "role": "direct-judge",
            "paper_sha256": SYNTHETIC_PAPER_SHA256,
            "candidate_semantic_sha256": SYNTHETIC_SEMANTIC_SHA256,
            "verdict": "faithful",
            "mismatches": [],
            "uncertainties": [],
            "rationale": "Synthetic interface check only.",
        },
    ),
    (
        "roundtrip-judge",
        "judgment.schema.json",
        {
            "role": "roundtrip-judge",
            "paper_sha256": SYNTHETIC_PAPER_SHA256,
            "candidate_semantic_sha256": SYNTHETIC_SEMANTIC_SHA256,
            "verdict": "faithful",
            "mismatches": [],
            "uncertainties": [],
            "rationale": "Synthetic interface check only.",
        },
    ),
    (
        "adjudicator",
        "adjudication.schema.json",
        {
            "role": "adjudicator",
            "paper_sha256": SYNTHETIC_PAPER_SHA256,
            "candidate_semantic_sha256": SYNTHETIC_SEMANTIC_SHA256,
            "verdict": "faithful",
            "mismatches": [],
            "remaining_uncertainties": [],
            "rationale": "Synthetic interface check only.",
        },
    ),
)
ROLES = (
    (
        "formalizer", "formalizer_model", "formalizer_reasoning_effort",
        True, False, None, EXPECTED_OUTPUT,
    ),
    (
        "auditor", "audit_model", "audit_reasoning_effort",
        False, True, None, EXPECTED_OUTPUT,
    ),
    *(
        (
            f"audit-schema-{audit_role}",
            "audit_model",
            "audit_reasoning_effort",
            False,
            True,
            schema_name,
            expected_output,
        )
        for audit_role, schema_name, expected_output in AUDIT_SCHEMA_PROBES
    ),
)
USAGE_FIELDS = (
    "input_tokens",
    "cached_input_tokens",
    "cache_write_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
    "total_tokens",
)


def _exact_usage(value: Any) -> bool:
    if not isinstance(value, Mapping) or set(value) != set(USAGE_FIELDS):
        return False
    if any(
        not isinstance(value[field], int)
        or isinstance(value[field], bool)
        or value[field] < 0
        for field in USAGE_FIELDS
    ):
        return False
    return (
        value["total_tokens"] > 0
        and value["input_tokens"]
        >= value["cached_input_tokens"] + value["cache_write_input_tokens"]
        and value["output_tokens"] >= value["reasoning_output_tokens"]
        and value["total_tokens"]
        == value["input_tokens"] + value["output_tokens"]
    )


def _check_command_cgroup(value: Any, envelope: Mapping[str, Any]) -> None:
    if (
        not isinstance(value, Mapping)
        or not isinstance(value.get("path"), str)
        or not value["path"]
        or value.get("memory_max") != str(envelope["memory_bytes"])
        or value.get("memory_swap_max") != "0"
        or value.get("pids_max") != str(envelope["tasks_max"])
        or value.get("cpu_weight") != str(envelope["command_cpu_weight"])
    ):
        raise BenchmarkError("provider qualification command cgroup is not admitted")


def _check_turn(
    result: TurnResult,
    turn: Any,
    *,
    expected_output: Mapping[str, Any],
    ephemeral: bool,
    command_envelope: Mapping[str, Any],
) -> None:
    """Require real, complete provider telemetry and the enforced capability gate."""

    if (
        result.exit_code != 0
        or result.timed_out
        or result.failure_kind is not None
        or not result.usage_complete
        or not isinstance(result.thread_id, str)
        or not result.thread_id
        or result.event_count < 1
        or result.active_started_perf_ns is None
        or result.active_ended_perf_ns is None
        or result.active_ended_perf_ns < result.active_started_perf_ns
        or not _exact_usage(result.usage)
    ):
        raise BenchmarkError("provider qualification turn did not complete exactly")
    try:
        output = json.loads(result.final_message)
    except (TypeError, json.JSONDecodeError) as error:
        raise BenchmarkError("provider qualification returned non-JSON output") from error
    if (
        not isinstance(output, dict)
        or output != expected_output
        or (
            "weighted_sum" in expected_output
            and type(output.get("weighted_sum")) is not int
        )
    ):
        raise BenchmarkError("provider qualification returned the wrong checkable output")
    if not isinstance(turn, Mapping):
        raise BenchmarkError("provider qualification turn record is malformed")
    capability = turn.get("capability_attestation")
    command_resources = turn.get("generated_command_cgroup")
    workspace_resources = turn.get("workspace_resource_ceiling")
    if (
        turn.get("schema_version") != 3
        or turn.get("thread_id") != result.thread_id
        or turn.get("persistent_app_server_session") is ephemeral
        or turn.get("terminal_status") != "completed"
        or turn.get("exit_code") != 0
        or turn.get("timed_out") is not False
        or turn.get("failure_kind") is not None
        or turn.get("usage_complete") is not True
        or turn.get("usage") != result.usage
        or turn.get("raw_response_count", 0) < 1
        or turn.get("cumulative_usage_delta_cross_check") != result.usage
        or turn.get("event_count") != result.event_count
        or not isinstance(capability, Mapping)
        or capability.get("passed") is not True
        or turn.get("protocol_error") is not None
        or turn.get("network_violation_attempts") != 0
        or turn.get("event_archive_violated") is not False
        or not isinstance(command_resources, Mapping)
        or command_resources.get("violated") is not False
        or not isinstance(workspace_resources, Mapping)
        or workspace_resources.get("violated") is not False
    ):
        raise BenchmarkError("provider qualification turn evidence failed its capability gate")
    before = command_resources.get("before")
    after = command_resources.get("after")
    _check_command_cgroup(before, command_envelope)
    _check_command_cgroup(after, command_envelope)
    delta = command_resources.get("limit_event_delta")
    if (
        before.get("path") != after.get("path")
        or not isinstance(delta, Mapping)
        or set(delta)
        != {
            "memory_events.max",
            "memory_events.oom",
            "memory_events.oom_kill",
            "pids_events.max",
        }
        or any(type(value) is not int or value != 0 for value in delta.values())
    ):
        raise BenchmarkError("provider qualification command cgroup changed or hit a limit")


def _check_shutdown(root: Path, thread_id: str) -> None:
    shutdown_path = root / "session-close" / "shutdown.json"
    stderr_path = root / "session-close" / "stderr-after-last-turn.log"
    if (
        not shutdown_path.is_file()
        or shutdown_path.is_symlink()
        or not stderr_path.is_file()
        or stderr_path.is_symlink()
    ):
        raise BenchmarkError("provider qualification lacks formalizer shutdown evidence")
    shutdown = load_json(shutdown_path)
    if (
        shutdown.get("thread_id") != thread_id
        or shutdown.get("graceful") is not True
        or shutdown.get("returncode") != 0
        or shutdown.get("forced_signal") is not None
        or shutdown.get("stdout_drained_to_eof") is not True
        or shutdown.get("late_stdout_line_count") != 0
        or shutdown.get("stderr_sha256") != sha256_file(stderr_path)
    ):
        raise BenchmarkError("provider qualification formalizer shutdown was not clean")


def _normalized(value: Any) -> str:
    if not isinstance(value, str):
        return ""
    return "".join(character for character in value.casefold() if character.isalnum())


def _tool_item(item: Mapping[str, Any]) -> bool:
    kind = _normalized(item.get("type"))
    return any(
        token in kind
        for token in (
            "tool", "commandexecution", "filechange", "fileread", "filewrite",
            "functioncall",
        )
    )


def _tool_text(item: Mapping[str, Any], keys: tuple[str, ...]) -> str:
    return " ".join(
        json.dumps(item[key], sort_keys=True, ensure_ascii=False)
        for key in keys
        if key in item
    )


def _has_code_mode_warning(payload: bytes) -> bool:
    return any(
        CODE_MODE.search(line) and WARNING.search(line)
        for line in payload.splitlines()
    )


def _event_has_code_mode_warning(value: Any) -> bool:
    if isinstance(value, str):
        encoded = value.encode("utf-8")
        return bool(CODE_MODE.search(encoded) and WARNING.search(encoded))
    if isinstance(value, Mapping):
        if (
            _normalized(value.get("type")) in {"warning", "error"}
            or _normalized(value.get("method")) in {"warning", "error"}
        ) and any(
            CODE_MODE.search(child.encode("utf-8"))
            for child in value.values()
            if isinstance(child, str)
        ):
            return True
        return any(_event_has_code_mode_warning(child) for child in value.values())
    if isinstance(value, list):
        return any(_event_has_code_mode_warning(child) for child in value)
    return False


def _check_tool_trace(
    role_root: Path,
    turn: Mapping[str, Any],
    *,
    marker: str,
    writable: bool,
) -> dict[str, Any]:
    """Require observable, successful workspace tools, not just a claimed result."""

    turn_root = role_root / "turn"
    events_path = turn_root / "events.jsonl"
    stderr_path = turn_root / "stderr.log"
    if any(
        not path.is_file() or path.is_symlink()
        for path in (events_path, stderr_path)
    ):
        raise BenchmarkError("provider qualification lacks tool trace or stderr evidence")
    if (
        turn.get("events_sha256") != sha256_file(events_path)
        or turn.get("stderr_sha256") != sha256_file(stderr_path)
    ):
        raise BenchmarkError("provider qualification tool trace digest mismatch")
    event_bytes = events_path.read_bytes()
    stderr_bytes = stderr_path.read_bytes()
    if _has_code_mode_warning(stderr_bytes):
        raise BenchmarkError("provider qualification emitted a Code Mode warning")
    if TOOL_FAILURE.search(stderr_bytes):
        raise BenchmarkError("provider qualification tool failed")
    late_stderr = role_root / "session-close" / "stderr-after-last-turn.log"
    if late_stderr.is_symlink():
        raise BenchmarkError("provider qualification has unsafe shutdown stderr evidence")
    if late_stderr.is_file() and _has_code_mode_warning(late_stderr.read_bytes()):
        raise BenchmarkError("provider qualification emitted a Code Mode warning")
    if late_stderr.is_file() and TOOL_FAILURE.search(late_stderr.read_bytes()):
        raise BenchmarkError("provider qualification tool failed")

    events = []
    for line in event_bytes.splitlines():
        try:
            event = json.loads(line)
        except json.JSONDecodeError as error:
            raise BenchmarkError("provider qualification tool trace is malformed") from error
        if not isinstance(event, Mapping):
            raise BenchmarkError("provider qualification tool trace is malformed")
        if _event_has_code_mode_warning(event):
            raise BenchmarkError("provider qualification emitted a Code Mode warning")
        events.append(event)
    if len(events) != turn.get("event_count"):
        raise BenchmarkError("provider qualification tool trace count mismatch")

    completed: list[tuple[str, Mapping[str, Any]]] = []
    outputs: dict[str, str] = {}
    result_call_ids: set[str] = set()
    for event in events:
        method = event.get("method")
        if isinstance(method, str) and (
            method.endswith("/failed") or method.endswith("/error")
        ):
            raise BenchmarkError("provider qualification tool failed")
        params = event.get("params")
        item = params.get("item") if isinstance(params, Mapping) else None
        if not isinstance(item, Mapping) or not _tool_item(item):
            continue
        status = _normalized(item.get("status"))
        exit_code = item.get("exitCode", item.get("exit_code"))
        result = item.get("result")
        output_text = _tool_text(
            item, ("output", "stdout", "aggregatedOutput", "content")
        )
        if (
            status in {"failed", "error", "cancelled", "canceled", "rejected", "denied"}
            or (exit_code is not None and (type(exit_code) is not int or exit_code != 0))
            or item.get("isError") is True
            or item.get("error") not in (None, "", False)
            or (
                isinstance(result, Mapping)
                and (
                    result.get("isError") is True
                    or result.get("error") not in (None, "", False)
                )
            )
            or (
                isinstance(params, Mapping)
                and params.get("error") not in (None, "", False)
            )
            or TOOL_FAILURE.search(output_text.encode("utf-8"))
        ):
            raise BenchmarkError("provider qualification tool failed")
        if method not in ("item/completed", "rawResponseItem/completed"):
            continue
        call_id = item.get("callId", item.get("call_id", item.get("id")))
        if isinstance(call_id, str) and call_id:
            outputs[call_id] = outputs.get(call_id, "") + _tool_text(
                item, ("output", "stdout", "aggregatedOutput", "result", "content")
            )
            if "functioncalloutput" in _normalized(item.get("type")):
                result_call_ids.add(call_id)
        completed.append((method, item))

    request_keys = (
        "command", "cmd", "name", "arguments", "input", "params", "path",
        "filePath", "changes", "patch",
    )
    result_keys = ("output", "stdout", "aggregatedOutput", "result", "content")
    read_items = []
    write_items = []
    for method, item in completed:
        request = _tool_text(item, request_keys)
        call_id = item.get("callId", item.get("call_id", item.get("id")))
        kind = _normalized(item.get("type"))
        response = _tool_text(item, result_keys)
        if isinstance(call_id, str):
            response += outputs.get(call_id, "")
        if INPUT_NAME in request and marker in response:
            read_items.append(item)
        raw_function_request = (
            method == "rawResponseItem/completed"
            and "functioncall" in kind
            and "functioncalloutput" not in kind
        )
        if (
            OUTPUT_NAME in request
            and kind != "functioncalloutput"
            and (not raw_function_request or call_id in result_call_ids)
        ):
            write_items.append(item)
    if not read_items:
        raise BenchmarkError("provider qualification lacks a completed workspace file-read tool")
    if writable and not write_items:
        raise BenchmarkError("provider qualification lacks a completed workspace file-write tool")
    return {
        "read_tool_items": len(read_items),
        "write_tool_items": len(write_items),
        "events_sha256": sha256_file(events_path),
    }


def _check_workspace_probe(
    workspace: Path,
    *,
    input_sha256: str,
    expected_output: Mapping[str, Any],
    writable: bool,
) -> None:
    source = workspace / INPUT_NAME
    output = workspace / OUTPUT_NAME
    if not source.is_file() or source.is_symlink() or sha256_file(source) != input_sha256:
        raise BenchmarkError("provider qualification workspace input changed")
    if not writable:
        if set(workspace.iterdir()) != {source}:
            raise BenchmarkError("provider qualification read-only workspace was written")
        return
    if not output.is_file() or output.is_symlink():
        raise BenchmarkError("provider qualification workspace file-write is missing")
    try:
        written = load_json(output)
    except (BenchmarkError, ValueError) as error:
        raise BenchmarkError("provider qualification workspace file-write is malformed") from error
    if written != expected_output or (
        "weighted_sum" in expected_output and type(written.get("weighted_sum")) is not int
    ):
        raise BenchmarkError("provider qualification workspace file-write has wrong content")


def qualification_identity(
    deployment: Deployment, manifest: Mapping[str, Any], config: Mapping[str, Any]
) -> dict[str, Any]:
    if not deployment.strict_hardware:
        raise BenchmarkError("provider qualification requires a strict-hardware deployment")
    deployment_record = load_json(deployment.path)
    manifest_sha256 = sha256_file(MANIFEST_PATH)
    if (
        deployment_record.get("release_manifest_sha256") != manifest_sha256
        or deployment_record.get("pilot_id") != config.get("pilot_id")
        or deployment_record.get("manifest_payload_sha256")
        != manifest.get("manifest_payload_sha256")
        or deployment_record.get("run_root") != str(deployment.run_root)
        or deployment_record.get("codex_binary_sha256")
        != sha256_file(deployment.codex_binary)
        or deployment_record.get("code_mode_host_sha256")
        != deployment.code_mode_host_sha256
        or manifest.get("pilot_id") != config.get("pilot_id")
    ):
        raise BenchmarkError("provider qualification deployment/release identity mismatch")
    return {
        "pilot_id": config["pilot_id"],
        "manifest_sha256": manifest_sha256,
        "manifest_payload_sha256": manifest["manifest_payload_sha256"],
        "deployment_path": str(deployment.path),
        "deployment_sha256": sha256_file(deployment.path),
        "codex_binary_sha256": sha256_file(deployment.codex_binary),
        "code_mode_host_sha256": deployment.code_mode_host_sha256,
        "roles": {
            role: {
                "model": str(config[model_key]),
                "reasoning_effort": str(config[effort_key]),
                "workspace_writable": writable,
                "ephemeral": ephemeral,
                "output_schema_sha256": (
                    sha256_file(AUDIT_SCHEMAS / schema_name)
                    if schema_name is not None
                    else sha256_bytes(canonical_json_bytes(OUTPUT_SCHEMA))
                ),
            }
            for (
                role, model_key, effort_key, writable, ephemeral, schema_name, _expected
            ) in ROLES
        },
    }


def _sealed_result(root: Path, identity: Mapping[str, Any], auth_file: Path) -> dict[str, Any]:
    record_path = root / "qualification.json"
    if not record_path.is_file() or record_path.is_symlink():
        raise BenchmarkError(f"provider qualification is incomplete: {root}")
    record = load_json(record_path)
    if (
        record.get("schema_version") != SCHEMA
        or record.get("status") != "PASSED"
        or record.get("identity") != identity
        or set(root.iterdir()) != {root / "roles", record_path}
        or record.get("roles_manifest") != tree_manifest(root / "roles")
    ):
        raise BenchmarkError("provider qualification is failed or its sealed evidence changed")
    assert_no_credentials_in_tree(root, auth_file)
    return {
        "status": "PASSED",
        "record_path": str(record_path),
        "record_sha256": sha256_file(record_path),
        "record": record,
    }


def run_provider_capability_canary(
    deployment: Deployment, *, timeout_seconds: float = 180.0
) -> dict[str, Any]:
    """Qualify both frozen models and every auditor response schema before a pair.

    Call under the campaign lock and Titan envelope, after provider-free doctor.
    A sealed result is reused without another provider call. The caller must
    require status PASSED before creating its official pair namespace.
    """

    if timeout_seconds <= 0:
        raise BenchmarkError("provider qualification timeout must be positive")
    manifest, config = verify_manifest()
    identity = qualification_identity(deployment, manifest, config)
    deployment_record = load_json(deployment.path)
    hardware_before = snapshot_hardware(strict=True)
    verify_frozen_hardware_identity(
        hardware_before, deployment_record.get("hardware_identity")
    )
    _check_command_cgroup(
        command_cgroup_snapshot(required=True), config["command_resource_envelope"]
    )
    qualification_parent = deployment.run_root / "qualifications"
    if deployment.run_root.is_symlink() or not deployment.run_root.is_dir():
        raise BenchmarkError("provider qualification run root is unsafe")
    qualification_parent.mkdir(mode=0o700, exist_ok=True)
    if qualification_parent.is_symlink() or not qualification_parent.is_dir():
        raise BenchmarkError("provider qualification namespace is unsafe")
    root = qualification_parent / identity["manifest_sha256"]
    if root.exists() or root.is_symlink():
        if root.is_symlink() or not root.is_dir():
            raise BenchmarkError("provider qualification root is unsafe")
        return _sealed_result(root, identity, deployment.auth_file)

    root.mkdir(mode=0o700)
    roles_root = root / "roles"
    roles_root.mkdir(mode=0o700)
    outcomes: dict[str, Any] = {}
    try:
        for (
            role, model_key, effort_key, writable, ephemeral, schema_name, expected
        ) in ROLES:
            role_root = roles_root / role
            workspace = role_root / "workspace"
            workspace.mkdir(parents=True, mode=0o700)
            marker = "qualification-" + secrets.token_hex(16)
            input_payload: dict[str, Any] = {"probe_marker": marker}
            if schema_name is None:
                input_payload.update({
                    "odd_values": [3, 5, 7],
                    "even_values": [2, 4, 6],
                    "uppercase_text": "NUMERICAL",
                })
            else:
                input_payload["expected_output"] = expected
            input_path = workspace / INPUT_NAME
            write_json_atomic(input_path, input_payload, mode=0o400)
            input_sha256 = sha256_file(input_path)
            schema_path = role_root / "output_schema.json"
            if schema_name is None:
                write_json_atomic(schema_path, OUTPUT_SCHEMA, mode=0o400)
                prompt = PROMPT + (
                    f" Use a workspace file-writing tool to create {OUTPUT_NAME} "
                    "containing exactly the same JSON object before returning it."
                    if writable else " Do not write to the workspace."
                )
            else:
                source_schema = AUDIT_SCHEMAS / schema_name
                if not source_schema.is_file() or source_schema.is_symlink():
                    raise BenchmarkError(
                        f"auditor response schema is unsafe: {source_schema}"
                    )
                write_bytes_atomic(schema_path, source_schema.read_bytes(), mode=0o400)
                prompt = (
                    "This is an off-benchmark structured-output interface check, "
                    f"not a paper audit. Use a workspace file-reading tool to read "
                    f"the entire {INPUT_NAME} file, including its probe_marker. "
                    "Copy the expected_output JSON object from that file exactly, "
                    "with no explanatory text. Do not write to the workspace."
                )
            if sha256_file(schema_path) != identity["roles"][role]["output_schema_sha256"]:
                raise BenchmarkError(
                    "provider qualification schema changed after identity freeze"
                )
            driver = CodexDriver(
                codex_binary=deployment.codex_binary,
                model=str(config[model_key]),
                reasoning_effort=str(config[effort_key]),
                state_root=None,
                auth_file=deployment.auth_file,
                bwrap_binary=deployment.bwrap_binary,
                offline_shell=deployment.offline_shell,
                toolchain_root=deployment.toolchain_root,
                packages_root=deployment.packages_root,
                workspace_writable=writable,
                code_mode_host_sha256=deployment.code_mode_host_sha256,
            )
            result: TurnResult | None = None
            try:
                result = driver.run_turn(
                    prompt=prompt,
                    workspace=workspace,
                    artifact_dir=role_root / "turn",
                    timeout_seconds=timeout_seconds,
                    output_schema=schema_path,
                    ephemeral=ephemeral,
                    sandbox="read-only" if ephemeral else "workspace-write",
                )
            finally:
                driver.close(artifact_dir=role_root / "session-close")
            assert result is not None
            turn_path = role_root / "turn" / "turn.json"
            if not turn_path.is_file() or turn_path.is_symlink():
                raise BenchmarkError("provider qualification turn record is missing")
            turn = load_json(turn_path)
            _check_turn(
                result,
                turn,
                expected_output=expected,
                ephemeral=ephemeral,
                command_envelope=config["command_resource_envelope"],
            )
            tool_probe = _check_tool_trace(
                role_root, turn, marker=marker, writable=writable
            )
            _check_workspace_probe(
                workspace,
                input_sha256=input_sha256,
                expected_output=expected,
                writable=writable,
            )
            if not ephemeral:
                _check_shutdown(role_root, result.thread_id)
            outcomes[role] = {
                **identity["roles"][role],
                "thread_id": result.thread_id,
                "usage": result.usage,
                "raw_provider_responses": turn["raw_response_count"],
                "workspace_tool_probe": tool_probe,
                "workspace_input_sha256": input_sha256,
                "workspace_output_sha256": (
                    sha256_file(workspace / OUTPUT_NAME) if writable else None
                ),
                "turn_record_sha256": sha256_file(turn_path),
                "turn_artifacts": tree_manifest(role_root),
            }

        hardware_after = snapshot_hardware(strict=True)
        verify_frozen_hardware_identity(
            hardware_after, deployment_record.get("hardware_identity")
        )
        _check_command_cgroup(
            command_cgroup_snapshot(required=True), config["command_resource_envelope"]
        )
        credential_scan = assert_no_credentials_in_tree(root, deployment.auth_file)
        record = {
            "schema_version": SCHEMA,
            "status": "PASSED",
            "classification": "off_benchmark_provider_qualification",
            "provider_turns": len(ROLES),
            "provider_calls": sum(
                outcome["raw_provider_responses"] for outcome in outcomes.values()
            ),
            "charged_to_contestant": False,
            "created_at_utc": utc_now(),
            "identity": identity,
            "role_outcomes": outcomes,
            "credential_scan": credential_scan,
            "hardware_before": hardware_before,
            "hardware_after": hardware_after,
            "roles_manifest": tree_manifest(roles_root),
        }
        assert_no_credentials_in_bytes(
            [("qualification.json", canonical_json_bytes(record))], deployment.auth_file
        )
        write_json_atomic(root / "qualification.json", record, mode=0o400)
        return _sealed_result(root, identity, deployment.auth_file)
    except BaseException:
        # Preserve the unique root and any paid-turn evidence. A minimal failed
        # record is best-effort; it never authorizes a retry in this release.
        failure_path = root / "qualification.json"
        if not failure_path.exists() and not failure_path.is_symlink():
            failure = {
                "schema_version": SCHEMA,
                "status": "FAILED",
                "classification": "off_benchmark_provider_qualification",
                "charged_to_contestant": False,
                "created_at_utc": utc_now(),
                "identity": identity,
                "completed_roles": sorted(outcomes),
            }
            try:
                assert_no_credentials_in_bytes(
                    [("qualification.json", canonical_json_bytes(failure))],
                    deployment.auth_file,
                )
                write_json_atomic(failure_path, failure, mode=0o400)
            except (BenchmarkError, OSError):
                pass
        raise
