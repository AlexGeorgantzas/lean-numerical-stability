#!/usr/bin/env python3
"""Stage and execute one fresh HighamBench N or L run.

The runner is agent-agnostic.  It can pass a seed and token limit to an agent
adapter, but it cannot make an arbitrary Codex CLI honor either value.  Those
controls are therefore explicit protocol claims in every raw record; runs are
marked unscored when required controls or exact provider token usage are absent.

After validator acceptance, a bounded cleanup grace may drain an adapter's
delayed completed-turn usage event. Acceptance time is recorded before this
grace. The raw record states that a completed-turn token total can include a
small amount of generation after the proof first became valid.
"""

from __future__ import annotations

import argparse
import contextlib
import ctypes
import hashlib
import json
import os
from pathlib import Path
import shutil
import struct
import subprocess
import time
from typing import Any, Mapping, Sequence
import uuid

try:
    from .common import (
        BenchmarkToolError,
        SCHEMA_VERSION,
        append_jsonl,
        command_display,
        copytree_fresh,
        parse_command_json,
        render_command,
        resolve_below,
        sha256_file,
        terminate_process,
        utc_now,
        write_json,
    )
    from .hashes import load_manifest, stage_manifest_files
    from .preflight import DEFAULT_MARKERS, run_preflight
    from .validator import ValidationConfig, validate
except ImportError:  # Direct script execution.
    from common import (  # type: ignore
        BenchmarkToolError,
        SCHEMA_VERSION,
        append_jsonl,
        command_display,
        copytree_fresh,
        parse_command_json,
        render_command,
        resolve_below,
        sha256_file,
        terminate_process,
        utc_now,
        write_json,
    )
    from hashes import load_manifest, stage_manifest_files  # type: ignore
    from preflight import DEFAULT_MARKERS, run_preflight  # type: ignore
    from validator import ValidationConfig, validate  # type: ignore


MAX_USAGE_GRACE_SECONDS = 5.0
NETWORK_VIOLATION_MARKER_ENV = "HIGHAMBENCH_NETWORK_VIOLATION_MARKER"
NETWORK_VIOLATION_MARKER_LIMIT = 4096
IN_MODIFY = 0x00000002
IN_ATTRIB = 0x00000004
IN_DELETE_SELF = 0x00000400
IN_MOVE_SELF = 0x00000800
IN_Q_OVERFLOW = 0x00004000
IN_IGNORED = 0x00008000
INOTIFY_EVENT = struct.Struct("iIII")


class NetworkViolationMonitor:
    """Keep an out-of-band kernel record of marker changes.

    The evaluated process can see the workspace file, but it cannot access this
    runner-owned inotify descriptor inside the separate process namespace.  A
    later truncate, rename, or delete therefore cannot erase the kernel event
    that tells the runner the marker changed.
    """

    def __init__(self, path: Path) -> None:
        library = ctypes.CDLL(None, use_errno=True)
        init = library.inotify_init1
        init.argtypes = [ctypes.c_int]
        init.restype = ctypes.c_int
        add_watch = library.inotify_add_watch
        add_watch.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_uint32]
        add_watch.restype = ctypes.c_int
        descriptor = init(os.O_NONBLOCK | os.O_CLOEXEC)
        if descriptor < 0:
            error = ctypes.get_errno()
            raise BenchmarkToolError(
                f"cannot create trusted network-marker monitor: {os.strerror(error)}"
            )
        mask = IN_MODIFY | IN_ATTRIB | IN_DELETE_SELF | IN_MOVE_SELF
        watch = add_watch(descriptor, os.fsencode(path), mask)
        if watch < 0:
            error = ctypes.get_errno()
            os.close(descriptor)
            raise BenchmarkToolError(
                f"cannot watch trusted network marker: {os.strerror(error)}"
            )
        self.descriptor = descriptor
        self.watch = watch
        self.closed = False

    def read_masks(self) -> list[int]:
        masks: list[int] = []
        while True:
            try:
                payload = os.read(self.descriptor, 65536)
            except BlockingIOError:
                break
            except InterruptedError:
                continue
            except OSError:
                masks.append(IN_Q_OVERFLOW)
                break
            if not payload:
                break
            offset = 0
            while offset + INOTIFY_EVENT.size <= len(payload):
                watch, mask, _cookie, name_length = INOTIFY_EVENT.unpack_from(
                    payload, offset
                )
                offset += INOTIFY_EVENT.size + name_length
                if watch in (self.watch, -1):
                    masks.append(mask)
        return masks

    def close(self) -> None:
        if not self.closed:
            os.close(self.descriptor)
            self.closed = True


def library_declaration_names(value: Any) -> list[str]:
    """Flatten the validator's rich dependency records for the run schema.

    The hidden validator keeps module and graph-distance details in its own log.
    Final benchmark records need only the declaration names required by the
    specification and consumed by ``result_set.py`` and the report builder.
    """

    if not isinstance(value, list):
        return []
    names: set[str] = set()
    for item in value:
        name = item.get("name") if isinstance(item, Mapping) else item
        if isinstance(name, str) and name:
            names.add(name)
    return sorted(names)


def create_network_violation_marker(workspace: Path) -> Path:
    """Create the empty, unpredictable marker used by the offline shell."""

    marker = resolve_below(
        workspace, f".highambench-network-violation-{uuid.uuid4().hex}.marker"
    )
    flags = os.O_WRONLY | os.O_CREAT | os.O_EXCL
    if hasattr(os, "O_NOFOLLOW"):
        flags |= os.O_NOFOLLOW
    descriptor = os.open(marker, flags, 0o600)
    os.close(descriptor)
    return marker


def inspect_network_violation_marker(
    path: Path, monitor: NetworkViolationMonitor
) -> dict[str, Any]:
    """Return a fail-closed audit result for the no-socket marker.

    The launcher appends one ``N`` byte for each denied call, up to a fixed
    bound.  Removing, replacing, or changing the marker is itself treated as a
    rule violation because otherwise an attempted call could be hidden.
    """

    base = {
        "detected": False,
        "event_count": 0,
        "saturated": False,
        "integrity_ok": True,
        "note": "no denied socket-related system call was recorded",
        "saved_marker_log": None,
        "marker_sha256": None,
    }
    masks = monitor.read_masks()
    marker_changed = any(mask & (IN_MODIFY | IN_ATTRIB) for mask in masks)
    marker_removed = any(
        mask & (IN_DELETE_SELF | IN_MOVE_SELF | IN_IGNORED) for mask in masks
    )
    queue_overflow = any(mask & IN_Q_OVERFLOW for mask in masks)
    base["kernel_event_count"] = len(masks)
    if queue_overflow:
        return {
            **base,
            "detected": True,
            "integrity_ok": False,
            "note": "the trusted network-marker event queue overflowed",
        }
    try:
        status = path.lstat()
    except FileNotFoundError:
        return {
            **base,
            "detected": True,
            "integrity_ok": False,
            "note": "the protected network-violation marker was removed",
        }
    except OSError as error:
        return {
            **base,
            "detected": True,
            "integrity_ok": False,
            "note": f"the protected network-violation marker could not be checked: {error}",
        }
    if marker_removed or path.is_symlink() or not path.is_file():
        return {
            **base,
            "detected": True,
            "integrity_ok": False,
            "note": "the protected network-violation marker was replaced",
        }
    if status.st_size > NETWORK_VIOLATION_MARKER_LIMIT:
        return {
            **base,
            "detected": True,
            "event_count": NETWORK_VIOLATION_MARKER_LIMIT,
            "saturated": True,
            "integrity_ok": False,
            "note": "the network-violation marker exceeded its fixed size bound",
        }
    try:
        payload = path.read_bytes()
    except OSError as error:
        return {
            **base,
            "detected": True,
            "integrity_ok": False,
            "note": f"the network-violation marker could not be read: {error}",
        }
    if any(byte != ord("N") for byte in payload):
        return {
            **base,
            "detected": True,
            "event_count": len(payload),
            "integrity_ok": False,
            "note": "the network-violation marker contained unexpected data",
        }
    if payload:
        return {
            **base,
            "detected": True,
            "event_count": len(payload),
            "saturated": len(payload) == NETWORK_VIOLATION_MARKER_LIMIT,
            "note": (
                "the offline shell recorded a denied socket-related system call"
            ),
        }
    if marker_changed:
        return {
            **base,
            "detected": True,
            "integrity_ok": False,
            "note": (
                "the trusted monitor recorded a marker change that was later cleared"
            ),
        }
    return base


def _nonnegative_int(value: Any, field: str) -> int:
    if not isinstance(value, int) or isinstance(value, bool) or value < 0:
        raise BenchmarkToolError(f"usage field {field!r} must be a nonnegative integer")
    return value


def read_token_usage(path: Path | None) -> dict[str, Any] | None:
    """Read normalized provider usage.

    The required meaning of ``input_tokens`` is total input tokens including
    cached input.  ``cached_input_tokens`` is retained for audit and is not
    added a second time.
    """

    if path is None or not path.is_file():
        return None
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise BenchmarkToolError(f"cannot read token usage {path}: {error}") from error
    calls: list[Mapping[str, Any]]
    if isinstance(value, dict) and isinstance(value.get("calls"), list):
        calls = value["calls"]
    elif isinstance(value, dict):
        calls = [value]
    else:
        raise BenchmarkToolError("usage JSON must be an object or contain a calls list")
    input_tokens = 0
    output_tokens = 0
    cached_input_tokens = 0
    for call in calls:
        if not isinstance(call, dict):
            raise BenchmarkToolError("each usage call must be an object")
        input_tokens += _nonnegative_int(call.get("input_tokens"), "input_tokens")
        output_tokens += _nonnegative_int(call.get("output_tokens"), "output_tokens")
        cached_input_tokens += _nonnegative_int(
            call.get("cached_input_tokens", 0), "cached_input_tokens"
        )
    if cached_input_tokens > input_tokens:
        raise BenchmarkToolError(
            "cached_input_tokens cannot exceed input_tokens when input includes cached tokens"
        )
    return {
        "input_tokens": input_tokens,
        "output_tokens": output_tokens,
        "cached_input_tokens": cached_input_tokens,
        "model_tokens": input_tokens + output_tokens,
        "call_count": len(calls),
        "input_includes_cached": True,
    }


def _submission_stamp(path: Path) -> tuple[int, int] | None:
    try:
        stat = path.stat()
    except FileNotFoundError:
        return None
    return stat.st_mtime_ns, stat.st_size


def wait_for_usage_after_acceptance(
    process: subprocess.Popen[Any],
    usage_path: Path | None,
    existing_usage: dict[str, Any] | None,
    *,
    grace_seconds: float,
    poll_seconds: float,
) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    """Briefly drain an agent adapter so it can persist final provider usage.

    The caller records validator acceptance before entering this function. The
    grace therefore changes only process cleanup time, never first-valid time.
    Codex exposes exact usage in ``turn.completed``, which can arrive just after
    the proof file. If the turn continues after the proof became valid, that
    exact completed-turn total can still exceed tokens used at the acceptance
    instant; the run record states this unavoidable alignment difference.
    """

    started = time.perf_counter()
    details: dict[str, Any] = {
        "configured_seconds": grace_seconds,
        "attempted": False,
        "usage_available_at_acceptance": existing_usage is not None,
        "usage_captured_during_grace": False,
        "process_exited_during_grace": process.poll() is not None,
        "waited_seconds": 0.0,
    }
    if existing_usage is not None or usage_path is None or grace_seconds <= 0:
        return existing_usage, details

    details["attempted"] = True
    deadline = started + grace_seconds
    usage = existing_usage
    while usage is None:
        usage = read_token_usage(usage_path)
        if usage is not None:
            details["usage_captured_during_grace"] = True
            break
        if process.poll() is not None:
            details["process_exited_during_grace"] = True
            # The adapter writes atomically before exiting. One immediate final
            # read covers the small interval between poll and file visibility.
            usage = read_token_usage(usage_path)
            break
        remaining = deadline - time.perf_counter()
        if remaining <= 0:
            break
        time.sleep(min(poll_seconds, remaining))
    details["waited_seconds"] = round(time.perf_counter() - started, 6)
    return usage, details


def protocol_status(args: argparse.Namespace, *, n_preflight: dict[str, Any] | None) -> dict[str, Any]:
    backend_seed_supplied = args.seed is not None
    claims = {
        "fresh_conversation": args.fresh_conversation,
        "filesystem_isolated": args.filesystem_isolated,
        "network_disabled": args.network_disabled,
        "backend_seed_supplied": backend_seed_supplied,
        "seed_enforced_by_agent": backend_seed_supplied and args.seed_enforced,
        "token_limit_enforced_by_agent": args.token_enforced,
        "condition_l_library_available": args.condition == "N" or args.library_available,
    }
    verified = {
        "fresh_workspace_copy": True,
        "condition_n_preflight": args.condition == "L"
        or bool(n_preflight and n_preflight.get("ok")),
        "condition_n_import_probe_complete": args.condition == "L"
        or bool(n_preflight and n_preflight.get("complete")),
    }
    notes: list[str] = []
    if not backend_seed_supplied:
        notes.append(
            "no backend seed was supplied; the repetition ID is not being presented as a seed"
        )
    elif not args.seed_enforced:
        notes.append(
            "seed is recorded and exported as HIGHAMBENCH_SEED, but this runner cannot "
            "make an arbitrary Codex CLI use it"
        )
    if not args.token_enforced:
        notes.append(
            "token limit is recorded and exported, but enforcement requires an agent/provider adapter"
        )
    if not args.filesystem_isolated:
        notes.append(
            "a copied directory does not prevent access to host paths; use a container or equivalent sandbox"
        )
    if not args.network_disabled:
        notes.append("network isolation is asserted by the caller, not implemented by this process runner")
    complete = all(claims.values()) and all(verified.values())
    return {"complete": complete, "claims": claims, "verified": verified, "notes": notes}


def make_validation_config(
    args: argparse.Namespace,
    workspace: Path,
    compile_command: Sequence[str],
    audit_command: Sequence[str] | None,
    *,
    timeout_seconds: float,
) -> ValidationConfig:
    return ValidationConfig(
        workspace=workspace,
        submission_relative=args.submission_relative,
        canonical_relative=args.canonical_relative,
        target_theorem=args.target_theorem,
        compile_command=compile_command,
        condition=args.condition,
        controlled_manifest=args.controlled_manifest,
        controlled_root_relative=args.task_dest,
        local_source_relatives=args.local_source_relative,
        forbidden_import_prefixes=args.forbidden_import_prefix,
        audit_command=audit_command,
        submission_module=args.submission_module,
        audit_helper=args.audit_helper,
        hidden_parent=args.hidden_parent,
        compile_timeout_seconds=max(0.1, min(args.validation_timeout_seconds, timeout_seconds)),
        audit_timeout_seconds=args.audit_timeout_seconds,
    )


def _base_record(args: argparse.Namespace, run_id: str) -> dict[str, Any]:
    pair_id = args.pair_id or (
        f"{args.agent_id}:{args.agent_version}:{args.model}:{args.task_id}:"
        f"{args.repetition_id}"
    )
    try:
        freeze_check = json.loads(args.freeze_check_json)
    except (AttributeError, json.JSONDecodeError) as error:
        raise BenchmarkToolError(f"invalid frozen-run verification JSON: {error}") from error
    if not isinstance(freeze_check, dict):
        raise BenchmarkToolError("frozen-run verification must be a JSON object")
    if (
        freeze_check.get("schema_version") != SCHEMA_VERSION
        or freeze_check.get("kind") != "highambench-frozen-run-verification"
        or freeze_check.get("ok") is not True
    ):
        raise BenchmarkToolError("frozen-run verification is not a successful supported check")
    if freeze_check.get("environment_id") != args.environment_id:
        raise BenchmarkToolError("frozen-run verification has the wrong environment_id")
    canonical_freeze = json.dumps(
        freeze_check, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    freeze_digest = hashlib.sha256(canonical_freeze).hexdigest()
    return {
        "schema_version": SCHEMA_VERSION,
        "kind": "highambench-run",
        "run_id": run_id,
        "pair_id": pair_id,
        "task_id": args.task_id,
        "paper_id": args.paper_id,
        "paper_sha256": args.paper_sha256,
        "tier": args.tier,
        "condition": args.condition,
        "repetition_id": args.repetition_id,
        "backend_seed": args.seed,
        "pair_order": args.pair_order,
        "order_index": args.order_index,
        "agent": {
            "id": args.agent_id,
            "version": args.agent_version,
            "model": args.model,
            "reasoning_effort": args.reasoning_effort,
        },
        "environment_id": args.environment_id,
        "frozen_run_verification": {
            "freeze_check_sha256": freeze_digest,
            "freeze_check": freeze_check,
        },
        "limits": {
            "time_seconds": args.time_limit_seconds,
            "model_tokens": args.token_limit,
            "post_acceptance_usage_grace_seconds": args.usage_grace_seconds,
        },
    }


def run_one(args: argparse.Namespace) -> dict[str, Any]:
    compile_command = parse_command_json(
        args.compile_command_json, option="--compile-command-json"
    )
    agent_command_template = parse_command_json(
        args.agent_command_json, option="--agent-command-json"
    )
    probe_command = parse_command_json(
        args.n_probe_command_json, option="--n-probe-command-json"
    )
    audit_command = parse_command_json(args.audit_command_json, option="--audit-command-json")
    assert compile_command is not None and agent_command_template is not None
    manifest = load_manifest(args.controlled_manifest)

    run_id = args.run_id or f"{args.task_id}-{args.condition}-{args.seed}-{uuid.uuid4().hex[:12]}"
    record = _base_record(args, run_id)
    workspace_parent = args.workspace_parent.resolve()
    workspace_parent.mkdir(parents=True, exist_ok=True)
    workspace = workspace_parent / f"highambench-run-{uuid.uuid4().hex}"
    logs_dir = args.logs_dir.resolve()
    logs_dir.mkdir(parents=True, exist_ok=True)
    agent_log = logs_dir / f"{run_id}.agent.log"
    validation_log = logs_dir / f"{run_id}.validation.json"
    started_at = utc_now()
    n_preflight: dict[str, Any] | None = None
    validation_result: dict[str, Any] | None = None
    agent_exit_code: int | None = None
    process: subprocess.Popen[Any] | None = None
    agent_system_error: str | None = None
    useful_work_started = False
    timed_out = False
    token_limited = False
    first_valid_seconds: float | None = None
    actual_stop_seconds = 0.0
    usage: dict[str, Any] | None = None
    submission_digest: str | None = None
    final_submission_digest: str | None = None
    accepted_submission_log: Path | None = None
    network_marker: Path | None = None
    network_monitor: NetworkViolationMonitor | None = None
    network_violation: dict[str, Any] = {
        "detected": False,
        "event_count": 0,
        "saturated": False,
        "integrity_ok": True,
        "note": "agent execution did not start",
        "saved_marker_log": None,
        "marker_sha256": None,
    }
    usage_capture: dict[str, Any] = {
        "configured_seconds": args.usage_grace_seconds,
        "attempted": False,
        "usage_available_at_acceptance": False,
        "usage_captured_during_grace": False,
        "process_exited_during_grace": False,
        "waited_seconds": 0.0,
    }

    try:
        copytree_fresh(args.base_workspace, workspace)
        network_marker = create_network_violation_marker(workspace)
        network_monitor = NetworkViolationMonitor(network_marker)
        task_destination = resolve_below(workspace, args.task_dest)
        staged_controlled = stage_manifest_files(args.task_root, task_destination, manifest)
        if args.condition == "N":
            n_preflight = run_preflight(
                workspace,
                markers=args.n_marker or DEFAULT_MARKERS,
                probe_command=probe_command,
                probe_timeout_seconds=args.n_probe_timeout_seconds,
            )
            n_preflight["controlled_task_staging"] = {
                "manifest_sha256": sha256_file(args.controlled_manifest),
                "verified_files": staged_controlled["verified"],
                "expected_files": staged_controlled["expected"],
                "complete": staged_controlled["ok"],
            }
            if not n_preflight["ok"]:
                record.update(
                    {
                        "started_at_utc": started_at,
                        "finished_at_utc": utc_now(),
                        "pass": False,
                        "useful_work_started": False,
                        "failure_code": "SYSTEM_ERROR",
                        "failure_note": "condition N environment failed its isolation preflight",
                        "actual_stop_seconds": 0.0,
                        "scored_elapsed_seconds": args.time_limit_seconds,
                        "token_usage": None,
                        "library_use": False,
                        "library_declarations": [],
                        "network_violation": network_violation,
                        "n_preflight": n_preflight,
                    }
                )
                protocol = protocol_status(args, n_preflight=n_preflight)
                record["protocol"] = protocol
                record["scored"] = False
                return record
        submission = resolve_below(workspace, args.submission_relative)
        if submission.exists():
            raise BenchmarkToolError(
                "submission path exists before prompt release; task package may expose a proof"
            )
        submission.parent.mkdir(parents=True, exist_ok=True)
        usage_path = (
            resolve_below(workspace, args.usage_relative) if args.usage_relative else None
        )
        prompt_file = (
            resolve_below(workspace, args.prompt_relative) if args.prompt_relative else ""
        )
        command_values: dict[str, str | Path | int] = {
            "workspace": workspace,
            "submission": submission,
            "condition": args.condition,
            "seed": "" if args.seed is None else args.seed,
            "prompt_file": prompt_file,
            "time_limit": args.time_limit_seconds,
            "token_limit": args.token_limit,
            "network_violation_marker": network_marker,
        }
        agent_command = render_command(agent_command_template, command_values)
        protocol = protocol_status(args, n_preflight=n_preflight)
        if args.strict_protocol and not protocol["complete"]:
            raise BenchmarkToolError(
                "strict protocol requested but controls are incomplete: "
                + "; ".join(protocol["notes"])
            )

        environment = os.environ.copy()
        environment.update(
            {
                "HIGHAMBENCH_CONDITION": args.condition,
                "HIGHAMBENCH_REPETITION_ID": args.repetition_id,
                "HIGHAMBENCH_SEED": "" if args.seed is None else str(args.seed),
                "HIGHAMBENCH_WORKSPACE": str(workspace),
                "HIGHAMBENCH_SUBMISSION": str(submission),
                "HIGHAMBENCH_TIME_LIMIT": str(args.time_limit_seconds),
                "HIGHAMBENCH_TOKEN_LIMIT": str(args.token_limit),
                NETWORK_VIOLATION_MARKER_ENV: str(network_marker),
            }
        )
        with agent_log.open("w", encoding="utf-8", newline="") as log:
            log.write(f"$ {command_display(agent_command)}\n\n")
            log.flush()
            prompt_released = time.perf_counter()
            try:
                process = subprocess.Popen(
                    agent_command,
                    cwd=workspace,
                    env=environment,
                    stdout=log,
                    stderr=subprocess.STDOUT,
                    text=True,
                    start_new_session=True,
                )
                useful_work_started = True
            except OSError as error:
                process = None
                agent_system_error = str(error)

            last_stamp: tuple[int, int] | None = None
            while process is not None:
                elapsed = time.perf_counter() - prompt_released
                if elapsed >= args.time_limit_seconds:
                    timed_out = True
                    terminate_process(process)
                    break
                try:
                    usage = read_token_usage(usage_path)
                except BenchmarkToolError as error:
                    agent_system_error = str(error)
                    terminate_process(process)
                    break
                if (
                    args.token_enforced
                    and usage is not None
                    and usage["model_tokens"] >= args.token_limit
                ):
                    token_limited = True
                    terminate_process(process)
                    break

                stamp = _submission_stamp(submission)
                if stamp is not None and stamp != last_stamp:
                    last_stamp = stamp
                    remaining = args.time_limit_seconds - elapsed
                    validation_result = validate(
                        make_validation_config(
                            args,
                            workspace,
                            compile_command,
                            audit_command,
                            timeout_seconds=remaining,
                        )
                    )
                    accepted_at = time.perf_counter() - prompt_released
                    if accepted_at >= args.time_limit_seconds:
                        timed_out = True
                        terminate_process(process)
                        break
                    if validation_result.get("pass"):
                        first_valid_seconds = accepted_at
                        accepted_submission_log = logs_dir / f"{run_id}.accepted.lean"
                        shutil.copy2(submission, accepted_submission_log)
                        submission_digest = sha256_file(accepted_submission_log)
                        try:
                            usage, usage_capture = wait_for_usage_after_acceptance(
                                process,
                                usage_path,
                                usage,
                                grace_seconds=args.usage_grace_seconds,
                                poll_seconds=min(args.poll_seconds, 0.05),
                            )
                        except BenchmarkToolError as error:
                            agent_system_error = str(error)
                        terminate_process(process)
                        break
                exit_code = process.poll()
                if exit_code is not None:
                    agent_exit_code = exit_code
                    break
                time.sleep(args.poll_seconds)

            if process is not None and agent_exit_code is None:
                agent_exit_code = process.poll()
                if agent_exit_code is None:
                    with contextlib.suppress(subprocess.TimeoutExpired):
                        agent_exit_code = process.wait(timeout=2.0)
            actual_stop_seconds = time.perf_counter() - prompt_released

        if usage is None:
            usage = read_token_usage(usage_path)
        final_stamp = _submission_stamp(submission)
        if (
            not timed_out
            and not token_limited
            and agent_system_error is None
            and first_valid_seconds is None
            and final_stamp is not None
            and final_stamp != last_stamp
        ):
            remaining = max(0.1, args.time_limit_seconds - actual_stop_seconds)
            validation_result = validate(
                make_validation_config(
                    args,
                    workspace,
                    compile_command,
                    audit_command,
                    timeout_seconds=remaining,
                )
            )
            validated_at = time.perf_counter() - prompt_released
            if validation_result.get("pass"):
                if validated_at >= args.time_limit_seconds:
                    timed_out = True
                else:
                    first_valid_seconds = validated_at
                    accepted_submission_log = logs_dir / f"{run_id}.accepted.lean"
                    shutil.copy2(submission, accepted_submission_log)
                    submission_digest = sha256_file(accepted_submission_log)
            elif validated_at >= args.time_limit_seconds:
                timed_out = True

        if submission.is_file():
            final_submission_digest = sha256_file(submission)
            if submission_digest is None:
                submission_digest = final_submission_digest

        network_violation = inspect_network_violation_marker(
            network_marker, network_monitor
        )
        network_monitor.close()
        network_monitor = None
        if network_violation["detected"] and network_marker.is_file():
            saved_network_marker = logs_dir / f"{run_id}.network-violation.marker"
            shutil.copy2(network_marker, saved_network_marker)
            network_violation["saved_marker_log"] = str(saved_network_marker)
            network_violation["marker_sha256"] = sha256_file(saved_network_marker)

        if timed_out:
            passed = False
            failure_code = "TIME_LIMIT"
            failure_note = "fixed wall-clock limit reached"
        elif token_limited:
            passed = False
            failure_code = "TOKEN_LIMIT"
            failure_note = "reported model-token limit reached before the time limit"
        elif agent_system_error and not submission.is_file() and not useful_work_started:
            passed = False
            failure_code = "SYSTEM_ERROR"
            failure_note = agent_system_error
        elif not submission.is_file():
            passed = False
            failure_code = "NO_SUBMISSION"
            failure_note = "agent ended without a proof file"
        elif network_violation["detected"]:
            passed = False
            failure_code = "RULE_VIOLATION"
            failure_note = network_violation["note"]
        elif agent_system_error:
            passed = False
            failure_code = "SYSTEM_ERROR"
            failure_note = agent_system_error
        elif first_valid_seconds is not None and validation_result and validation_result.get("pass"):
            passed = True
            failure_code = None
            failure_note = ""
        elif validation_result is None:
            passed = False
            failure_code = "SYSTEM_ERROR"
            failure_note = agent_system_error or "submission was not validated"
        else:
            passed = False
            failure_code = validation_result.get("failure_code") or "PROOF_ERROR"
            failure_note = validation_result.get("note", "Lean rejected the submitted proof")

        if validation_result is not None:
            write_json(validation_log, validation_result)
        library_use = False if args.condition == "N" else (
            validation_result.get("library_use") if validation_result else None
        )
        library_declarations = library_declaration_names(
            validation_result.get("library_declarations", []) if validation_result else []
        )
        protocol = protocol_status(args, n_preflight=n_preflight)
        if usage is None:
            protocol["complete"] = False
            protocol["notes"].append(
                "exact provider token usage was not supplied; token measurement is missing"
            )
        elif usage["model_tokens"] > args.token_limit:
            protocol["complete"] = False
            protocol["notes"].append(
                "provider-reported completed-turn usage exceeded the configured token limit"
            )
        if passed and usage is not None:
            protocol["notes"].append(
                "provider usage is exact for the completed Codex turn but may include tokens "
                "after the proof first became valid and before turn.completed"
            )
        if passed and args.condition == "L" and not (
            validation_result and validation_result.get("library_audit_complete")
        ):
            protocol["complete"] = False
            protocol["notes"].append(
                "passed L run lacks a completed transitive library-dependency audit"
            )
        protocol["verified"]["network_violation_marker_integrity"] = network_violation[
            "integrity_ok"
        ]
        if not network_violation["integrity_ok"]:
            protocol["complete"] = False
            protocol["notes"].append(
                "the per-run network-violation marker failed its integrity check"
            )
        scored = protocol["complete"] and (
            failure_code != "SYSTEM_ERROR" or useful_work_started
        )
        record.update(
            {
                "started_at_utc": started_at,
                "finished_at_utc": utc_now(),
                "pass": passed,
                "useful_work_started": useful_work_started,
                "scored": scored,
                "failure_code": failure_code,
                "failure_note": failure_note,
                "actual_stop_seconds": round(actual_stop_seconds, 6),
                "first_valid_seconds": (
                    round(first_valid_seconds, 6) if first_valid_seconds is not None else None
                ),
                "scored_elapsed_seconds": (
                    round(first_valid_seconds, 6)
                    if passed and first_valid_seconds is not None
                    else args.time_limit_seconds
                ),
                "time_measurement": "prompt release to validator acceptance",
                "token_usage": usage,
                "token_measurement": {
                    "source": "normalized provider completed-turn usage",
                    "provider_turn_total_exact": usage is not None,
                    "aligned_exactly_to_first_valid": False if passed and usage is not None else None,
                    "deviation_note": (
                        "Codex emits exact usage only at turn.completed; this total may include "
                        "tokens generated after validator acceptance. The recorded first-valid "
                        "time is captured before the bounded usage grace and is unchanged."
                        if passed
                        else ""
                    ),
                    "capture_grace": usage_capture,
                },
                "library_use": library_use,
                "library_declarations": library_declarations,
                "network_violation": network_violation,
                "failure_precedence": "TIME_LIMIT,TOKEN_LIMIT,NO_SUBMISSION,RULE_VIOLATION,"
                "SYNTAX_OR_ELAB,PROOF_ERROR,SYSTEM_ERROR",
                "submission_sha256": submission_digest,
                "final_submission_sha256": final_submission_digest,
                "accepted_submission_log": (
                    str(accepted_submission_log) if accepted_submission_log else None
                ),
                "submission_changed_after_acceptance": (
                    submission_digest is not None
                    and final_submission_digest is not None
                    and submission_digest != final_submission_digest
                ),
                "agent_exit_code": agent_exit_code,
                "agent_command": agent_command,
                "agent_log": str(agent_log),
                "validation_log": str(validation_log) if validation_result else None,
                "n_preflight": n_preflight,
                "protocol": protocol,
                "workspace_retained": args.keep_workspace,
                "workspace": str(workspace) if args.keep_workspace else None,
            }
        )
        return record
    except (OSError, BenchmarkToolError) as error:
        if process is not None and process.poll() is None:
            terminate_process(process)
        exception_network = (
            inspect_network_violation_marker(network_marker, network_monitor)
            if network_marker is not None and network_monitor is not None
            else network_violation
        )
        exception_protocol = protocol_status(args, n_preflight=n_preflight)
        exception_protocol["verified"]["network_violation_marker_integrity"] = (
            exception_network["integrity_ok"]
        )
        if not exception_network["integrity_ok"]:
            exception_protocol["complete"] = False
            exception_protocol["notes"].append(
                "the per-run network-violation marker failed its integrity check"
            )
        if usage is None:
            exception_protocol["complete"] = False
            exception_protocol["notes"].append(
                "exact provider token usage was not supplied; token measurement is missing"
            )
        elif usage["model_tokens"] > args.token_limit:
            exception_protocol["complete"] = False
            exception_protocol["notes"].append(
                "provider-reported completed-turn usage exceeded the configured token limit"
            )
        record.update(
            {
                "started_at_utc": started_at,
                "finished_at_utc": utc_now(),
                "pass": False,
                "useful_work_started": useful_work_started,
                "scored": useful_work_started and exception_protocol["complete"],
                "failure_code": "SYSTEM_ERROR",
                "failure_note": str(error),
                "actual_stop_seconds": round(actual_stop_seconds, 6),
                "scored_elapsed_seconds": args.time_limit_seconds,
                "token_usage": usage,
                "library_use": False if args.condition == "N" else None,
                "library_declarations": [],
                "network_violation": exception_network,
                "n_preflight": n_preflight,
                "protocol": exception_protocol,
            }
        )
        return record
    finally:
        if process is not None and process.poll() is None:
            terminate_process(process)
        if network_monitor is not None:
            network_monitor.close()
        if workspace.exists() and not args.keep_workspace:
            shutil.rmtree(workspace, ignore_errors=True)


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--condition", choices=("N", "L"), required=True)
    parser.add_argument("--task-id", required=True)
    parser.add_argument("--paper-id", required=True)
    parser.add_argument("--paper-sha256", required=True)
    parser.add_argument("--tier", choices=("T1", "T2", "T3"), required=True)
    parser.add_argument("--repetition-id", required=True)
    parser.add_argument(
        "--seed",
        type=int,
        help="real backend seed, if the backend supports and obeys one",
    )
    parser.add_argument("--pair-id")
    parser.add_argument("--pair-order", choices=("N-first", "L-first"), required=True)
    parser.add_argument("--order-index", type=int, choices=(1, 2), required=True)
    parser.add_argument("--run-id")
    parser.add_argument("--agent-id", required=True)
    parser.add_argument("--agent-version", required=True)
    parser.add_argument("--model", required=True)
    parser.add_argument("--reasoning-effort", required=True)
    parser.add_argument("--environment-id", required=True)
    parser.add_argument("--freeze-check-json", required=True)

    parser.add_argument("--base-workspace", type=Path, required=True)
    parser.add_argument("--task-root", type=Path, required=True)
    parser.add_argument("--controlled-manifest", type=Path, required=True)
    parser.add_argument("--task-dest", default="task")
    parser.add_argument("--workspace-parent", type=Path, required=True)
    parser.add_argument("--logs-dir", type=Path, required=True)
    parser.add_argument("--raw-jsonl", type=Path, required=True)
    parser.add_argument("--keep-workspace", action="store_true")

    parser.add_argument("--submission-relative", required=True)
    parser.add_argument("--canonical-relative", required=True)
    parser.add_argument("--target-theorem", required=True)
    parser.add_argument("--local-source-relative", action="append", default=[])
    parser.add_argument("--forbidden-import-prefix", action="append", default=[])
    parser.add_argument("--submission-module")
    parser.add_argument("--audit-helper", type=Path)
    parser.add_argument("--prompt-relative")
    parser.add_argument("--usage-relative")

    parser.add_argument("--agent-command-json", required=True)
    parser.add_argument("--compile-command-json", required=True)
    parser.add_argument("--audit-command-json")
    parser.add_argument("--n-probe-command-json")
    parser.add_argument("--n-marker", action="append", default=[])
    parser.add_argument("--n-probe-timeout-seconds", type=float, default=60.0)
    parser.add_argument("--hidden-parent", type=Path)
    parser.add_argument("--validation-timeout-seconds", type=float, default=120.0)
    parser.add_argument("--audit-timeout-seconds", type=float, default=120.0)
    parser.add_argument("--poll-seconds", type=float, default=0.25)
    parser.add_argument(
        "--usage-grace-seconds",
        type=float,
        default=2.0,
        help=(
            "bounded post-acceptance drain for a delayed provider usage event; "
            "does not change first-valid time"
        ),
    )

    parser.add_argument("--time-limit-seconds", type=float, required=True)
    parser.add_argument("--token-limit", type=int, required=True)
    parser.add_argument("--fresh-conversation", action="store_true")
    parser.add_argument("--filesystem-isolated", action="store_true")
    parser.add_argument("--network-disabled", action="store_true")
    parser.add_argument("--seed-enforced", action="store_true")
    parser.add_argument("--token-enforced", action="store_true")
    parser.add_argument("--library-available", action="store_true")
    parser.add_argument("--strict-protocol", action="store_true")
    parser.add_argument("--output", type=Path)
    return parser


def _validate_args(args: argparse.Namespace) -> None:
    if args.time_limit_seconds <= 0 or args.validation_timeout_seconds <= 0:
        raise BenchmarkToolError("time limits must be positive")
    if args.token_limit <= 0:
        raise BenchmarkToolError("token limit must be positive")
    if args.poll_seconds <= 0:
        raise BenchmarkToolError("poll interval must be positive")
    if not 0 <= args.usage_grace_seconds <= MAX_USAGE_GRACE_SECONDS:
        raise BenchmarkToolError(
            f"usage grace must be between 0 and {MAX_USAGE_GRACE_SECONDS:g} seconds"
        )
    if len(args.paper_sha256) != 64 or any(
        char not in "0123456789abcdef" for char in args.paper_sha256
    ):
        raise BenchmarkToolError("paper SHA-256 must be 64 lowercase hexadecimal characters")


def main() -> int:
    args = make_parser().parse_args()
    try:
        _validate_args(args)
        record = run_one(args)
    except BenchmarkToolError as error:
        record = {
            "schema_version": SCHEMA_VERSION,
            "kind": "highambench-run",
            "pass": False,
            "useful_work_started": False,
            "scored": False,
            "failure_code": "SYSTEM_ERROR",
            "failure_note": str(error),
        }
    append_jsonl(args.raw_jsonl, record)
    if args.output:
        write_json(args.output, record)
    else:
        print(json.dumps(record, indent=2, sort_keys=True))
    return 0 if record.get("pass") else 1


if __name__ == "__main__":
    raise SystemExit(main())
