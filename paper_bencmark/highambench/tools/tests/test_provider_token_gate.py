from __future__ import annotations

import hashlib
import http.client
import io
import json
import os
from pathlib import Path
import random
import ssl
import stat
import sys
import tempfile
import threading
import time
import unittest
from unittest import mock
from urllib.parse import urlsplit


TOOLS = Path(__file__).resolve().parents[1]
if str(TOOLS) not in sys.path:
    sys.path.insert(0, str(TOOLS))

import provider_token_gate as gate_module  # noqa: E402
from provider_token_gate import (  # noqa: E402
    ADMISSION_MODE_EXCLUSIVE,
    CLOSE_REASON_ACCEPTED_SUBMISSION,
    CLOSE_REASON_NATURAL_END,
    CLOSE_REASON_TOKEN_LIMIT,
    PHASE_CLOSED,
    PHASE_DRAINING,
    PHASE_EXCLUSIVE,
    PHASE_POISONED,
    PROVIDER_GATE_FINAL_SUFFIX,
    PROVIDER_GATE_LIVE_SUFFIX,
    PROVIDER_CONNECTION_FACTORY_EXPLICIT_TLS,
    PROVIDER_CONNECTION_FACTORY_TEST_OVERRIDE,
    PROVIDER_PROXY_MODE,
    PROVIDER_TRANSPORT_ENV_REQUIRED_ABSENT,
    PROVIDER_CERTIFICATE_SOURCE_MODE,
    RELEASE_BYTE_IDENTITY,
    RELEASE_SANITIZED_COMPACTION_CROSSING,
    RELEASE_SANITIZED_CROSSING,
    ProviderGateError,
    ProviderGateValidationError,
    ProviderTokenGate,
    build_transport_provenance,
    provider_gate_artifact_path,
    provider_gate_live_path,
    validate_artifact,
)


MODEL = "gpt-5.6-sol"
EFFORT = "ultra"
ROOT = "root-thread"
RUN = "run-id"
CATALOG_SHA = "a" * 64
ENTRY_SHA = "b" * 64
PROMPT_SHA = "c" * 64


def canonical_record_hash(value: dict[str, object], field: str) -> str:
    unsigned = {key: item for key, item in value.items() if key != field}
    encoded = json.dumps(
        unsigned, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def reseal_provider_gate_record(value: dict[str, object]) -> None:
    unsigned = dict(value)
    unsigned.pop("record_sha256", None)
    value["record_sha256"] = hashlib.sha256(
        (
            json.dumps(
                unsigned,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            )
            + "\n"
        ).encode("utf-8")
    ).hexdigest()


def prompt_release(**changes: object) -> dict[str, object]:
    value: dict[str, object] = {
        "schema_version": 1,
        "protocol_version": "highambench-prompt-release-v1",
        "kind": "highambench_prompt_released",
        "root_thread_id": ROOT,
        "run_id": RUN,
        "model": MODEL,
        "reasoning_effort": EFFORT,
        "effective_prompt_sha256": PROMPT_SHA,
    }
    value.update(changes)
    value["release_sha256"] = canonical_record_hash(value, "release_sha256")
    return value


def provider_usage(
    total: int,
    *,
    output: int = 10,
    cached: int = 0,
    cache_write: int = 0,
    reasoning: int = 0,
) -> dict[str, object]:
    assert output <= total
    return {
        "input_tokens": total - output,
        "input_tokens_details": {
            "cached_tokens": cached,
            "cache_write_tokens": cache_write,
        },
        "output_tokens": output,
        "output_tokens_details": {"reasoning_tokens": reasoning},
        "total_tokens": total,
    }


def appserver_usage(usage: dict[str, object]) -> dict[str, int]:
    input_details = usage.get("input_tokens_details")
    output_details = usage.get("output_tokens_details")
    assert isinstance(input_details, dict)
    assert isinstance(output_details, dict)
    return {
        "input_tokens": int(usage["input_tokens"]),
        "cached_input_tokens": int(input_details["cached_tokens"]),
        "cache_write_input_tokens": int(input_details["cache_write_tokens"]),
        "output_tokens": int(usage["output_tokens"]),
        "reasoning_output_tokens": int(output_details["reasoning_tokens"]),
        "total_tokens": int(usage["total_tokens"]),
    }


def counted_request_body() -> bytes:
    return json.dumps(
        {"model": MODEL, "stream": True, "input": "test"},
        separators=(",", ":"),
    ).encode("utf-8")


def request_metadata(thread_id: str, turn_id: str) -> dict[str, str]:
    return {
        "installation_id": "installation-1",
        "session_id": "session-1",
        "thread_id": thread_id,
        "turn_id": turn_id,
        "request_kind": "turn",
        "window_id": "window-1",
    }


def completed_sse(
    response_id: str,
    usage: dict[str, object],
    *,
    tool_frame: bool = False,
) -> bytes:
    frames: list[str] = []
    output: list[dict[str, object]] = []
    if tool_frame:
        output_item: dict[str, object] = {
            "type": "function_call",
            "id": "fc-danger",
            "status": "completed",
            "call_id": "call-danger",
            "name": "exec",
            "arguments": '{"danger":true}',
        }
        tool = {
            "type": "response.output_item.done",
            "output_index": 0,
            "item": output_item,
        }
        output.append(output_item)
        frames.append(
            "event: response.output_item.done\ndata: "
            + json.dumps(tool, separators=(",", ":"))
            + "\n\n"
        )
    completed = {
        "type": "response.completed",
        "sequence_number": 99,
        "response": {
            "id": response_id,
            "usage": usage,
            "end_turn": False,
            "output": output,
        },
    }
    frames.append(
        "event: response.completed\ndata: "
        + json.dumps(completed, separators=(",", ":"))
        + "\n\n"
    )
    return "".join(frames).encode("utf-8")


def compaction_completed_sse(
    response_id: str,
    usage: dict[str, object],
    *,
    encrypted_content: str = "opaque-compaction-history",
    extra_output_item: dict[str, object] | None = None,
) -> bytes:
    output: list[dict[str, object]] = [
        {
            "type": "compaction",
            "id": "cmp-upstream-extra-field-is-dropped",
            "encrypted_content": encrypted_content,
        }
    ]
    events: list[dict[str, object]] = [
        {
            "type": "response.output_item.done",
            "sequence_number": 7,
            "output_index": 0,
            "item": output[0],
        }
    ]
    if extra_output_item is not None:
        output.append(extra_output_item)
        events.append(
            {
                "type": "response.output_item.done",
                "sequence_number": 8,
                "output_index": 1,
                "item": extra_output_item,
            }
        )
    events.append(
        {
            "type": "response.completed",
            "sequence_number": 9,
            "response": {
                "id": response_id,
                "usage": usage,
                "end_turn": False,
                "output": output,
            },
        }
    )
    return "".join(
        f"event: {event['type']}\ndata: "
        + json.dumps(event, separators=(",", ":"))
        + "\n\n"
        for event in events
    ).encode("utf-8")


def output_items_completed_sse(
    response_id: str,
    usage: dict[str, object],
    output_items: list[dict[str, object]],
    *,
    completed_output: list[dict[str, object]] | None = None,
) -> bytes:
    events: list[dict[str, object]] = [
        {
            "type": "response.output_item.done",
            "output_index": index,
            "item": item,
        }
        for index, item in enumerate(output_items)
    ]
    events.append(
        {
            "type": "response.completed",
            "response": {
                "id": response_id,
                "usage": usage,
                "end_turn": False,
                "output": (
                    output_items if completed_output is None else completed_output
                ),
            },
        }
    )
    return "".join(
        f"event: {event['type']}\ndata: "
        + json.dumps(event, separators=(",", ":"))
        + "\n\n"
        for event in events
    ).encode("utf-8")


def collaboration_wait_sse(
    response_id: str,
    usage: dict[str, object],
    *,
    timeout_ms: object = 3_600_000,
    namespace: str = "collaboration",
    extra_arguments: dict[str, object] | None = None,
    extra_output_items: list[dict[str, object]] | None = None,
    function_call_extra_fields: dict[str, object] | None = None,
    omit_status: bool = False,
) -> bytes:
    arguments: dict[str, object] = {"timeout_ms": timeout_ms}
    if extra_arguments:
        arguments.update(extra_arguments)
    wait_item: dict[str, object] = {
        "type": "function_call",
        "id": f"fc-{response_id}-wait",
        "status": "completed",
        "call_id": f"call-{response_id}-wait",
        "name": "wait_agent",
        "namespace": namespace,
        "arguments": json.dumps(arguments, separators=(",", ":")),
    }
    wait_item.update(function_call_extra_fields or {})
    if omit_status:
        wait_item.pop("status")
    output_items: list[dict[str, object]] = [
        {
            "type": "reasoning",
            "id": f"rs-{response_id}",
            "status": "completed",
            "encrypted_content": "PRIVATE-REASONING-JOB-1508245",
            "summary": [],
        },
        wait_item,
    ]
    output_items.extend(extra_output_items or [])
    return output_items_completed_sse(response_id, usage, output_items)


class FakePlan:
    def __init__(
        self,
        body: bytes,
        *,
        status: int = 200,
        content_type: str | None = "text/event-stream",
        content_encoding: str | None = "identity",
        content_types: list[str] | None = None,
        content_encodings: list[str] | None = None,
        release: threading.Event | None = None,
        read_error: BaseException | None = None,
    ) -> None:
        self.body = body
        self.status = status
        self.content_types = (
            list(content_types)
            if content_types is not None
            else ([] if content_type is None else [content_type])
        )
        self.content_encodings = (
            list(content_encodings)
            if content_encodings is not None
            else ([] if content_encoding is None else [content_encoding])
        )
        self.release = release
        self.read_error = read_error
        self.started = threading.Event()
        self.request: tuple[tuple[object, ...], dict[str, object]] | None = None


class FakeResponse:
    def __init__(self, plan: FakePlan) -> None:
        self.plan = plan
        self.status = plan.status
        self._read = False

    def read(self, _maximum: int) -> bytes:
        if self.plan.release is not None:
            if not self.plan.release.wait(10.0):
                raise TimeoutError("test upstream was not released")
        if self.plan.read_error is not None:
            raise self.plan.read_error
        if self._read:
            return b""
        self._read = True
        return self.plan.body

    def getheader(self, name: str) -> str | None:
        values = {
            "content-type": self.plan.content_types,
            "content-encoding": self.plan.content_encodings,
        }
        selected = values.get(name.lower(), [])
        return ", ".join(selected) if selected else None

    def getheaders(self) -> list[tuple[str, str]]:
        return (
            [("Content-Type", value) for value in self.plan.content_types]
            + [
                ("Content-Encoding", value)
                for value in self.plan.content_encodings
            ]
            + [("x-request-id", "fake-request")]
        )


class FakeConnection:
    def __init__(self, plan: FakePlan) -> None:
        self.plan = plan

    def request(self, *args: object, **kwargs: object) -> None:
        self.plan.request = (args, kwargs)
        self.plan.started.set()

    def getresponse(self) -> FakeResponse:
        return FakeResponse(self.plan)

    def close(self) -> None:
        return


class FakeFactory:
    def __init__(self, plans: list[FakePlan]) -> None:
        self.plans = plans
        self._index = 0
        self._lock = threading.Lock()

    @property
    def count(self) -> int:
        with self._lock:
            return self._index

    def __call__(self) -> FakeConnection:
        with self._lock:
            if self._index >= len(self.plans):
                raise AssertionError("unexpected upstream connection")
            plan = self.plans[self._index]
            self._index += 1
        return FakeConnection(plan)


class _BrokenClientWriter:
    def write(self, _body: bytes) -> int:
        raise BrokenPipeError("test client disconnected after provider commit")

    def flush(self) -> None:
        return


class _DisconnectedClientHandler:
    """Small handler surface for a deterministic post-commit disconnect."""

    command = "POST"

    def __init__(self, body: bytes) -> None:
        self.headers = {
            "Content-Type": "application/json",
            "Content-Length": str(len(body)),
        }
        self.rfile = io.BytesIO(body)
        self.wfile = _BrokenClientWriter()
        self.close_connection = False

    def send_response(self, _status: int) -> None:
        return

    def send_header(self, _name: str, _value: str) -> None:
        return

    def end_headers(self) -> None:
        return


class GateHarness:
    def __init__(
        self,
        testcase: unittest.TestCase,
        plans: list[FakePlan],
        *,
        token_limit: int,
        response_bound: int,
        bind_prompt: bool = True,
    ) -> None:
        self.testcase = testcase
        self.temporary = tempfile.TemporaryDirectory()
        self.root = Path(self.temporary.name)
        self.factory = FakeFactory(plans)
        self.gate = ProviderTokenGate(
            self.root / "attempt.provider-token-gate.live.json",
            self.root / "attempt.provider-token-gate.json",
            token_limit=token_limit,
            response_bound=response_bound,
            model_catalog_sha256=CATALOG_SHA,
            model_entry_sha256=ENTRY_SHA,
            capability_nonce="d" * 64,
            _connection_factory=self.factory,
        )
        self.url = urlsplit(self.gate.start())
        self.gate.bind_root(
            ROOT, run_id=RUN, model=MODEL, reasoning_effort=EFFORT
        )
        if bind_prompt:
            self.gate.bind_prompt_release(prompt_release())

    def post(
        self,
        *,
        model: str = MODEL,
        stream: object = True,
        secret: str = "PROMPT-SECRET-DO-NOT-PERSIST",
        path: str | None = None,
        authorization: str = "Bearer AUTH-SECRET-DO-NOT-PERSIST",
        request_kind: str = "turn",
        installation_id: str = "installation-1",
        session_id: str = "session-1",
        thread_id: str = ROOT,
        turn_id: str = "turn-1",
        window_id: str = "window-1",
    ) -> tuple[int, bytes, dict[str, str]]:
        body = json.dumps(
            {"model": model, "stream": stream, "input": secret},
            separators=(",", ":"),
        ).encode("utf-8")
        connection = http.client.HTTPConnection(
            self.url.hostname, self.url.port, timeout=15
        )
        try:
            connection.request(
                "POST",
                path or self.url.path + "/responses",
                body,
                {
                    "Content-Type": "application/json",
                    "Content-Length": str(len(body)),
                    "Authorization": authorization,
                    "x-openai-attestation": "ATTESTATION-SECRET-DO-NOT-PERSIST",
                    "x-codex-turn-metadata": json.dumps(
                        {
                            "installation_id": installation_id,
                            "session_id": session_id,
                            "thread_id": thread_id,
                            "turn_id": turn_id,
                            "request_kind": request_kind,
                            "window_id": window_id,
                        }
                    ),
                },
            )
            response = connection.getresponse()
            result = response.read()
            headers = {name.lower(): value for name, value in response.getheaders()}
            return response.status, result, headers
        finally:
            connection.close()

    def crossbind(self, response_id: str, usage: dict[str, object], sequence: int) -> None:
        self.gate.crossbind_appserver_response(
            response_id,
            appserver_usage(usage),
            thread_id=ROOT,
            turn_id="turn-1",
            event_sequence=sequence,
        )

    def finish(self, reason: str | None = None) -> dict[str, object]:
        if reason is not None:
            result = self.gate.close(reason)
            self.testcase.assertTrue(result["won"])
        self.gate.stop()
        return self.gate.finalize()

    def cleanup(self) -> None:
        try:
            snapshot = self.gate.snapshot()
            if snapshot["phase"] not in (PHASE_CLOSED, PHASE_POISONED):
                self.gate.close("system_error")
            self.gate.stop()
        except (ProviderGateError, OSError):
            pass
        self.temporary.cleanup()


class ProviderTokenGateTests(unittest.TestCase):
    def test_path_helpers_strip_usage_suffix(self) -> None:
        usage = Path("/trusted/run.usage.json")
        self.assertEqual(
            provider_gate_live_path(usage),
            Path("/trusted/run" + PROVIDER_GATE_LIVE_SUFFIX),
        )
        self.assertEqual(
            provider_gate_artifact_path(usage),
            Path("/trusted/run" + PROVIDER_GATE_FINAL_SUFFIX),
        )

    def test_transport_builder_is_local_only_explicit_and_hostname_verifying(self) -> None:
        with mock.patch.object(
            gate_module.socket,
            "getaddrinfo",
            side_effect=AssertionError("transport builder performed DNS"),
        ), mock.patch.object(
            gate_module.http.client,
            "HTTPSConnection",
            side_effect=AssertionError("transport builder opened a connection"),
        ):
            context, provenance = build_transport_provenance()
        self.assertEqual(
            provenance["connection_factory_mode"],
            PROVIDER_CONNECTION_FACTORY_EXPLICIT_TLS,
        )
        self.assertEqual(context.verify_mode, ssl.CERT_REQUIRED)
        self.assertIs(context.check_hostname, True)
        self.assertEqual(context.minimum_version, ssl.TLSVersion.TLSv1_2)
        self.assertIsNone(context.keylog_filename)
        self.assertGreater(context.cert_store_stats()["x509_ca"], 0)
        tls = provenance["tls"]
        self.assertEqual(
            tls["certificate_source_mode"], PROVIDER_CERTIFICATE_SOURCE_MODE
        )
        self.assertEqual(
            tls["certificate_source"]["logical_path"],
            gate_module.PROVIDER_CA_BUNDLE_PATH,
        )
        self.assertIsNone(tls["certificate_source"]["symlink_target"])
        self.assertIs(tls["default_capath_used"], False)
        self.assertEqual(tls["server_hostname"], "chatgpt.com")
        self.assertEqual(tls["alpn_protocols"], ["http/1.1"])
        self.assertEqual(
            provenance["environment"]["proxy_mode"], PROVIDER_PROXY_MODE
        )
        self.assertIs(
            provenance["resolver"]["resolved_addresses_frozen"], False
        )
        self.assertEqual(
            provenance["resolver"]["variability_classification"],
            "availability_only_under_authenticated_tls_hostname",
        )
        for key in (
            "http_server_module",
            "json_module",
            "json_encoder_module",
            "json_decoder_module",
            "json_extension",
            "hashlib_module",
            "hashlib_extension",
        ):
            self.assertEqual(len(provenance["python"][key]["sha256"]), 64)

    def test_default_factory_is_direct_and_uses_the_frozen_context(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            gate = ProviderTokenGate(
                root / "live.json",
                root / "final.json",
                token_limit=100,
                response_bound=272,
                model_catalog_sha256=CATALOG_SHA,
                model_entry_sha256=ENTRY_SHA,
                capability_nonce="d" * 64,
            )
            sentinel_connection = object()
            with mock.patch.object(
                gate_module.http.client,
                "HTTPSConnection",
                return_value=sentinel_connection,
            ) as constructor:
                self.assertIs(gate._connection_factory(), sentinel_connection)
            constructor.assert_called_once_with(
                gate_module.DEFAULT_UPSTREAM_HOST,
                gate_module.DEFAULT_UPSTREAM_PORT,
                timeout=1800,
                context=gate._tls_context,
            )
            provenance = gate.static_record()["configuration"][
                "transport_provenance"
            ]
            self.assertEqual(
                provenance["connection_factory_mode"],
                PROVIDER_CONNECTION_FACTORY_EXPLICIT_TLS,
            )

    def test_transport_override_environment_is_fail_closed(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            for name in PROVIDER_TRANSPORT_ENV_REQUIRED_ABSENT:
                with self.subTest(name=name), mock.patch.dict(
                    os.environ, {name: "forbidden-test-value"}
                ):
                    with self.assertRaisesRegex(
                        ProviderGateError, "transport override environment"
                    ):
                        ProviderTokenGate(
                            root / "live.json",
                            root / "final.json",
                            token_limit=100,
                            response_bound=272,
                            model_catalog_sha256=CATALOG_SHA,
                            model_entry_sha256=ENTRY_SHA,
                            capability_nonce="d" * 64,
                        )

    def test_runtime_transport_override_poisoned_before_upstream_send(self) -> None:
        usage = provider_usage(40)
        plan = FakePlan(completed_sse("never-sent", usage))
        harness = GateHarness(
            self, [plan], token_limit=500, response_bound=100
        )
        self.addCleanup(harness.cleanup)
        with mock.patch.dict(os.environ, {"SSL_CERT_FILE": "/tmp/untrusted.pem"}):
            status, _body, _headers = harness.post()
        self.assertEqual(status, 502)
        self.assertIsNone(plan.request)
        self.assertFalse(plan.started.is_set())
        state = harness.gate.snapshot()
        self.assertEqual(state["phase"], PHASE_POISONED)
        artifact = harness.finish()
        self.assertIs(artifact["calls"][0]["upstream_started"], False)
        self.assertEqual(
            artifact["configuration"]["transport_provenance"][
                "connection_factory_mode"
            ],
            PROVIDER_CONNECTION_FACTORY_TEST_OVERRIDE,
        )

    def test_b_greater_than_limit_starts_exclusive_and_sanitizes_crossing(self) -> None:
        usage = provider_usage(110, output=10, cached=80, reasoning=5)
        upstream = completed_sse("resp-cross", usage, tool_frame=True)
        harness = GateHarness(
            self, [FakePlan(upstream)], token_limit=100, response_bound=272
        )
        self.addCleanup(harness.cleanup)
        status, body, _headers = harness.post()
        self.assertEqual(status, 200)
        self.assertNotIn(b"function_call", body)
        frames = [frame for frame in body.decode().split("\n\n") if frame]
        self.assertEqual(len(frames), 1)
        self.assertTrue(frames[0].startswith("event: response.completed\ndata: "))
        event = json.loads(frames[0].split("\ndata: ", 1)[1])
        self.assertEqual(set(event), {"type", "response"})
        self.assertEqual(event["response"]["id"], "resp-cross")
        self.assertEqual(event["response"]["usage"], usage)
        self.assertEqual(event["response"]["output"], [])
        self.assertIs(event["response"]["end_turn"], True)
        harness.crossbind("resp-cross", usage, 1)
        artifact = harness.finish()
        state = artifact["state"]
        self.assertEqual(state["phase"], PHASE_CLOSED)
        self.assertEqual(state["close_reason"], CLOSE_REASON_TOKEN_LIMIT)
        self.assertEqual(state["completed_tokens"], 110)
        call = artifact["calls"][0]
        self.assertEqual(call["admission_mode"], ADMISSION_MODE_EXCLUSIVE)
        self.assertEqual(call["release_kind"], RELEASE_SANITIZED_CROSSING)
        self.assertEqual(call["normalized_usage"]["cached_input_tokens"], 80)
        self.assertEqual(call["released_sanitized_body_utf8"].encode(), body)
        self.assertEqual(stat.S_IMODE(harness.gate.final_artifact_path.stat().st_mode), 0o444)

    def test_b_equal_limit_first_request_is_exclusive(self) -> None:
        usage = provider_usage(100, cached=50)
        harness = GateHarness(
            self,
            [FakePlan(completed_sse("resp-equal", usage))],
            token_limit=100,
            response_bound=100,
        )
        self.addCleanup(harness.cleanup)
        self.assertEqual(harness.post()[0], 200)
        harness.crossbind("resp-equal", usage, 1)
        artifact = harness.finish()
        self.assertEqual(artifact["calls"][0]["admission_mode"], ADMISSION_MODE_EXCLUSIVE)
        self.assertTrue(artifact["state"]["crossing_closed"])

    def test_compaction_crossing_releases_only_one_minimal_compaction_item(self) -> None:
        usage = provider_usage(110, output=10, cached=80, reasoning=5)
        upstream = compaction_completed_sse("resp-compact-cross", usage)
        harness = GateHarness(
            self, [FakePlan(upstream)], token_limit=100, response_bound=272
        )
        self.addCleanup(harness.cleanup)

        status, body, _headers = harness.post(request_kind="compaction")
        self.assertEqual(status, 200)
        frames = [frame for frame in body.decode().split("\n\n") if frame]
        self.assertEqual(len(frames), 2)
        events = [json.loads(frame.split("\ndata: ", 1)[1]) for frame in frames]
        self.assertEqual(
            events[0],
            {
                "type": "response.output_item.done",
                "item": {
                    "type": "compaction",
                    "encrypted_content": "opaque-compaction-history",
                },
            },
        )
        self.assertEqual(set(events[1]), {"type", "response"})
        self.assertEqual(events[1]["type"], "response.completed")
        self.assertEqual(events[1]["response"]["id"], "resp-compact-cross")
        self.assertEqual(events[1]["response"]["usage"], usage)
        self.assertEqual(events[1]["response"]["output"], [])
        self.assertIs(events[1]["response"]["end_turn"], True)

        harness.crossbind("resp-compact-cross", usage, 1)
        artifact = harness.finish()
        call = artifact["calls"][0]
        crossing = artifact["state"]["crossing"]
        self.assertEqual(
            call["release_kind"], RELEASE_SANITIZED_COMPACTION_CROSSING
        )
        self.assertEqual(call["request_metadata"]["request_kind"], "compaction")
        self.assertEqual(call["released_sanitized_events"], events)
        self.assertEqual(crossing["request_kind"], "compaction")
        self.assertEqual(crossing["release_kind"], call["release_kind"])
        self.assertTrue(
            artifact["invariants"][
                "no_action_capable_output_frames_on_crossing"
            ]
        )
        self.assertEqual(validate_artifact(harness.gate.final_artifact_path), artifact)

        for label, mutate in (
            (
                "extra-compaction-frame",
                lambda value: value["calls"][0]["released_sanitized_events"].insert(
                    1, value["calls"][0]["released_sanitized_events"][0]
                ),
            ),
            (
                "ordinary-release-kind",
                lambda value: value["calls"][0].__setitem__(
                    "release_kind", RELEASE_SANITIZED_CROSSING
                ),
            ),
            (
                "crossing-kind",
                lambda value: value["state"]["crossing"].__setitem__(
                    "request_kind", "turn"
                ),
            ),
        ):
            with self.subTest(label=label):
                forged = json.loads(json.dumps(artifact))
                mutate(forged)
                reseal_provider_gate_record(forged)
                forged_path = harness.root / f"forged-compaction-{label}.json"
                forged_path.write_text(
                    json.dumps(forged, sort_keys=True, separators=(",", ":")) + "\n",
                    encoding="utf-8",
                )
                forged_path.chmod(0o444)
                with self.assertRaises(ProviderGateValidationError):
                    validate_artifact(forged_path)

    def test_compaction_crossing_rejects_missing_empty_or_extra_output_items(self) -> None:
        usage = provider_usage(110)
        cases = (
            ("missing", completed_sse("resp-missing-compaction", usage)),
            (
                "empty",
                compaction_completed_sse(
                    "resp-empty-compaction", usage, encrypted_content=""
                ),
            ),
            (
                "extra",
                compaction_completed_sse(
                    "resp-extra-compaction",
                    usage,
                    extra_output_item={
                        "type": "function_call",
                        "call_id": "call-must-remain-quarantined",
                        "name": "exec",
                        "arguments": "{}",
                    },
                ),
            ),
        )
        for label, upstream in cases:
            with self.subTest(label=label):
                harness = GateHarness(
                    self, [FakePlan(upstream)], token_limit=100, response_bound=272
                )
                self.addCleanup(harness.cleanup)
                status, body, _headers = harness.post(request_kind="compaction")
                self.assertEqual(status, 502)
                self.assertNotIn(b"function_call", body)
                self.assertEqual(harness.gate.snapshot()["phase"], PHASE_POISONED)
                artifact = harness.finish()
                self.assertTrue(artifact["state"]["poisoned"])
                self.assertIsNone(artifact["calls"][0]["normalized_usage"])

    def test_four_overlaps_drain_then_serialize_to_sole_crossing(self) -> None:
        first_release = threading.Event()
        first_usages = [provider_usage(80, cached=50) for _ in range(4)]
        fifth_usage = provider_usage(100, cached=60)
        sixth_usage = provider_usage(100, cached=70)
        crossing_usage = provider_usage(100, cached=80)
        crossing_release = threading.Event()
        plans = [
            FakePlan(completed_sse(f"resp-{index}", usage), release=first_release)
            for index, usage in enumerate(first_usages, 1)
        ]
        plans.extend(
            [
                FakePlan(completed_sse("resp-5", fifth_usage)),
                FakePlan(completed_sse("resp-6", sixth_usage)),
                FakePlan(
                    completed_sse("resp-7", crossing_usage, tool_frame=True),
                    release=crossing_release,
                ),
            ]
        )
        harness = GateHarness(
            self, plans, token_limit=600, response_bound=120
        )
        self.addCleanup(harness.cleanup)
        results: dict[int, tuple[int, bytes, dict[str, str]]] = {}

        def post_at(index: int) -> None:
            results[index] = harness.post(secret=f"secret-{index}")

        workers = [threading.Thread(target=post_at, args=(index,)) for index in range(1, 5)]
        for worker in workers:
            worker.start()
        for plan in plans[:4]:
            self.assertTrue(plan.started.wait(5.0))
        fifth = threading.Thread(target=post_at, args=(5,))
        fifth.start()
        deadline = time.monotonic() + 5.0
        while harness.gate.snapshot()["phase"] != PHASE_DRAINING:
            self.assertLess(time.monotonic(), deadline)
            time.sleep(0.01)
        self.assertEqual(harness.factory.count, 4)
        first_release.set()
        for worker in workers:
            worker.join(5.0)
            self.assertFalse(worker.is_alive())
        fifth.join(5.0)
        self.assertFalse(fifth.is_alive())
        self.assertEqual(harness.gate.snapshot()["phase"], PHASE_EXCLUSIVE)
        results[6] = harness.post(secret="secret-6")
        seventh = threading.Thread(target=post_at, args=(7,))
        seventh.start()
        self.assertTrue(plans[6].started.wait(5.0))
        denied = threading.Thread(target=post_at, args=(8,))
        denied.start()
        time.sleep(0.05)
        self.assertEqual(harness.factory.count, 7)
        crossing_release.set()
        seventh.join(5.0)
        denied.join(5.0)
        self.assertFalse(seventh.is_alive())
        self.assertFalse(denied.is_alive())
        self.assertEqual(results[8][0], 409)
        self.assertEqual(harness.factory.count, 7)
        for index, usage in enumerate(first_usages, 1):
            harness.crossbind(f"resp-{index}", usage, index)
        harness.crossbind("resp-5", fifth_usage, 5)
        harness.crossbind("resp-6", sixth_usage, 6)
        harness.crossbind("resp-7", crossing_usage, 7)
        artifact = harness.finish()
        self.assertEqual(artifact["state"]["completed_tokens"], 620)
        crossing = artifact["state"]["crossing"]
        self.assertEqual(crossing["response_id"], "resp-7")
        self.assertTrue(crossing["sole_inflight"])
        exclusive_calls = [
            call
            for call in artifact["calls"]
            if call["admission_mode"] == ADMISSION_MODE_EXCLUSIVE
        ]
        self.assertEqual([call["response_id"] for call in exclusive_calls], [
            "resp-5",
            "resp-6",
            "resp-7",
        ])
        self.assertTrue(all(call["open_before"] == 0 for call in exclusive_calls))
        self.assertTrue(
            any(
                denial["reason"] == "provider_gate_closed"
                and denial["upstream_started"] is False
                for denial in artifact["denials"]
            )
        )

    def test_randomized_completion_interleavings_are_exact(self) -> None:
        for seed in range(4):
            with self.subTest(seed=seed):
                releases = [threading.Event() for _ in range(3)]
                usages = [provider_usage(30 + index, cached=10) for index in range(3)]
                plans = [
                    FakePlan(completed_sse(f"random-{seed}-{index}", usage), release=release)
                    for index, (usage, release) in enumerate(zip(usages, releases))
                ]
                harness = GateHarness(
                    self, plans, token_limit=1_000, response_bound=100
                )
                workers = [threading.Thread(target=harness.post) for _ in plans]
                try:
                    for worker in workers:
                        worker.start()
                    for plan in plans:
                        self.assertTrue(plan.started.wait(5.0))
                    order = list(range(3))
                    random.Random(seed).shuffle(order)
                    for index in order:
                        releases[index].set()
                        time.sleep(0.005)
                    for worker in workers:
                        worker.join(5.0)
                        self.assertFalse(worker.is_alive())
                    for index, usage in enumerate(usages):
                        harness.crossbind(f"random-{seed}-{index}", usage, index)
                    artifact = harness.finish(CLOSE_REASON_NATURAL_END)
                    self.assertEqual(
                        artifact["state"]["completed_tokens"],
                        sum(int(usage["total_tokens"]) for usage in usages),
                    )
                    self.assertTrue(artifact["invariants"]["strict_reservation_safe"])
                finally:
                    harness.cleanup()

    def test_below_cap_body_is_byte_identical_and_secrets_are_redacted(self) -> None:
        usage = provider_usage(90, cached=70)
        upstream = completed_sse("resp-low", usage, tool_frame=True)
        harness = GateHarness(
            self, [FakePlan(upstream)], token_limit=500, response_bound=100
        )
        self.addCleanup(harness.cleanup)
        status, body, _ = harness.post()
        self.assertEqual(status, 200)
        self.assertEqual(body, upstream)
        harness.crossbind("resp-low", usage, 1)
        artifact = harness.finish(CLOSE_REASON_NATURAL_END)
        call = artifact["calls"][0]
        self.assertEqual(call["release_kind"], RELEASE_BYTE_IDENTITY)
        self.assertEqual(call["released_body_sha256"], call["upstream_body_sha256"])
        artifact_text = harness.gate.final_artifact_path.read_text()
        self.assertNotIn("PROMPT-SECRET-DO-NOT-PERSIST", artifact_text)
        self.assertNotIn("AUTH-SECRET-DO-NOT-PERSIST", artifact_text)
        self.assertNotIn("ATTESTATION-SECRET-DO-NOT-PERSIST", artifact_text)
        self.assertNotIn("d" * 64, artifact_text)
        self.assertEqual(call["credential_headers_present"], [
            "authorization",
            "x-openai-attestation",
        ])

    def test_explicit_parent_interrupt_authenticates_discarded_child_response(
        self,
    ) -> None:
        child_usage = provider_usage(90, cached=50)
        interrupt_usage = provider_usage(80, cached=40)
        tail_usage = provider_usage(70, cached=30)
        interrupt_release = threading.Event()
        child_release = threading.Event()
        interrupt_item: dict[str, object] = {
            "type": "function_call",
            "id": "fc-explicit-interrupt",
            "status": "completed",
            "call_id": "call-explicit-interrupt",
            "name": "interrupt_agent",
            "namespace": "collaboration",
            "arguments": json.dumps(
                {"target": "/root/lemma_search"}, separators=(",", ":")
            ),
        }
        harness = GateHarness(
            self,
            [
                FakePlan(
                    output_items_completed_sse(
                        "resp-explicit-interrupt",
                        interrupt_usage,
                        [interrupt_item],
                    ),
                    release=interrupt_release,
                ),
                FakePlan(
                    completed_sse("resp-discarded-child", child_usage),
                    release=child_release,
                ),
                FakePlan(completed_sse("resp-direct-tail", tail_usage)),
            ],
            token_limit=1_000,
            response_bound=100,
        )
        self.addCleanup(harness.cleanup)

        interrupt_result: list[tuple[int, bytes, dict[str, str]]] = []
        interrupt = threading.Thread(target=lambda: interrupt_result.append(harness.post()))
        interrupt.start()
        self.assertTrue(harness.factory.plans[0].started.wait(5.0))

        # The child starts after the provider admitted the parent response, but
        # before that response commits and exposes the interrupt function call.
        disconnected_handler = _DisconnectedClientHandler(counted_request_body())
        child = threading.Thread(
            target=harness.gate._handle_counted,
            args=(
                disconnected_handler,
                request_metadata("child-thread", "child-turn"),
            ),
        )
        child.start()
        self.assertTrue(harness.factory.plans[1].started.wait(5.0))

        interrupt_release.set()
        interrupt.join(5.0)
        self.assertFalse(interrupt.is_alive())
        self.assertEqual(interrupt_result[0][0], 200)
        harness.crossbind("resp-explicit-interrupt", interrupt_usage, 1)
        child_release.set()
        child.join(5.0)
        self.assertFalse(child.is_alive())
        self.assertTrue(disconnected_handler.close_connection)
        self.assertFalse(harness.gate.snapshot()["poisoned"])

        candidates = (
            harness.gate.discarded_after_explicit_child_interrupt_candidates(
                "child-thread", "child-turn"
            )
        )
        self.assertEqual(len(candidates), 1)
        candidate = candidates[0]
        self.assertEqual(
            set(candidate),
            gate_module.PROVIDER_GATE_DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_CANDIDATE_KEYS,
        )
        self.assertEqual(candidate["response_id"], "resp-discarded-child")
        self.assertEqual(
            candidate["interrupting_response_id"], "resp-explicit-interrupt"
        )
        self.assertEqual(
            candidate["interrupt_function_call_id"], "call-explicit-interrupt"
        )
        self.assertLess(
            candidate["interrupt_admitted_monotonic_ns"],
            candidate["admitted_monotonic_ns"],
        )
        self.assertLess(
            candidate["interrupt_bind_monotonic_ns"],
            candidate["commit_monotonic_ns"],
        )

        harness.gate.crossbind_discarded_after_explicit_child_interrupt(
            "resp-discarded-child",
            "child-thread",
            "child-turn",
            "resp-explicit-interrupt",
        )
        self.assertEqual(
            harness.gate.discarded_after_explicit_child_interrupt_candidates(
                "child-thread", "child-turn"
            ),
            [],
        )
        self.assertEqual(harness.post()[0], 200)
        harness.crossbind("resp-direct-tail", tail_usage, 2)
        artifact = harness.finish(CLOSE_REASON_NATURAL_END)
        discarded = next(
            call
            for call in artifact["calls"]
            if call["response_id"] == "resp-discarded-child"
        )
        self.assertIsNone(discarded["error"])
        self.assertFalse(discarded["client_release_complete"])
        self.assertEqual(
            discarded["appserver_delivery"]["kind"],
            gate_module.PROVIDER_GATE_DELIVERY_DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT,
        )
        self.assertEqual(artifact["state"]["completed_tokens"], 240)
        self.assertTrue(
            artifact["invariants"]["all_appserver_deliveries_reconciled"]
        )

    def test_unresolved_postcommit_disconnect_still_fails_closed(self) -> None:
        usage = provider_usage(90, cached=50)
        harness = GateHarness(
            self,
            [FakePlan(completed_sse("resp-unresolved-disconnect", usage))],
            token_limit=500,
            response_bound=100,
        )
        self.addCleanup(harness.cleanup)

        handler = _DisconnectedClientHandler(counted_request_body())
        harness.gate._handle_counted(
            handler, request_metadata("child-thread", "child-turn")
        )
        snapshot = harness.gate.snapshot()
        self.assertFalse(snapshot["poisoned"])

        close = harness.gate.close(CLOSE_REASON_NATURAL_END)
        self.assertFalse(close["won"])
        self.assertEqual(close["phase"], PHASE_POISONED)
        artifact = harness.finish()
        self.assertTrue(artifact["state"]["poisoned"])
        self.assertIn(
            "natural_end_boundary_before_appserver_delivery",
            artifact["state"]["poison_reasons"],
        )
        call = artifact["calls"][0]
        self.assertEqual(call["error"], "client_disconnect_after_commit")
        self.assertIsNone(call["appserver_delivery"])
        self.assertFalse(
            artifact["invariants"]["all_appserver_deliveries_reconciled"]
        )

    def test_job_1508245_suppressed_wait_is_reconciled_to_direct_successor(self) -> None:
        """The provider-complete wait remains counted when Codex suppresses its event."""

        wait_usage = provider_usage(
            11_835, output=60, cached=10_000, reasoning=36
        )
        successor_usage = provider_usage(70, output=10, cached=50)
        wait_body = collaboration_wait_sse(
            "resp-job-1508245-wait", wait_usage
        )
        harness = GateHarness(
            self,
            [
                FakePlan(wait_body),
                FakePlan(completed_sse("resp-job-1508245-successor", successor_usage)),
            ],
            token_limit=50_000,
            response_bound=20_000,
        )
        self.addCleanup(harness.cleanup)

        self.assertEqual(harness.post()[0], 200)
        self.assertEqual(harness.post()[0], 200)
        harness.crossbind("resp-job-1508245-successor", successor_usage, 8)

        candidates = harness.gate.suppressed_collaboration_wait_candidates(
            ROOT, "turn-1"
        )
        self.assertEqual(len(candidates), 1)
        candidate = candidates[0]
        self.assertEqual(
            set(candidate),
            gate_module.PROVIDER_GATE_SUPPRESSED_WAIT_CANDIDATE_KEYS,
        )
        self.assertEqual(candidate["response_id"], "resp-job-1508245-wait")
        self.assertEqual(
            candidate["successor_response_id"],
            "resp-job-1508245-successor",
        )
        self.assertEqual(candidate["normalized_usage"], appserver_usage(wait_usage))
        self.assertEqual(candidate["wait_timeout_ms"], 3_600_000)
        self.assertLess(
            candidate["commit_monotonic_ns"],
            candidate["successor_admitted_monotonic_ns"],
        )

        before = harness.gate.completed_response_usage_snapshot()
        self.assertEqual(len(before), 2)
        self.assertTrue(
            all(
                set(item)
                == gate_module.PROVIDER_GATE_COMPLETED_RESPONSE_USAGE_SNAPSHOT_KEYS
                for item in before
            )
        )
        self.assertIsNone(before[0]["appserver_delivery_kind"])
        self.assertEqual(
            before[1]["appserver_delivery_kind"],
            gate_module.PROVIDER_GATE_DELIVERY_DIRECT,
        )

        harness.gate.crossbind_suppressed_collaboration_wait(
            "resp-job-1508245-wait",
            ROOT,
            "turn-1",
            "resp-job-1508245-successor",
        )
        self.assertEqual(
            harness.gate.suppressed_collaboration_wait_candidates(
                ROOT, "turn-1"
            ),
            [],
        )
        after = harness.gate.completed_response_usage_snapshot()
        self.assertEqual(
            after[0]["appserver_delivery_kind"],
            gate_module.PROVIDER_GATE_DELIVERY_SUPPRESSED_WAIT,
        )
        self.assertEqual(
            after[0]["successor_response_id"],
            "resp-job-1508245-successor",
        )

        artifact = harness.finish(CLOSE_REASON_ACCEPTED_SUBMISSION)
        self.assertEqual(artifact["state"]["completed_tokens"], 11_905)
        self.assertTrue(
            artifact["invariants"][
                "all_appserver_deliveries_reconciled"
            ]
        )
        wait_call, successor_call = artifact["calls"]
        self.assertIsNone(wait_call["appserver_crossbind"])
        self.assertEqual(
            wait_call["appserver_delivery"],
            {
                "kind": gate_module.PROVIDER_GATE_DELIVERY_SUPPRESSED_WAIT,
                "successor_call_id": successor_call["call_id"],
                "successor_response_id": successor_call["response_id"],
                "bind_unix_ns": wait_call["appserver_delivery"]["bind_unix_ns"],
                "bind_monotonic_ns": wait_call["appserver_delivery"][
                    "bind_monotonic_ns"
                ],
            },
        )
        manifest = wait_call["response_output_manifest"]
        self.assertEqual(
            set(manifest), gate_module.PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_KEYS
        )
        self.assertEqual(manifest["output_item_count"], 2)
        self.assertEqual(manifest["action_capable_item_count"], 1)
        self.assertEqual(
            manifest["items"][1]["wait_timeout_ms"], 3_600_000
        )
        artifact_text = harness.gate.final_artifact_path.read_text()
        self.assertNotIn("PRIVATE-REASONING-JOB-1508245", artifact_text)
        self.assertNotIn('{"timeout_ms":3600000}', artifact_text)
        self.assertEqual(
            validate_artifact(harness.gate.final_artifact_path), artifact
        )
        mutations = (
            (
                "manifest-timeout",
                lambda value: value["calls"][0]["response_output_manifest"][
                    "items"
                ][1].__setitem__("wait_timeout_ms", 9_999),
            ),
            (
                "suppressed-successor",
                lambda value: value["calls"][0]["appserver_delivery"].__setitem__(
                    "successor_response_id", "not-the-successor"
                ),
            ),
            (
                "direct-bind-clock",
                lambda value: value["calls"][1]["appserver_delivery"].__setitem__(
                    "bind_monotonic_ns",
                    value["calls"][1]["appserver_delivery"][
                        "bind_monotonic_ns"
                    ]
                    + 1,
                ),
            ),
        )
        for label, mutate in mutations:
            with self.subTest(forgery=label):
                forged = json.loads(json.dumps(artifact))
                mutate(forged)
                reseal_provider_gate_record(forged)
                forged_path = harness.root / f"forged-job-1508245-{label}.json"
                forged_path.write_text(
                    json.dumps(forged, sort_keys=True, separators=(",", ":"))
                    + "\n"
                )
                forged_path.chmod(0o444)
                with self.assertRaises(ProviderGateValidationError):
                    validate_artifact(forged_path)

    def test_live_extended_wait_shape_is_reconciled_without_persisting_sidecars(
        self,
    ) -> None:
        usage = provider_usage(40, output=10)
        encrypted_arg = "x" * 160
        wait_body = collaboration_wait_sse(
            "wait-live-extended",
            usage,
            timeout_ms=3_600_000,
            function_call_extra_fields={
                "encrypted_function_args": [encrypted_arg],
            },
            omit_status=True,
        )
        successor_id = "successor-live-extended"
        harness = GateHarness(
            self,
            [
                FakePlan(wait_body),
                FakePlan(completed_sse(successor_id, usage)),
            ],
            token_limit=500,
            response_bound=100,
        )
        self.addCleanup(harness.cleanup)

        self.assertEqual(harness.post()[0], 200)
        self.assertEqual(harness.post()[0], 200)
        harness.crossbind(successor_id, usage, 2)
        candidates = harness.gate.suppressed_collaboration_wait_candidates(
            ROOT, "turn-1"
        )
        self.assertEqual(len(candidates), 1)
        self.assertEqual(candidates[0]["wait_timeout_ms"], 3_600_000)
        harness.gate.crossbind_suppressed_collaboration_wait(
            "wait-live-extended",
            ROOT,
            "turn-1",
            successor_id,
        )
        artifact = harness.finish(CLOSE_REASON_ACCEPTED_SUBMISSION)
        self.assertEqual(
            artifact["calls"][0]["response_output_manifest"]["items"][1][
                "wait_timeout_ms"
            ],
            3_600_000,
        )
        artifact_text = harness.gate.final_artifact_path.read_text()
        self.assertNotIn(encrypted_arg, artifact_text)

        base = {
            "type": "function_call",
            "id": "fc-live-wait",
            "status": "completed",
            "call_id": "call-live-wait",
            "name": "wait_agent",
            "namespace": "collaboration",
            "arguments": '{"timeout_ms":3600000}',
        }
        self.assertEqual(
            gate_module._wait_agent_timeout_ms(
                {**base, "encrypted_function_args": ["encrypted"]}
            ),
            3_600_000,
        )
        self.assertEqual(
            gate_module._wait_agent_timeout_ms(
                {
                    **base,
                    "internal_chat_message_metadata_passthrough": {
                        "turn_id": "turn-live"
                    },
                }
            ),
            3_600_000,
        )
        without_status = dict(base)
        without_status.pop("status")
        self.assertEqual(
            gate_module._wait_agent_timeout_ms(
                {
                    **without_status,
                    "encrypted_function_args": [],
                    "internal_chat_message_metadata_passthrough": {},
                }
            ),
            3_600_000,
        )
        self.assertEqual(
            gate_module._wait_agent_timeout_ms(
                {
                    **without_status,
                    "encrypted_function_args": ["one", "two"],
                }
            ),
            3_600_000,
        )

    def test_live_extended_wait_shape_checks_semantics_not_opaque_envelope(
        self,
    ) -> None:
        base: dict[str, object] = {
            "type": "function_call",
            "id": "fc-live-wait",
            "status": "completed",
            "call_id": "call-live-wait",
            "name": "wait_agent",
            "namespace": "collaboration",
            "arguments": '{"timeout_ms":3600000}',
        }
        self.assertEqual(
            gate_module._wait_agent_timeout_ms(
                {
                    **base,
                    "encrypted_function_args": {"new_provider_shape": True},
                    "internal_chat_message_metadata_passthrough": ["opaque"],
                    "future_ignored_envelope_field": {"value": 1},
                }
            ),
            3_600_000,
        )
        cases: dict[str, dict[str, object]] = {
            "bad-status": {**base, "status": "in_progress"},
            "wrong-type": {**base, "type": "custom_tool_call"},
            "wrong-name": {**base, "name": "send_message"},
            "wrong-namespace": {**base, "namespace": "functions"},
            "empty-id": {**base, "id": ""},
            "empty-call-id": {**base, "call_id": ""},
            "wrong-arguments": {**base, "arguments": '{"timeout_ms":1}'},
        }
        for label, item in cases.items():
            with self.subTest(label=label):
                self.assertIsNone(gate_module._wait_agent_timeout_ms(item))

    def test_suppressed_wait_rejects_output_mismatch_and_inexact_waits(self) -> None:
        usage = provider_usage(40, output=10)
        message_item: dict[str, object] = {
            "type": "message",
            "id": "msg-not-wait-only",
            "status": "completed",
            "role": "assistant",
            "content": [],
        }
        exact_items = [
            {
                "type": "function_call",
                "id": "fc-mismatch",
                "status": "completed",
                "call_id": "call-mismatch",
                "name": "wait_agent",
                "namespace": "collaboration",
                "arguments": '{"timeout_ms":30000}',
            }
        ]
        mismatch = GateHarness(
            self,
            [
                FakePlan(
                    output_items_completed_sse(
                        "resp-output-mismatch",
                        usage,
                        exact_items,
                        completed_output=[message_item],
                    )
                )
            ],
            token_limit=500,
            response_bound=100,
        )
        try:
            self.assertEqual(mismatch.post()[0], 502)
            self.assertEqual(mismatch.gate.snapshot()["phase"], PHASE_POISONED)
            mismatch.finish()
        finally:
            mismatch.cleanup()

        cases = {
            "message-output": collaboration_wait_sse(
                "wait-message", usage, extra_output_items=[message_item]
            ),
            "wrong-namespace": collaboration_wait_sse(
                "wait-namespace", usage, namespace="other"
            ),
            "extra-argument": collaboration_wait_sse(
                "wait-extra-arg", usage, extra_arguments={"extra": True}
            ),
            "timeout-bool": collaboration_wait_sse(
                "wait-bool", usage, timeout_ms=True
            ),
            "timeout-below-bound": collaboration_wait_sse(
                "wait-short", usage, timeout_ms=9_999
            ),
        }
        for label, body in cases.items():
            with self.subTest(label=label):
                successor_id = f"successor-{label}"
                harness = GateHarness(
                    self,
                    [
                        FakePlan(body),
                        FakePlan(completed_sse(successor_id, usage)),
                    ],
                    token_limit=500,
                    response_bound=100,
                )
                try:
                    self.assertEqual(harness.post()[0], 200)
                    self.assertEqual(harness.post()[0], 200)
                    harness.crossbind(successor_id, usage, 2)
                    self.assertEqual(
                        harness.gate.suppressed_collaboration_wait_candidates(
                            ROOT, "turn-1"
                        ),
                        [],
                    )
                    response_id = json.loads(
                        body.decode().split("event: response.completed\ndata: ", 1)[1]
                    )["response"]["id"]
                    with self.assertRaisesRegex(
                        ProviderGateError, "eligible exact collaboration wait"
                    ):
                        harness.gate.crossbind_suppressed_collaboration_wait(
                            response_id, ROOT, "turn-1", successor_id
                        )
                    self.assertEqual(
                        harness.gate.snapshot()["phase"], PHASE_POISONED
                    )
                    harness.finish()
                finally:
                    harness.cleanup()

    def test_multiple_suppressed_waits_require_a_later_direct_successor(self) -> None:
        usage = provider_usage(40, output=10)
        harness = GateHarness(
            self,
            [
                FakePlan(collaboration_wait_sse("wait-one", usage)),
                FakePlan(collaboration_wait_sse("wait-two", usage)),
                FakePlan(completed_sse("direct-successor", usage)),
            ],
            token_limit=1_000,
            response_bound=100,
        )
        self.addCleanup(harness.cleanup)
        self.assertEqual(harness.post()[0], 200)
        self.assertEqual(harness.post()[0], 200)
        self.assertEqual(
            harness.gate.suppressed_collaboration_wait_candidates(
                ROOT, "turn-1"
            ),
            [],
        )
        self.assertEqual(harness.post()[0], 200)
        harness.crossbind("direct-successor", usage, 3)
        candidates = harness.gate.suppressed_collaboration_wait_candidates(
            ROOT, "turn-1"
        )
        self.assertEqual(
            [candidate["response_id"] for candidate in candidates],
            ["wait-one", "wait-two"],
        )
        for response_id in ("wait-one", "wait-two"):
            harness.gate.crossbind_suppressed_collaboration_wait(
                response_id, ROOT, "turn-1", "direct-successor"
            )
        artifact = harness.finish(CLOSE_REASON_NATURAL_END)
        self.assertFalse(artifact["state"]["poisoned"])
        self.assertEqual(
            [
                call["appserver_delivery"]["kind"]
                for call in artifact["calls"]
            ],
            [
                gate_module.PROVIDER_GATE_DELIVERY_SUPPRESSED_WAIT,
                gate_module.PROVIDER_GATE_DELIVERY_SUPPRESSED_WAIT,
                gate_module.PROVIDER_GATE_DELIVERY_DIRECT,
            ],
        )

    def test_six_job_shaped_responses_form_a_superseded_message_chain(self) -> None:
        """Six same-turn responses may reconcile through immediate successors."""

        usage = provider_usage(40, output=10)
        response_ids = [f"job-shaped-response-{index}" for index in range(1, 7)]
        plans = []
        for index, response_id in enumerate(response_ids, 1):
            plans.append(
                FakePlan(
                    output_items_completed_sse(
                        response_id,
                        usage,
                        [
                            {
                                "type": "reasoning",
                                "id": f"reasoning-{index}",
                                "status": "completed",
                                "summary": [],
                            },
                            {
                                "type": "function_call",
                                "id": f"function-{index}",
                                "status": "completed",
                                "call_id": f"collaboration-call-{index}",
                                "name": "send_message",
                                "namespace": "collaboration",
                                "arguments": '{"message":"opaque","target":"child"}',
                            },
                        ],
                    )
                )
            )
        harness = GateHarness(
            self, plans, token_limit=2_000, response_bound=100
        )
        self.addCleanup(harness.cleanup)

        for _response_id in response_ids:
            status, _body, _headers = harness.post()
            self.assertEqual(status, 200)
        harness.crossbind(response_ids[-1], usage, 6)

        candidates = harness.gate.superseded_by_collaboration_message_candidates(
            ROOT, "turn-1"
        )
        self.assertEqual(
            [candidate["response_id"] for candidate in candidates],
            response_ids[:-1],
        )
        self.assertTrue(
            all(
                set(candidate)
                == gate_module.PROVIDER_GATE_SUPERSEDED_COLLABORATION_MESSAGE_CANDIDATE_KEYS
                and candidate["action_capable_item_count"] == 1
                and candidate["successor_response_id"] == response_ids[index + 1]
                and candidate["commit_monotonic_ns"]
                < candidate["successor_admitted_monotonic_ns"]
                for index, candidate in enumerate(candidates)
            )
        )
        for response_id, successor_id in zip(response_ids, response_ids[1:]):
            harness.gate.crossbind_superseded_by_collaboration_message(
                response_id, ROOT, "turn-1", successor_id
            )

        artifact = harness.finish(CLOSE_REASON_ACCEPTED_SUBMISSION)
        self.assertEqual(artifact["state"]["completed_tokens"], 240)
        self.assertEqual(
            [call["appserver_delivery"]["kind"] for call in artifact["calls"]],
            [
                gate_module.PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE
            ]
            * 5
            + [gate_module.PROVIDER_GATE_DELIVERY_DIRECT],
        )
        self.assertTrue(
            all(
                call["appserver_crossbind"] is None
                for call in artifact["calls"][:-1]
            )
        )
        self.assertEqual(
            validate_artifact(harness.gate.final_artifact_path), artifact
        )

        forged = json.loads(json.dumps(artifact))
        latest = forged["calls"][-1]
        latest["appserver_crossbind"] = None
        latest["appserver_delivery"]["kind"] = (
            gate_module.PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE
        )
        latest["appserver_delivery"]["successor_call_id"] = forged["calls"][0][
            "call_id"
        ]
        latest["appserver_delivery"]["successor_response_id"] = forged["calls"][
            0
        ]["response_id"]
        reseal_provider_gate_record(forged)
        forged_path = harness.root / "forged-superseded-latest.json"
        forged_path.write_text(
            json.dumps(forged, sort_keys=True, separators=(",", ":")) + "\n",
            encoding="utf-8",
        )
        forged_path.chmod(0o444)
        with self.assertRaises(ProviderGateValidationError):
            validate_artifact(forged_path)

    def test_superseded_message_chain_may_end_through_suppressed_wait(self) -> None:
        """An authenticated wait is a bridge from its predecessor to direct delivery."""

        usage = provider_usage(40, output=10)
        source = output_items_completed_sse(
            "mixed-source",
            usage,
            [
                {
                    "type": "reasoning",
                    "id": "mixed-source-reasoning",
                    "status": "completed",
                    "summary": [],
                },
                {
                    "type": "function_call",
                    "id": "mixed-source-function",
                    "status": "completed",
                    "call_id": "mixed-source-collaboration-call",
                    "name": "send_message",
                    "namespace": "collaboration",
                    "arguments": '{"message":"opaque","target":"child"}',
                },
            ],
        )
        harness = GateHarness(
            self,
            [
                FakePlan(source),
                FakePlan(collaboration_wait_sse("mixed-wait", usage)),
                FakePlan(completed_sse("mixed-direct", usage)),
            ],
            token_limit=1_000,
            response_bound=100,
        )
        self.addCleanup(harness.cleanup)

        for _ in range(3):
            self.assertEqual(harness.post()[0], 200)
        harness.crossbind("mixed-direct", usage, 3)
        harness.gate.crossbind_suppressed_collaboration_wait(
            "mixed-wait", ROOT, "turn-1", "mixed-direct"
        )
        candidates = harness.gate.superseded_by_collaboration_message_candidates(
            ROOT, "turn-1"
        )
        self.assertEqual(
            [
                (item["response_id"], item["successor_response_id"])
                for item in candidates
            ],
            [("mixed-source", "mixed-wait")],
        )
        harness.gate.crossbind_superseded_by_collaboration_message(
            "mixed-source", ROOT, "turn-1", "mixed-wait"
        )

        artifact = harness.finish(CLOSE_REASON_ACCEPTED_SUBMISSION)
        self.assertEqual(
            [call["appserver_delivery"]["kind"] for call in artifact["calls"]],
            [
                gate_module.PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE,
                gate_module.PROVIDER_GATE_DELIVERY_SUPPRESSED_WAIT,
                gate_module.PROVIDER_GATE_DELIVERY_DIRECT,
            ],
        )
        self.assertEqual(
            validate_artifact(harness.gate.final_artifact_path), artifact
        )

        skipped_wait = json.loads(json.dumps(artifact))
        skipped_wait["calls"][0]["appserver_delivery"].update(
            {
                "successor_call_id": skipped_wait["calls"][2]["call_id"],
                "successor_response_id": skipped_wait["calls"][2][
                    "response_id"
                ],
            }
        )
        reseal_provider_gate_record(skipped_wait)
        skipped_path = harness.root / "forged-mixed-chain-skips-wait.json"
        skipped_path.write_text(
            json.dumps(skipped_wait, sort_keys=True, separators=(",", ":"))
            + "\n",
            encoding="utf-8",
        )
        skipped_path.chmod(0o444)
        with self.assertRaisesRegex(
            ProviderGateValidationError, "skipped its immediate successor"
        ):
            validate_artifact(skipped_path)

        non_direct_wait_successor = json.loads(json.dumps(artifact))
        final_delivery = non_direct_wait_successor["calls"][2][
            "appserver_delivery"
        ]
        final_delivery.update(
            {
                "kind": gate_module.PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE,
                "successor_call_id": non_direct_wait_successor["calls"][1][
                    "call_id"
                ],
                "successor_response_id": non_direct_wait_successor["calls"][1][
                    "response_id"
                ],
            }
        )
        non_direct_wait_successor["calls"][2]["appserver_crossbind"] = None
        reseal_provider_gate_record(non_direct_wait_successor)
        non_direct_path = harness.root / "forged-mixed-chain-nondirect-wait.json"
        non_direct_path.write_text(
            json.dumps(
                non_direct_wait_successor,
                sort_keys=True,
                separators=(",", ":"),
            )
            + "\n",
            encoding="utf-8",
        )
        non_direct_path.chmod(0o444)
        with self.assertRaises(ProviderGateValidationError):
            validate_artifact(non_direct_path)

    def test_superseded_message_requires_an_immediate_exact_metadata_successor(
        self,
    ) -> None:
        usage = provider_usage(40, output=10)
        cases = (
            ("no-successor", [FakePlan(completed_sse("source-only", usage))]),
            (
                "wrong-metadata",
                [
                    FakePlan(completed_sse("source-wrong-metadata", usage)),
                    FakePlan(completed_sse("different-session", usage)),
                ],
            ),
        )
        for label, plans in cases:
            with self.subTest(label=label):
                harness = GateHarness(
                    self, plans, token_limit=500, response_bound=100
                )
                try:
                    self.assertEqual(harness.post()[0], 200)
                    source_id = (
                        "source-only"
                        if label == "no-successor"
                        else "source-wrong-metadata"
                    )
                    successor_id = "missing-successor"
                    if label == "wrong-metadata":
                        self.assertEqual(
                            harness.post(session_id="different-session-id")[0],
                            200,
                        )
                        harness.crossbind("different-session", usage, 2)
                        successor_id = "different-session"
                    self.assertEqual(
                        harness.gate.superseded_by_collaboration_message_candidates(
                            ROOT, "turn-1"
                        ),
                        [],
                    )
                    with self.assertRaisesRegex(
                        ProviderGateError, "immediate later same-metadata response"
                    ):
                        harness.gate.crossbind_superseded_by_collaboration_message(
                            source_id, ROOT, "turn-1", successor_id
                        )
                    self.assertEqual(
                        harness.gate.snapshot()["phase"], PHASE_POISONED
                    )
                    harness.finish()
                finally:
                    harness.cleanup()

    def test_superseded_message_cannot_be_crossing_or_terminal_boundary(self) -> None:
        usage = provider_usage(40, output=10)
        boundary = GateHarness(
            self,
            [
                FakePlan(completed_sse("boundary-source", usage)),
                FakePlan(completed_sse("boundary-latest", usage)),
            ],
            token_limit=500,
            response_bound=100,
        )
        try:
            self.assertEqual(boundary.post()[0], 200)
            self.assertEqual(boundary.post()[0], 200)
            boundary.gate.crossbind_superseded_by_collaboration_message(
                "boundary-source", ROOT, "turn-1", "boundary-latest"
            )
            close = boundary.gate.close(CLOSE_REASON_NATURAL_END)
            self.assertFalse(close["won"])
            self.assertEqual(boundary.gate.snapshot()["phase"], PHASE_POISONED)
            boundary.finish()
        finally:
            boundary.cleanup()

        crossing_usage = provider_usage(110, output=10)
        crossing = GateHarness(
            self,
            [FakePlan(completed_sse("crossing-response", crossing_usage))],
            token_limit=100,
            response_bound=272,
        )
        try:
            self.assertEqual(crossing.post()[0], 200)
            self.assertEqual(
                crossing.gate.superseded_by_collaboration_message_candidates(
                    ROOT, "turn-1"
                ),
                [],
            )
            with self.assertRaisesRegex(
                ProviderGateError,
                "not eligible to be superseded by a collaboration message",
            ):
                crossing.gate.crossbind_superseded_by_collaboration_message(
                    "crossing-response",
                    ROOT,
                    "turn-1",
                    "impossible-successor",
                )
            self.assertEqual(crossing.gate.snapshot()["phase"], PHASE_POISONED)
        finally:
            crossing.cleanup()

    def test_job_1508105_absent_content_type_is_strictly_authenticated(self) -> None:
        """Regression for the missing-header failure shape from prep job 1508105."""

        usage = provider_usage(90, cached=70)
        upstream = completed_sse("resp-job-1508105", usage, tool_frame=True)
        plan = FakePlan(upstream, content_type=None, content_encoding=None)
        harness = GateHarness(
            self, [plan], token_limit=500, response_bound=100
        )
        self.addCleanup(harness.cleanup)

        status, body, response_headers = harness.post()
        self.assertEqual(status, 200)
        self.assertEqual(body, upstream)
        self.assertEqual(response_headers["content-type"], "text/event-stream")
        self.assertEqual(response_headers["content-encoding"], "identity")
        self.assertIsNotNone(plan.request)
        assert plan.request is not None
        outbound = plan.request[1]["headers"]
        self.assertEqual(outbound["Accept"], "text/event-stream")
        self.assertEqual(outbound["Accept-Encoding"], "identity")
        self.assertNotIn("accept", {name.lower() for name in outbound if name != "Accept"})

        harness.crossbind("resp-job-1508105", usage, 1)
        artifact = harness.finish(CLOSE_REASON_NATURAL_END)
        self.assertEqual(
            artifact["schema_version"], gate_module.PROVIDER_GATE_SCHEMA_VERSION
        )
        self.assertEqual(
            artifact["protocol"], gate_module.PROVIDER_GATE_PROTOCOL
        )
        self.assertEqual(
            artifact["implementation"]["version"],
            gate_module.PROVIDER_GATE_IMPLEMENTATION_VERSION,
        )
        self.assertEqual(
            artifact["configuration"]["upstream_response_contract"],
            {
                "schema_version": 1,
                "protocol": "highambench-responses-sse-envelope-v1",
                "success_status": 200,
                "content_type_policy": (
                    "absent_or_single_text_event_stream_optional_utf8_charset"
                ),
                "content_encoding_policy": "absent_or_single_identity",
                "outbound_accept": "text/event-stream",
                "parser": "highambench-strict-responses-sse-v2",
                "downstream_content_type": "text/event-stream",
                "downstream_content_encoding": "identity",
            },
        )
        call = artifact["calls"][0]
        self.assertEqual(call["upstream_content_type_occurrences"], 0)
        self.assertIsNone(call["upstream_content_type"])
        self.assertEqual(call["upstream_content_encoding_occurrences"], 0)
        self.assertIsNone(call["upstream_content_encoding"])
        authentication = call["upstream_sse_authentication"]
        self.assertEqual(set(authentication), gate_module.PROVIDER_GATE_SSE_AUTHENTICATION_KEYS)
        self.assertEqual(
            authentication["content_type_basis"],
            "authenticated_stream_request_header_absent",
        )
        self.assertEqual(
            authentication["content_encoding_basis"],
            "implicit_identity_header_absent",
        )
        self.assertIs(authentication["downstream_content_type_synthesized"], True)
        self.assertEqual(authentication["body_sha256"], hashlib.sha256(upstream).hexdigest())
        self.assertEqual(authentication["body_bytes"], len(upstream))
        self.assertEqual(authentication["response_id"], "resp-job-1508105")
        self.assertEqual(authentication["completed_event_index"], 1)
        self.assertEqual(authentication["json_event_count"], 2)
        self.assertEqual(authentication["done_count"], 0)
        self.assertNotIn(upstream.decode("utf-8"), harness.gate.final_artifact_path.read_text())
        self.assertEqual(validate_artifact(harness.gate.final_artifact_path), artifact)

    def test_declared_headers_and_header_rejections_are_occurrence_exact(self) -> None:
        usage = provider_usage(40)
        accepted_plan = FakePlan(
            completed_sse("declared-headers", usage),
            content_type='Text/Event-Stream; charset="UTF-8"',
            content_encoding="Identity",
        )
        accepted = GateHarness(
            self, [accepted_plan], token_limit=500, response_bound=100
        )
        self.addCleanup(accepted.cleanup)
        self.assertEqual(accepted.post()[0], 200)
        accepted.crossbind("declared-headers", usage, 1)
        accepted_artifact = accepted.finish(CLOSE_REASON_NATURAL_END)
        accepted_call = accepted_artifact["calls"][0]
        self.assertEqual(accepted_call["upstream_content_type_occurrences"], 1)
        self.assertEqual(
            accepted_call["upstream_content_type"],
            'Text/Event-Stream; charset="UTF-8"',
        )
        self.assertEqual(accepted_call["upstream_content_encoding_occurrences"], 1)
        self.assertEqual(accepted_call["upstream_content_encoding"], "Identity")
        self.assertEqual(
            accepted_call["upstream_sse_authentication"]["content_type_basis"],
            "declared_text_event_stream",
        )
        self.assertEqual(
            accepted_call["upstream_sse_authentication"]["content_encoding_basis"],
            "declared_identity",
        )
        self.assertIs(
            accepted_call["upstream_sse_authentication"][
                "downstream_content_type_synthesized"
            ],
            False,
        )
        authentication_mutations = (
            ("schema-v2", lambda value: value.__setitem__("schema_version", 2)),
            (
                "protocol-v2",
                lambda value: value.__setitem__(
                    "protocol", "highambench-provider-token-gate-v2"
                ),
            ),
            (
                "implementation-v2",
                lambda value: value["implementation"].__setitem__("version", "2"),
            ),
            (
                "missing-contract",
                lambda value: value["configuration"].pop(
                    "upstream_response_contract"
                ),
            ),
            (
                "extra-auth-field",
                lambda value: value["calls"][0]["upstream_sse_authentication"].__setitem__(
                    "extra", True
                ),
            ),
            (
                "incomplete-auth",
                lambda value: value["calls"][0]["upstream_sse_authentication"].__setitem__(
                    "complete", False
                ),
            ),
            (
                "wrong-auth-basis",
                lambda value: value["calls"][0]["upstream_sse_authentication"].__setitem__(
                    "content_type_basis",
                    "authenticated_stream_request_header_absent",
                ),
            ),
            (
                "wrong-event-index",
                lambda value: value["calls"][0]["upstream_sse_authentication"].__setitem__(
                    "completed_event_index", 99
                ),
            ),
            (
                "wrong-body-hash",
                lambda value: value["calls"][0]["upstream_sse_authentication"].__setitem__(
                    "body_sha256", "0" * 64
                ),
            ),
            (
                "wrong-occurrences",
                lambda value: value["calls"][0].__setitem__(
                    "upstream_content_type_occurrences", 0
                ),
            ),
        )
        for label, mutate in authentication_mutations:
            with self.subTest(label=label):
                forged = json.loads(json.dumps(accepted_artifact))
                mutate(forged)
                reseal_provider_gate_record(forged)
                forged_path = accepted.root / f"forged-v3-{label}.json"
                forged_path.write_text(
                    json.dumps(forged, sort_keys=True, separators=(",", ":"))
                    + "\n"
                )
                forged_path.chmod(0o444)
                with self.assertRaises(ProviderGateValidationError):
                    validate_artifact(forged_path)

        rejected = (
            ("status", {"status": 201}, 1, 1),
            ("empty-type", {"content_type": ""}, 1, 1),
            ("wrong-type", {"content_type": "application/json"}, 1, 1),
            (
                "type-parameter",
                {"content_type": "text/event-stream; boundary=no"},
                1,
                1,
            ),
            (
                "duplicate-type",
                {"content_types": ["text/event-stream", "text/event-stream"]},
                2,
                1,
            ),
            ("empty-encoding", {"content_encoding": ""}, 1, 1),
            ("gzip", {"content_encoding": "gzip"}, 1, 1),
            (
                "duplicate-encoding",
                {"content_encodings": ["identity", "identity"]},
                1,
                2,
            ),
        )
        for label, options, expected_type_count, expected_encoding_count in rejected:
            with self.subTest(label=label):
                plan = FakePlan(completed_sse(f"reject-{label}", usage), **options)
                harness = GateHarness(
                    self, [plan], token_limit=500, response_bound=100
                )
                self.addCleanup(harness.cleanup)
                status, _body, _headers = harness.post()
                self.assertEqual(status, 502)
                artifact = harness.finish()
                call = artifact["calls"][0]
                self.assertEqual(
                    call["upstream_content_type_occurrences"], expected_type_count
                )
                self.assertEqual(
                    call["upstream_content_encoding_occurrences"],
                    expected_encoding_count,
                )
                self.assertIsNone(call["upstream_sse_authentication"])
                self.assertIsNone(call["normalized_usage"])
                if expected_type_count != 1:
                    self.assertIsNone(call["upstream_content_type"])
                if expected_encoding_count != 1:
                    self.assertIsNone(call["upstream_content_encoding"])
                self.assertEqual(
                    validate_artifact(harness.gate.final_artifact_path), artifact
                )

    def test_strict_sse_parser_accepts_only_complete_authenticated_envelopes(self) -> None:
        usage = provider_usage(40)
        response_id = "strict-response"
        created = {
            "type": "response.created",
            "response": {"id": response_id},
        }
        completed = {
            "type": "response.completed",
            "response": {"id": response_id, "usage": usage, "output": []},
        }

        def frame(event: dict[str, object], *, event_name: str | None = None) -> bytes:
            name = event_name if event_name is not None else str(event["type"])
            return (
                f"event: {name}\ndata: "
                + json.dumps(event, separators=(",", ":"))
                + "\n\n"
            ).encode("utf-8")

        valid = (
            b": keepalive\r\nid: stream-1\r\nretry: 1000\r\n\r\n"
            + frame(created).replace(b"\n", b"\r\n")
            + frame(completed).replace(b"\n", b"\r\n")
            + b"data: [DONE]\r\n\r\n"
        )
        parsed = gate_module._parse_sse_completed(valid)
        self.assertEqual(parsed[0], response_id)
        self.assertEqual(parsed[2]["total_tokens"], 40)
        self.assertEqual(parsed[5], {
            "json_event_count": 2,
            "completed_event_index": 1,
            "done_count": 1,
        })

        completion = frame(completed)
        other = frame({"type": "response.created", "response": {"id": response_id}})
        adversarial = {
            "invalid-utf8": b"\xff\n\n",
            "bom": b"\xef\xbb\xbf" + completion,
            "nul": b": bad\x00comment\n\n" + completion,
            "bare-cr": completion.replace(b"\n", b"\r"),
            "unterminated": completion[:-1],
            "unknown-field": b"unknown: value\n\n" + completion,
            "duplicate-event": (
                b"event: response.completed\nevent: response.completed\ndata: "
                + json.dumps(completed, separators=(",", ":")).encode()
                + b"\n\n"
            ),
            "duplicate-id": b"id: one\nid: two\n\n" + completion,
            "duplicate-retry": b"retry: 1\nretry: 2\n\n" + completion,
            "invalid-retry": b"retry: 1.5\n\n" + completion,
            "event-without-data": b"event: response.created\n\n" + completion,
            "event-type-mismatch": frame(completed, event_name="response.created"),
            "malformed-json": b"event: response.completed\ndata: {\n\n",
            "duplicate-json-key": (
                b'event: response.completed\ndata: {"type":"response.completed",'
                b'"type":"response.completed"}\n\n'
            ),
            "nonfinite-json": (
                b'event: response.completed\ndata: {"type":"response.completed",'
                b'"value":NaN}\n\n'
            ),
            "nonobject-json": b"event: response.completed\ndata: []\n\n",
            "done-before-completed": b"data: [DONE]\n\n" + completion,
            "duplicate-done": completion + b"data: [DONE]\n\ndata: [DONE]\n\n",
            "event-after-completed": completion + other,
            "control-after-completed": completion + b"id: late\n\n",
            "comment-after-done": completion + b"data: [DONE]\n\n: late\n\n",
            "failed-event": frame({"type": "response.failed"}) + completion,
            "incomplete-event": frame({"type": "response.incomplete"}) + completion,
            "error-event": frame({"type": "error"}) + completion,
            "missing-completion": other,
            "conflicting-response-id": frame(
                {"type": "response.created", "response": {"id": "other"}}
            ) + completion,
            "missing-usage": frame(
                {
                    "type": "response.completed",
                    "response": {"id": response_id},
                }
            ),
            "failed-completion": frame(
                {
                    "type": "response.completed",
                    "response": {
                        "id": response_id,
                        "status": "failed",
                        "usage": usage,
                    },
                }
            ),
        }
        for label, body in adversarial.items():
            with self.subTest(label=label), self.assertRaises(ProviderGateError):
                gate_module._parse_sse_completed(body)

    def test_job_1509078_empty_completed_output_uses_done_message_manifest(self) -> None:
        """Regression for the complete done item plus empty final output shape."""

        usage = provider_usage(40)
        response_id = "resp-job-1509078"
        message_item: dict[str, object] = {
            "type": "message",
            "id": "msg-job-1509078",
            "status": "completed",
            "role": "assistant",
            "content": [
                {
                    "type": "output_text",
                    "annotations": [],
                    "logprobs": [],
                    "text": "I will inspect the target.",
                }
            ],
        }
        upstream = output_items_completed_sse(
            response_id,
            usage,
            [message_item],
            completed_output=[],
        )
        parsed = gate_module._parse_sse_completed(upstream)
        self.assertEqual(parsed[0], response_id)
        self.assertEqual(parsed[3]["response"]["output"], [])
        manifest = parsed[6]
        self.assertEqual(manifest["output_item_count"], 1)
        self.assertEqual(manifest["action_capable_item_count"], 0)
        self.assertEqual(manifest["items"][0]["type"], "message")
        self.assertEqual(manifest["items"][0]["id"], "msg-job-1509078")

        harness = GateHarness(
            self,
            [FakePlan(upstream)],
            token_limit=500,
            response_bound=100,
        )
        try:
            status, body, _headers = harness.post()
            self.assertEqual(status, 200)
            self.assertEqual(body, upstream)
            harness.crossbind(response_id, usage, 1)
            artifact = harness.finish(CLOSE_REASON_NATURAL_END)
            call = artifact["calls"][0]
            self.assertEqual(call["response_output_manifest"], manifest)
            self.assertEqual(
                call["upstream_sse_authentication"]["parser"],
                "highambench-strict-responses-sse-v2",
            )
            self.assertEqual(
                validate_artifact(harness.gate.final_artifact_path), artifact
            )
        finally:
            harness.cleanup()

    def test_nonempty_completed_output_cannot_hide_done_action(self) -> None:
        usage = provider_usage(40)
        action_item: dict[str, object] = {
            "type": "function_call",
            "id": "fc-visible-action",
            "status": "completed",
            "call_id": "call-visible-action",
            "name": "exec",
            "arguments": '{"command":"true"}',
        }
        benign_message: dict[str, object] = {
            "type": "message",
            "id": "msg-hides-action",
            "status": "completed",
            "role": "assistant",
            "content": [],
        }
        upstream = output_items_completed_sse(
            "resp-action-hiding",
            usage,
            [action_item],
            completed_output=[benign_message],
        )
        with self.assertRaisesRegex(
            ProviderGateError,
            "response.completed output disagrees with output_item.done",
        ):
            gate_module._parse_sse_completed(upstream)

    def test_response_failed_code_diagnostic_is_safe_and_fail_closed(self) -> None:
        secret_message = "SECRET PROVIDER FAILURE BODY MUST NOT PERSIST"

        def failed_sse(code: object = None, *, include_code: bool = True) -> bytes:
            error: dict[str, object] = {"message": secret_message}
            if include_code:
                error["code"] = code
            event = {
                "type": "response.failed",
                "response": {"error": error},
            }
            return (
                "event: response.failed\ndata: "
                + json.dumps(event, separators=(",", ":"))
                + "\n\n"
            ).encode("utf-8")

        with self.assertRaisesRegex(
            ProviderGateError,
            r"event_type=response\.failed, code=server_error",
        ):
            gate_module._parse_sse_completed(failed_sse("server_error"))

        malformed_codes = (
            None,
            429,
            "",
            "contains spaces",
            "x"
            * (gate_module.PROVIDER_GATE_SSE_DIAGNOSTIC_TOKEN_MAX_LENGTH + 1),
            "unsafe\nvalue",
        )
        for code in malformed_codes:
            with self.subTest(code=code), self.assertRaisesRegex(
                ProviderGateError,
                r"event_type=response\.failed, code=unknown",
            ):
                gate_module._parse_sse_completed(failed_sse(code))
        with self.assertRaisesRegex(
            ProviderGateError,
            r"event_type=response\.failed, code=unknown",
        ):
            gate_module._parse_sse_completed(failed_sse(include_code=False))

        harness = GateHarness(
            self,
            [FakePlan(failed_sse("rate_limit_exceeded"))],
            token_limit=500,
            response_bound=100,
        )
        try:
            self.assertEqual(harness.post()[0], 502)
            artifact = harness.finish()
            reason = (
                "Responses SSE contains a failed response event "
                "(event_type=response.failed, code=rate_limit_exceeded)"
            )
            self.assertEqual(artifact["calls"][0]["error"], reason)
            self.assertIn(reason, artifact["state"]["poison_reasons"])
            self.assertNotIn(secret_message, harness.gate.final_artifact_path.read_text())
        finally:
            harness.cleanup()

    def test_generic_failure_event_diagnostics_are_safe(self) -> None:
        def frame(event: dict[str, object]) -> bytes:
            return (
                f"event: {event['type']}\ndata: "
                + json.dumps(event, separators=(",", ":"))
                + "\n\n"
            ).encode("utf-8")

        cases = (
            (
                {
                    "type": "error",
                    "code": "server_error",
                    "message": "SECRET TOP-LEVEL MESSAGE",
                },
                r"event_type=error, code=server_error",
            ),
            (
                {
                    "type": "response.incomplete",
                    "response": {
                        "error": {
                            "code": "rate_limit_exceeded",
                            "message": "SECRET NESTED MESSAGE",
                        },
                        "incomplete_details": {"reason": "max_output_tokens"},
                    },
                },
                (
                    r"event_type=response\.incomplete, code=rate_limit_exceeded, "
                    r"incomplete_reason=max_output_tokens"
                ),
            ),
            (
                {
                    "type": "response.incomplete",
                    "incomplete_details": {"reason": "unsafe reason"},
                    "response": {"error": {"code": ["not", "a", "string"]}},
                },
                (
                    r"event_type=response\.incomplete, code=unknown, "
                    r"incomplete_reason=unknown"
                ),
            ),
        )
        for event, expected in cases:
            with self.subTest(event_type=event["type"]), self.assertRaisesRegex(
                ProviderGateError, expected
            ):
                gate_module._parse_sse_completed(frame(event))

    def test_unknown_routes_compact_model_and_transport_are_denied_without_upstream(self) -> None:
        harness = GateHarness(self, [], token_limit=500, response_bound=100)
        self.addCleanup(harness.cleanup)
        wrong_nonce = "/" + "e" * 64 + gate_module.DEFAULT_UPSTREAM_BASE_PATH + "/responses"
        self.assertEqual(harness.post(path=wrong_nonce)[0], 404)
        self.assertEqual(harness.post(path=harness.url.path + "/responses/compact")[0], 422)
        self.assertEqual(harness.post(path=harness.url.path + "/other-inference")[0], 404)
        self.assertEqual(harness.post(model="gpt-5.6")[0], 422)
        self.assertEqual(harness.post(stream=False)[0], 422)
        self.assertEqual(harness.factory.count, 0)
        artifact = harness.finish(CLOSE_REASON_NATURAL_END)
        self.assertGreaterEqual(len(artifact["denials"]), 5)
        self.assertTrue(
            all(item["upstream_started"] is False for item in artifact["denials"])
        )

    def test_counted_route_rejects_unknown_or_empty_request_kind_before_upstream(self) -> None:
        for label, request_kind in (("unknown", "review"), ("empty", "")):
            with self.subTest(label=label):
                harness = GateHarness(
                    self, [], token_limit=500, response_bound=100
                )
                self.addCleanup(harness.cleanup)
                status, _body, _headers = harness.post(request_kind=request_kind)
                self.assertEqual(status, 422)
                self.assertEqual(harness.factory.count, 0)
                artifact = harness.finish(CLOSE_REASON_NATURAL_END)
                self.assertEqual(artifact["calls"], [])
                self.assertEqual(
                    artifact["denials"][0]["reason"],
                    "missing_or_unsupported_request_metadata",
                )
    def test_post_close_send_is_denied_and_forged_start_time_is_rejected(self) -> None:
        usage = provider_usage(40, cached=20)
        harness = GateHarness(
            self,
            [FakePlan(completed_sse("before-close", usage))],
            token_limit=500,
            response_bound=100,
        )
        self.addCleanup(harness.cleanup)
        self.assertEqual(harness.post()[0], 200)
        harness.crossbind("before-close", usage, 1)
        close_result = harness.gate.close(CLOSE_REASON_NATURAL_END)
        self.assertTrue(close_result["won"])
        self.assertEqual(harness.post()[0], 409)
        self.assertEqual(harness.factory.count, 1)
        artifact = harness.finish()
        self.assertTrue(artifact["state"]["no_post_close_upstream"])
        self.assertTrue(
            any(
                denial["reason"] == "provider_gate_closed"
                and denial["upstream_started"] is False
                for denial in artifact["denials"]
            )
        )

        forged = json.loads(json.dumps(artifact))
        terminal_time = min(
            transition["monotonic_ns"]
            for transition in forged["transitions"]
            if transition["to_phase"] in (PHASE_CLOSED, PHASE_POISONED)
        )
        forged["calls"][0]["upstream_start_monotonic_ns"] = terminal_time + 1
        unsigned = dict(forged)
        unsigned.pop("record_sha256")
        forged["record_sha256"] = hashlib.sha256(
            (
                json.dumps(
                    unsigned,
                    sort_keys=True,
                    separators=(",", ":"),
                    ensure_ascii=False,
                )
                + "\n"
            ).encode("utf-8")
        ).hexdigest()
        forged_path = harness.root / "forged.provider-token-gate.json"
        forged_path.write_text(
            json.dumps(forged, sort_keys=True, separators=(",", ":")) + "\n"
        )
        forged_path.chmod(0o444)
        with self.assertRaisesRegex(ProviderGateValidationError, "after gate close"):
            validate_artifact(forged_path)

    def test_accepted_submission_close_is_atomic_and_open_call_poisons(self) -> None:
        usage = provider_usage(40, cached=20)
        clean = GateHarness(
            self,
            [FakePlan(completed_sse("accepted-clean", usage))],
            token_limit=500,
            response_bound=100,
        )
        try:
            self.assertEqual(clean.post()[0], 200)
            clean.crossbind("accepted-clean", usage, 1)
            result = clean.gate.close_for_accepted_submission()
            self.assertTrue(result["won"])
            self.assertEqual(result["effective_reason"], CLOSE_REASON_ACCEPTED_SUBMISSION)
            artifact = clean.finish()
            self.assertEqual(
                artifact["state"]["close_reason"],
                CLOSE_REASON_ACCEPTED_SUBMISSION,
            )
        finally:
            clean.cleanup()

        release = threading.Event()
        raced = GateHarness(
            self,
            [FakePlan(completed_sse("accepted-race", usage), release=release)],
            token_limit=500,
            response_bound=100,
        )
        try:
            client = threading.Thread(target=raced.post)
            client.start()
            self.assertTrue(raced.factory.plans[0].started.wait(5.0))
            result = raced.gate.close_for_accepted_submission()
            self.assertFalse(result["won"])
            self.assertEqual(result["phase"], PHASE_POISONED)
            release.set()
            client.join(5.0)
            self.assertFalse(client.is_alive())
            artifact = raced.finish()
            self.assertTrue(artifact["state"]["poisoned"])
            self.assertIn(
                "accepted_submission_boundary_with_open_provider_request",
                artifact["state"]["poison_reasons"],
            )
        finally:
            raced.cleanup()

    def test_get_routes_never_reach_upstream_and_setup_ledger_stays_empty(self) -> None:
        harness = GateHarness(
            self,
            [],
            token_limit=500,
            response_bound=100,
            bind_prompt=False,
        )
        self.addCleanup(harness.cleanup)
        connection = http.client.HTTPConnection(harness.url.hostname, harness.url.port)
        try:
            connection.request("GET", harness.url.path + "/models")
            response = connection.getresponse()
            self.assertEqual(response.status, 404)
            response.read()
        finally:
            connection.close()
        harness.gate.bind_prompt_release(prompt_release())
        connection = http.client.HTTPConnection(harness.url.hostname, harness.url.port)
        try:
            connection.request("GET", harness.url.path + "/models")
            response = connection.getresponse()
            self.assertEqual(response.status, 404)
            response.read()
        finally:
            connection.close()
        artifact = harness.finish(CLOSE_REASON_NATURAL_END)
        self.assertEqual(harness.factory.count, 0)
        self.assertEqual(artifact["setup_requests"], [])
        self.assertEqual(len(artifact["denials"]), 2)
        self.assertTrue(
            all(
                denial["reason"] == "unknown_or_disallowed_route"
                and denial["upstream_started"] is False
                for denial in artifact["denials"]
            )
        )

    def test_malformed_usage_bound_violation_duplicate_and_disconnect_poison(self) -> None:
        malformed = provider_usage(50)
        malformed["total_tokens"] = 51
        oversized = provider_usage(101)
        duplicate_usage = provider_usage(40)
        cases = {
            "malformed": [FakePlan(completed_sse("bad-total", malformed))],
            "bound": [FakePlan(completed_sse("over-bound", oversized))],
            "disconnect": [
                FakePlan(b"", read_error=ConnectionResetError("test disconnect"))
            ],
        }
        for label, plans in cases.items():
            with self.subTest(label=label):
                harness = GateHarness(
                    self, plans, token_limit=500, response_bound=100
                )
                try:
                    self.assertEqual(harness.post()[0], 502)
                    self.assertEqual(harness.gate.snapshot()["phase"], PHASE_POISONED)
                    artifact = harness.finish()
                    self.assertTrue(artifact["state"]["poisoned"])
                finally:
                    harness.cleanup()

        plans = [
            FakePlan(completed_sse("duplicate", duplicate_usage)),
            FakePlan(completed_sse("duplicate", duplicate_usage)),
        ]
        harness = GateHarness(self, plans, token_limit=500, response_bound=100)
        try:
            self.assertEqual(harness.post()[0], 200)
            harness.crossbind("duplicate", duplicate_usage, 1)
            self.assertEqual(harness.post()[0], 502)
            self.assertEqual(harness.gate.snapshot()["phase"], PHASE_POISONED)
            artifact = harness.finish()
            self.assertIn("duplicate_response_id", artifact["state"]["poison_reasons"])
        finally:
            harness.cleanup()

    def test_duplicate_and_conflicting_appserver_crossbinds_poison(self) -> None:
        usage = provider_usage(40, cached=20)
        harness = GateHarness(
            self, [FakePlan(completed_sse("crossbind", usage))], token_limit=500, response_bound=100
        )
        self.addCleanup(harness.cleanup)
        self.assertEqual(harness.post()[0], 200)
        harness.crossbind("crossbind", usage, 1)
        with self.assertRaisesRegex(ProviderGateError, "twice"):
            harness.crossbind("crossbind", usage, 2)
        self.assertEqual(harness.gate.snapshot()["phase"], PHASE_POISONED)
        harness.finish()

        other = GateHarness(self, [], token_limit=500, response_bound=100)
        try:
            with self.assertRaisesRegex(ProviderGateError, "unknown"):
                other.gate.crossbind_appserver_response(
                    "unknown", appserver_usage(usage)
                )
            self.assertEqual(other.gate.snapshot()["phase"], PHASE_POISONED)
            other.finish()
        finally:
            other.cleanup()

    def test_prompt_release_identity_is_cross_bound_field_by_field(self) -> None:
        for field, bad_value in (
            ("root_thread_id", "other-root"),
            ("run_id", "other-run"),
            ("model", "other-model"),
            ("reasoning_effort", "high"),
        ):
            with self.subTest(field=field):
                with tempfile.TemporaryDirectory() as temporary:
                    root = Path(temporary)
                    gate = ProviderTokenGate(
                        root / "live",
                        root / "final",
                        token_limit=500,
                        response_bound=100,
                        model_catalog_sha256=CATALOG_SHA,
                        model_entry_sha256=ENTRY_SHA,
                        capability_nonce="d" * 64,
                        _connection_factory=FakeFactory([]),
                    )
                    gate.bind_root(
                        ROOT, run_id=RUN, model=MODEL, reasoning_effort=EFFORT
                    )
                    with self.assertRaisesRegex(ProviderGateError, field):
                        gate.bind_prompt_release(prompt_release(**{field: bad_value}))
                    self.assertEqual(gate.snapshot()["phase"], PHASE_POISONED)

    def test_stop_waits_for_active_handler_before_final_seal(self) -> None:
        release = threading.Event()
        usage = provider_usage(40)
        harness = GateHarness(
            self,
            [FakePlan(completed_sse("late", usage), release=release)],
            token_limit=500,
            response_bound=100,
        )
        self.addCleanup(harness.cleanup)
        result: list[tuple[int, bytes, dict[str, str]]] = []
        client = threading.Thread(target=lambda: result.append(harness.post()))
        client.start()
        self.assertTrue(harness.factory.plans[0].started.wait(5.0))
        stopped = threading.Event()

        def stop_gate() -> None:
            harness.gate.stop()
            stopped.set()

        stopper = threading.Thread(target=stop_gate)
        stopper.start()
        time.sleep(0.05)
        self.assertFalse(stopped.is_set())
        with self.assertRaisesRegex(ProviderGateError, "stopped"):
            harness.gate.finalize()
        release.set()
        client.join(5.0)
        stopper.join(5.0)
        self.assertFalse(client.is_alive())
        self.assertFalse(stopper.is_alive())
        artifact = harness.gate.finalize()
        before = harness.gate.final_artifact_path.read_bytes()
        time.sleep(0.05)
        after = harness.gate.final_artifact_path.read_bytes()
        self.assertEqual(before, after)
        self.assertTrue(artifact["state"]["handlers_quiescent"])
        self.assertTrue(artifact["state"]["poisoned"])

    def test_final_validator_rejects_mode_hash_and_canonical_tampering(self) -> None:
        harness = GateHarness(self, [], token_limit=500, response_bound=100)
        self.addCleanup(harness.cleanup)
        harness.finish(CLOSE_REASON_NATURAL_END)
        path = harness.gate.final_artifact_path
        os.chmod(path, 0o644)
        with self.assertRaisesRegex(ProviderGateValidationError, "0444"):
            validate_artifact(path)
        os.chmod(path, 0o444)
        original = path.read_bytes()

        for label, mutate, expected_error in (
            (
                "transport",
                lambda value: value["configuration"]["transport_provenance"][
                    "tls"
                ].__setitem__("certificate_source_mode", "environment_default"),
                "certificate_source_mode",
            ),
            (
                "setup",
                lambda value: value["setup_requests"].append({"fabricated": True}),
                "setup forwarding must be absent",
            ),
        ):
            forged = json.loads(original)
            mutate(forged)
            unsigned = dict(forged)
            unsigned.pop("record_sha256")
            forged["record_sha256"] = hashlib.sha256(
                (
                    json.dumps(
                        unsigned,
                        sort_keys=True,
                        separators=(",", ":"),
                        ensure_ascii=False,
                    )
                    + "\n"
                ).encode("utf-8")
            ).hexdigest()
            forged_path = harness.root / f"forged-{label}.json"
            forged_path.write_text(
                json.dumps(forged, sort_keys=True, separators=(",", ":")) + "\n"
            )
            forged_path.chmod(0o444)
            with self.assertRaisesRegex(
                ProviderGateValidationError, expected_error
            ):
                validate_artifact(forged_path)

        os.chmod(path, 0o644)
        record = json.loads(original)
        record["state"]["completed_tokens"] = 1
        path.write_text(json.dumps(record, sort_keys=True, separators=(",", ":")) + "\n")
        os.chmod(path, 0o444)
        with self.assertRaisesRegex(ProviderGateValidationError, "self-hash"):
            validate_artifact(path)

    def test_final_validator_rejects_bool_and_float_numeric_aliases(self) -> None:
        harness = GateHarness(self, [], token_limit=500, response_bound=100)
        self.addCleanup(harness.cleanup)
        artifact = harness.finish(CLOSE_REASON_NATURAL_END)

        mutations = (
            ("schema-bool", lambda value: value.__setitem__("schema_version", True)),
            (
                "transport-schema-bool",
                lambda value: value["configuration"]["transport_provenance"].__setitem__(
                    "schema_version", True
                ),
            ),
            (
                "retry-bool",
                lambda value: value["configuration"].__setitem__(
                    "request_retries", False
                ),
            ),
            (
                "bound-float",
                lambda value: value["configuration"].__setitem__(
                    "response_bound", 100.0
                ),
            ),
            (
                "completed-false",
                lambda value: value["state"].__setitem__(
                    "completed_tokens", False
                ),
            ),
            (
                "active-false",
                lambda value: value["state"].__setitem__(
                    "active_handler_count", False
                ),
            ),
            (
                "sequence-float",
                lambda value: value["state"].__setitem__("sequence", 1.0),
            ),
            (
                "invariant-one",
                lambda value: value["invariants"].__setitem__(
                    "bindings_complete", 1
                ),
            ),
        )
        for label, mutate in mutations:
            with self.subTest(label=label):
                forged = json.loads(json.dumps(artifact))
                mutate(forged)
                reseal_provider_gate_record(forged)
                forged_path = harness.root / f"forged-type-{label}.json"
                forged_path.write_text(
                    json.dumps(forged, sort_keys=True, separators=(",", ":")) + "\n"
                )
                forged_path.chmod(0o444)
                with self.assertRaises(ProviderGateValidationError):
                    validate_artifact(forged_path)

        usage = provider_usage(40, cached=20)
        call_harness = GateHarness(
            self,
            [FakePlan(completed_sse("strict-types", usage))],
            token_limit=500,
            response_bound=100,
        )
        self.addCleanup(call_harness.cleanup)
        self.assertEqual(call_harness.post()[0], 200)
        call_harness.crossbind("strict-types", usage, 1)
        call_artifact = call_harness.finish(CLOSE_REASON_NATURAL_END)
        call_mutations = (
            (
                "call-bound-float",
                lambda value: value["calls"][0].__setitem__(
                    "response_bound", 100.0
                ),
            ),
            (
                "upstream-start-one",
                lambda value: value["calls"][0].__setitem__(
                    "upstream_started", 1
                ),
            ),
            (
                "previous-total-false",
                lambda value: value["calls"][0].__setitem__(
                    "previous_total", False
                ),
            ),
            (
                "crossed-cap-zero",
                lambda value: value["calls"][0].__setitem__(
                    "crossed_cap", 0
                ),
            ),
            (
                "crossbind-sequence-float",
                lambda value: value["calls"][0]["appserver_crossbind"].__setitem__(
                    "event_sequence", 1.0
                ),
            ),
        )
        for label, mutate in call_mutations:
            with self.subTest(label=label):
                forged = json.loads(json.dumps(call_artifact))
                mutate(forged)
                reseal_provider_gate_record(forged)
                forged_path = call_harness.root / f"forged-type-{label}.json"
                forged_path.write_text(
                    json.dumps(forged, sort_keys=True, separators=(",", ":")) + "\n"
                )
                forged_path.chmod(0o444)
                with self.assertRaises(ProviderGateValidationError):
                    validate_artifact(forged_path)


if __name__ == "__main__":
    unittest.main()
