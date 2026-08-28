#!/usr/bin/env python3
"""Trusted, fail-closed Responses API token-admission proxy.

The benchmark's Codex process uses this loopback-only proxy as a private model
provider.  Every counted ``POST /responses`` is fully buffered, authenticated,
and committed to a durable ledger before any provider output is released to
Codex.  Concurrent requests are admitted only while reserving the frozen
per-response upper bound cannot reach the attempt token limit.  The gate then
drains and serializes requests, making the first cap-crossing response the sole
request in flight.

This module deliberately uses only the Python 3.10 standard library.  It never
records request bodies, response bodies, credential values, or the unguessable
loopback capability.  It records only the two non-secret representation-header
values needed to authenticate a provider response envelope.
"""

from __future__ import annotations

import copy
import hashlib
import http.client
import http.server as http_server
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import json
import json.decoder as json_decoder
import json.encoder as json_encoder
import os
from pathlib import Path
import re
import secrets
import socket
import ssl
import stat
import sys
import sysconfig
import threading
import time
from typing import Any, Callable, Mapping, MutableMapping, Sequence
from urllib.parse import urlsplit

import _ssl
import _socket
import _hashlib
import _json


PROVIDER_GATE_SCHEMA_VERSION = 6
PROVIDER_GATE_PROTOCOL = "highambench-provider-token-gate-v6"
PROVIDER_GATE_IMPLEMENTATION_NAME = "provider_token_gate.py"
PROVIDER_GATE_IMPLEMENTATION_VERSION = "6"
PROVIDER_GATE_RECORD_SHA256_FIELD = "record_sha256"
PROVIDER_GATE_LIVE_SUFFIX = ".provider-token-gate.live.json"
PROVIDER_GATE_FINAL_SUFFIX = ".provider-token-gate.json"
PROVIDER_GATE_CANONICAL_ENCODING = "compact_sorted_key_utf8_json_newline"
PROVIDER_GATE_SEALED_MODE = "0444"

DEFAULT_UPSTREAM_ORIGIN = "https://chatgpt.com"
DEFAULT_UPSTREAM_HOST = "chatgpt.com"
DEFAULT_UPSTREAM_PORT = 443
DEFAULT_UPSTREAM_BASE_PATH = "/backend-api/codex"
DEFAULT_RESPONSE_BOUND = 272_000
DEFAULT_MAX_REQUEST_BYTES = 64 * 1024 * 1024
DEFAULT_MAX_RESPONSE_BYTES = 256 * 1024 * 1024
PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_SCHEMA_VERSION = 1
PROVIDER_GATE_UPSTREAM_RESPONSE_PROTOCOL = "highambench-responses-sse-envelope-v1"
PROVIDER_GATE_SSE_PARSER = "highambench-strict-responses-sse-v2"
PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_SCHEMA_VERSION = 1
PROVIDER_GATE_WAIT_AGENT_MIN_TIMEOUT_MS = 10_000
PROVIDER_GATE_WAIT_AGENT_MAX_TIMEOUT_MS = 3_600_000
PROVIDER_GATE_DELIVERY_DIRECT = "direct_raw_response"
PROVIDER_GATE_DELIVERY_SUPPRESSED_WAIT = "suppressed_collaboration_wait"
PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE = (
    "superseded_by_collaboration_message"
)
PROVIDER_GATE_DELIVERY_DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT = (
    "discarded_after_explicit_child_interrupt"
)
PROVIDER_GATE_DELIVERY_KINDS = (
    PROVIDER_GATE_DELIVERY_DIRECT,
    PROVIDER_GATE_DELIVERY_SUPPRESSED_WAIT,
    PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE,
    PROVIDER_GATE_DELIVERY_DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT,
)
PROVIDER_GATE_CONTENT_TYPE_POLICY = (
    "absent_or_single_text_event_stream_optional_utf8_charset"
)
PROVIDER_GATE_CONTENT_ENCODING_POLICY = "absent_or_single_identity"
PROVIDER_GATE_OUTBOUND_ACCEPT = "text/event-stream"
PROVIDER_GATE_DOWNSTREAM_CONTENT_TYPE = "text/event-stream"
PROVIDER_GATE_DOWNSTREAM_CONTENT_ENCODING = "identity"
PROVIDER_GATE_SSE_DIAGNOSTIC_TOKEN_MAX_LENGTH = 64
PROVIDER_GATE_SSE_CONTENT_TYPE_BASES = (
    "declared_text_event_stream",
    "authenticated_stream_request_header_absent",
)
PROVIDER_GATE_SSE_CONTENT_ENCODING_BASES = (
    "declared_identity",
    "implicit_identity_header_absent",
)
PROVIDER_TRANSPORT_SCHEMA_VERSION = 1
PROVIDER_TRANSPORT_KIND = "python-stdlib-http-client-explicit-tls-v1"
PROVIDER_CA_BUNDLE_PATH = "/etc/ssl/certs/ca-certificates.crt"
PROVIDER_OPENSSL_CONFIG_PATH = "/usr/lib/ssl/openssl.cnf"
PROVIDER_RESOLV_CONF_PATH = "/etc/resolv.conf"
PROVIDER_NSSWITCH_PATH = "/etc/nsswitch.conf"
PROVIDER_HOSTS_PATH = "/etc/hosts"
PROVIDER_GAI_CONF_PATH = "/etc/gai.conf"
PROVIDER_TLS_MINIMUM_VERSION = ssl.TLSVersion.TLSv1_2
PROVIDER_TLS_ALPN_PROTOCOLS = ("http/1.1",)
PROVIDER_CERTIFICATE_SOURCE_MODE = "explicit_hashed_pem_cadata_only"
PROVIDER_PROXY_MODE = "direct_http_client_no_environment_proxy"
PROVIDER_CONNECTION_FACTORY_EXPLICIT_TLS = "explicit_tls"
PROVIDER_CONNECTION_FACTORY_TEST_OVERRIDE = "test_override"
PROVIDER_CONNECTION_FACTORY_MODES = (
    PROVIDER_CONNECTION_FACTORY_EXPLICIT_TLS,
    PROVIDER_CONNECTION_FACTORY_TEST_OVERRIDE,
)
PROVIDER_RESOLVER_POLICY = (
    "host_getaddrinfo_dynamic_addresses_authenticated_by_tls_hostname"
)
PROVIDER_RESOLVER_VARIABILITY_CLASSIFICATION = (
    "availability_only_under_authenticated_tls_hostname"
)
PROVIDER_TRANSPORT_ENV_REQUIRED_ABSENT = tuple(
    sorted(
        {
            "ALL_PROXY",
            "CURL_CA_BUNDLE",
            "HTTPS_PROXY",
            "HTTP_PROXY",
            "LD_AUDIT",
            "LD_LIBRARY_PATH",
            "LD_PRELOAD",
            "NO_PROXY",
            "OPENSSL_CONF",
            "OPENSSL_MODULES",
            "PYTHONHOME",
            "PYTHONHTTPSVERIFY",
            "PYTHONINSPECT",
            "PYTHONPATH",
            "PYTHONSTARTUP",
            "PYTHONWARNINGS",
            "REQUESTS_CA_BUNDLE",
            "SSLKEYLOGFILE",
            "SSL_CERT_DIR",
            "SSL_CERT_FILE",
            "all_proxy",
            "http_proxy",
            "https_proxy",
            "no_proxy",
        }
    )
)

PHASE_CONCURRENT = "CONCURRENT"
PHASE_DRAINING = "DRAINING"
PHASE_EXCLUSIVE = "EXCLUSIVE"
PHASE_CLOSED = "CLOSED"
PHASE_POISONED = "POISONED"
PROVIDER_GATE_PHASES = (
    PHASE_CONCURRENT,
    PHASE_DRAINING,
    PHASE_EXCLUSIVE,
    PHASE_CLOSED,
    PHASE_POISONED,
)

CLOSE_REASON_TOKEN_LIMIT = "token_limit"
CLOSE_REASON_ACCEPTED_SUBMISSION = "accepted_submission"
CLOSE_REASON_NATURAL_END = "natural_end"
CLOSE_REASON_SYSTEM_ERROR = "system_error"
CLOSE_REASON_POISON = "poison"
PROVIDER_GATE_CLOSE_REASONS = (
    CLOSE_REASON_TOKEN_LIMIT,
    CLOSE_REASON_ACCEPTED_SUBMISSION,
    CLOSE_REASON_NATURAL_END,
    CLOSE_REASON_SYSTEM_ERROR,
    CLOSE_REASON_POISON,
)

RELEASE_BYTE_IDENTITY = "byte_identity"
RELEASE_SANITIZED_CROSSING = "sanitized_crossing_completion"
RELEASE_SANITIZED_COMPACTION_CROSSING = (
    "sanitized_compaction_crossing_completion"
)
RELEASE_SANITIZED_TERMINAL = "sanitized_terminal_close"
RELEASE_NONE = "none"
PROVIDER_GATE_RELEASE_KINDS = (
    RELEASE_BYTE_IDENTITY,
    RELEASE_SANITIZED_CROSSING,
    RELEASE_SANITIZED_COMPACTION_CROSSING,
    RELEASE_SANITIZED_TERMINAL,
    RELEASE_NONE,
)

ADMISSION_MODE_CONCURRENT = "CONCURRENT"
ADMISSION_MODE_EXCLUSIVE = "EXCLUSIVE"
PROVIDER_GATE_ADMISSION_MODES = (
    ADMISSION_MODE_CONCURRENT,
    ADMISSION_MODE_EXCLUSIVE,
)

PROVIDER_GATE_TOP_LEVEL_KEYS = frozenset(
    {
        "schema_version",
        "protocol",
        "implementation",
        "configuration",
        "bindings",
        "lifecycle",
        "state",
        "calls",
        "transitions",
        "denials",
        "setup_requests",
        "invariants",
        "canonical_encoding",
        "sealed_mode",
        PROVIDER_GATE_RECORD_SHA256_FIELD,
    }
)
PROVIDER_GATE_IMPLEMENTATION_KEYS = frozenset({"name", "version", "source_sha256"})
PROVIDER_GATE_CONFIGURATION_KEYS = frozenset(
    {
        "token_limit",
        "response_bound",
        "response_bound_enforcement",
        "model_catalog_sha256",
        "model_entry_sha256",
        "strict_admission_inequality",
        "upstream_origin",
        "upstream_base_path",
        "loopback_only",
        "capability_persisted",
        "websockets_supported",
        "request_retries",
        "stream_retries",
        "request_compression",
        "response_compression",
        "counted_route",
        "counted_request_kinds",
        "rejected_inference_routes",
        "allowed_setup_route_prefixes",
        "crossing_release_policy",
        "upstream_response_contract",
        "transport_provenance",
    }
)
PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_KEYS = frozenset(
    {
        "schema_version",
        "protocol",
        "success_status",
        "content_type_policy",
        "content_encoding_policy",
        "outbound_accept",
        "parser",
        "downstream_content_type",
        "downstream_content_encoding",
    }
)
PROVIDER_GATE_BINDING_KEYS = frozenset(
    {
        "root_thread_id",
        "run_id",
        "model",
        "reasoning_effort",
        "prompt_release_sha256",
        "prompt_release_protocol",
        "prompt_sha256",
    }
)
PROVIDER_GATE_STATE_KEYS = frozenset(
    {
        "phase",
        "close_reason",
        "completed_tokens",
        "crossing",
        "crossing_closed",
        "open_request_ids",
        "all_complete",
        "no_post_close_upstream",
        "poisoned",
        "poison_reasons",
        "active_handler_count",
        "handlers_quiescent",
        "sequence",
    }
)
PROVIDER_GATE_LIFECYCLE_KEYS = frozenset(
    {
        "started_unix_ns",
        "started_monotonic_ns",
        "stopped_unix_ns",
        "stopped_monotonic_ns",
        "finalized_unix_ns",
        "finalized_monotonic_ns",
    }
)
PROVIDER_GATE_REQUEST_METADATA_KEYS = frozenset(
    {
        "installation_id",
        "session_id",
        "thread_id",
        "turn_id",
        "request_kind",
        "window_id",
    }
)
PROVIDER_GATE_NORMALIZED_USAGE_KEYS = frozenset(
    {
        "input_tokens",
        "cached_input_tokens",
        "cache_write_input_tokens",
        "output_tokens",
        "reasoning_output_tokens",
        "total_tokens",
    }
)
PROVIDER_GATE_CALL_KEYS = frozenset(
    {
        "sequence",
        "call_id",
        "method",
        "route",
        "request_body_sha256",
        "request_bytes",
        "request_model",
        "request_stream",
        "request_metadata",
        "credential_headers_present",
        "admission_mode",
        "response_bound",
        "completed_before",
        "open_before",
        "reserved_before",
        "reservation_after",
        "admitted_unix_ns",
        "admitted_monotonic_ns",
        "upstream_started",
        "upstream_start_unix_ns",
        "upstream_start_monotonic_ns",
        "upstream_status",
        "upstream_content_type_occurrences",
        "upstream_content_type",
        "upstream_content_encoding_occurrences",
        "upstream_content_encoding",
        "upstream_sse_authentication",
        "upstream_body_sha256",
        "upstream_body_bytes",
        "response_id",
        "usage",
        "normalized_usage",
        "previous_total",
        "committed_total",
        "commit_unix_ns",
        "commit_monotonic_ns",
        "crossed_cap",
        "release_kind",
        "released_body_sha256",
        "released_body_bytes",
        "released_sanitized_event",
        "released_sanitized_events",
        "released_sanitized_body_utf8",
        "client_release_complete",
        "response_output_manifest",
        "appserver_crossbind",
        "appserver_delivery",
        "error",
    }
)
PROVIDER_GATE_SSE_AUTHENTICATION_KEYS = frozenset(
    {
        "schema_version",
        "protocol",
        "parser",
        "complete",
        "content_type_basis",
        "content_encoding_basis",
        "json_event_count",
        "completed_event_index",
        "done_count",
        "body_sha256",
        "body_bytes",
        "response_id",
        "downstream_content_type_synthesized",
    }
)
PROVIDER_GATE_DENIAL_KEYS = frozenset(
    {
        "sequence",
        "denial_id",
        "method",
        "route",
        "reason",
        "phase",
        "upstream_started",
        "unix_ns",
        "monotonic_ns",
        "request_metadata",
    }
)
PROVIDER_GATE_TRANSITION_KEYS = frozenset(
    {
        "sequence",
        "from_phase",
        "to_phase",
        "reason",
        "call_id",
        "unix_ns",
        "monotonic_ns",
    }
)
PROVIDER_GATE_CROSSING_KEYS = frozenset(
    {
        "call_id",
        "response_id",
        "sequence",
        "previous_total",
        "response_tokens",
        "completed_tokens",
        "overshoot_tokens",
        "commit_unix_ns",
        "commit_monotonic_ns",
        "sole_inflight",
        "release_kind",
        "request_kind",
    }
)
PROVIDER_GATE_CROSSBIND_KEYS = frozenset(
    {
        "thread_id",
        "turn_id",
        "event_sequence",
        "normalized_usage",
        "bind_unix_ns",
        "bind_monotonic_ns",
    }
)
PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_KEYS = frozenset(
    {
        "schema_version",
        "response_id",
        "output_item_count",
        "action_capable_item_count",
        "items",
    }
)
PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_ITEM_KEYS = frozenset(
    {
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
)
PROVIDER_GATE_APPSERVER_DELIVERY_KEYS = frozenset(
    {
        "kind",
        "successor_call_id",
        "successor_response_id",
        "bind_unix_ns",
        "bind_monotonic_ns",
    }
)
PROVIDER_GATE_SUPPRESSED_WAIT_CANDIDATE_KEYS = frozenset(
    {
        "response_id",
        "call_id",
        "thread_id",
        "turn_id",
        "normalized_usage",
        "commit_unix_ns",
        "commit_monotonic_ns",
        "wait_call_id",
        "wait_timeout_ms",
        "response_output_manifest_sha256",
        "successor_response_id",
        "successor_call_id",
        "successor_admitted_unix_ns",
        "successor_admitted_monotonic_ns",
    }
)
PROVIDER_GATE_SUPERSEDED_COLLABORATION_MESSAGE_CANDIDATE_KEYS = frozenset(
    {
        "response_id",
        "call_id",
        "thread_id",
        "turn_id",
        "normalized_usage",
        "commit_unix_ns",
        "commit_monotonic_ns",
        "action_capable_item_count",
        "response_output_manifest_sha256",
        "successor_response_id",
        "successor_call_id",
        "successor_admitted_unix_ns",
        "successor_admitted_monotonic_ns",
    }
)
PROVIDER_GATE_DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_CANDIDATE_KEYS = frozenset(
    {
        "response_id",
        "call_id",
        "thread_id",
        "turn_id",
        "normalized_usage",
        "admitted_unix_ns",
        "admitted_monotonic_ns",
        "commit_unix_ns",
        "commit_monotonic_ns",
        "action_capable_item_count",
        "response_output_manifest_sha256",
        "interrupting_response_id",
        "interrupting_call_id",
        "interrupt_parent_thread_id",
        "interrupt_parent_turn_id",
        "interrupt_admitted_unix_ns",
        "interrupt_admitted_monotonic_ns",
        "interrupt_commit_unix_ns",
        "interrupt_commit_monotonic_ns",
        "interrupt_bind_unix_ns",
        "interrupt_bind_monotonic_ns",
        "interrupt_function_item_id",
        "interrupt_function_call_id",
        "interrupt_function_arguments_sha256",
        "interrupt_function_arguments_bytes",
        "interrupt_response_output_manifest_sha256",
    }
)
PROVIDER_GATE_COMPLETED_RESPONSE_USAGE_SNAPSHOT_KEYS = frozenset(
    {
        "response_id",
        "call_id",
        "commit_unix_ns",
        "commit_monotonic_ns",
        "normalized_usage",
        "thread_id",
        "turn_id",
        "appserver_delivery_kind",
        "successor_call_id",
        "successor_response_id",
    }
)
PROVIDER_TRANSPORT_PROVENANCE_KEYS = frozenset(
    {
        "schema_version",
        "kind",
        "python",
        "openssl",
        "tls",
        "resolver",
        "environment",
        "connection_factory_mode",
    }
)
PROVIDER_TRANSPORT_DEPENDENCY_KEYS = frozenset(
    {"logical_path", "resolved_path", "symlink_target", "sha256", "bytes", "mode"}
)
PROVIDER_TRANSPORT_PYTHON_KEYS = frozenset(
    {
        "executable",
        "version",
        "implementation",
        "binary",
        "ssl_module",
        "http_client_module",
        "socket_module",
        "http_server_module",
        "json_module",
        "json_encoder_module",
        "json_decoder_module",
        "json_extension",
        "hashlib_module",
        "hashlib_extension",
        "ssl_extension",
        "socket_implementation",
    }
)
PROVIDER_TRANSPORT_OPENSSL_KEYS = frozenset(
    {"version", "version_number", "libssl", "libcrypto", "config"}
)
PROVIDER_TRANSPORT_TLS_KEYS = frozenset(
    {
        "protocol",
        "protocol_value",
        "server_hostname",
        "server_port",
        "certificate_source",
        "certificate_source_mode",
        "certificate_authority_count",
        "default_capath_used",
        "verify_mode",
        "verify_mode_value",
        "check_hostname",
        "minimum_version",
        "minimum_version_value",
        "maximum_version",
        "maximum_version_value",
        "alpn_protocols",
        "keylog_enabled",
        "context_options",
        "verify_flags",
        "security_level",
        "cipher_names_sha256",
    }
)
PROVIDER_TRANSPORT_RESOLVER_KEYS = frozenset(
    {
        "policy",
        "hostname",
        "resolv_conf",
        "nsswitch_conf",
        "hosts_file",
        "gai_conf",
        "libc",
        "libnss_dns",
        "libnss_files",
        "resolved_addresses_frozen",
        "variability_classification",
    }
)
PROVIDER_TRANSPORT_ENVIRONMENT_KEYS = frozenset(
    {"required_absent", "observed_absent", "proxy_mode"}
)
PROVIDER_GATE_INVARIANT_KEYS = frozenset(
    {
        "bindings_complete",
        "completed_sum_matches",
        "usage_consistent",
        "all_response_totals_within_bound",
        "response_ids_unique",
        "strict_reservation_safe",
        "exclusive_serial",
        "crossing_sole_inflight",
        "crossing_rewritten",
        "no_action_capable_output_frames_on_crossing",
        "no_post_close_upstream",
        "all_admitted_terminal",
        "all_appserver_deliveries_reconciled",
        "no_open_requests",
        "not_poisoned",
    }
)

COUNTED_METHOD = "POST"
COUNTED_ROUTE = "/responses"
PROVIDER_GATE_COUNTED_REQUEST_KINDS = ("turn", "compaction")
REJECTED_INFERENCE_ROUTES = ("/responses/compact",)
ALLOWED_SETUP_ROUTE_PREFIXES: tuple[str, ...] = ()
CROSSING_RELEASE_POLICY = (
    "ordinary_empty_output_or_compaction_single_item_before_minimal_completion"
)

_HOP_BY_HOP_HEADERS = frozenset(
    {
        "connection",
        "keep-alive",
        "proxy-authenticate",
        "proxy-authorization",
        "te",
        "trailer",
        "transfer-encoding",
        "upgrade",
    }
)
_CREDENTIAL_HEADERS = frozenset(
    {
        "authorization",
        "cookie",
        "openai-organization",
        "openai-project",
        "chatgpt-account-id",
        "x-openai-attestation",
        "x-codex-attestation",
    }
)
_REQUEST_METADATA_KEYS = (
    "installation_id",
    "session_id",
    "thread_id",
    "turn_id",
    "request_kind",
    "window_id",
)


class ProviderGateError(RuntimeError):
    """Base class for provider-gate failures."""


class ProviderGateValidationError(ProviderGateError):
    """Raised when a live or final artifact is not authentic and consistent."""


class _LocalDenial(ProviderGateError):
    def __init__(self, status: int, code: str, message: str) -> None:
        super().__init__(message)
        self.status = status
        self.code = code
        self.message = message


def _canonical_json_bytes(value: Any) -> bytes:
    return (
        json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        + "\n"
    ).encode("utf-8")


def _sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def _document_sha256(value: Mapping[str, Any]) -> str:
    unsigned = dict(value)
    unsigned.pop(PROVIDER_GATE_RECORD_SHA256_FIELD, None)
    return _sha256_bytes(_canonical_json_bytes(unsigned))


def _self_hashed(value: Mapping[str, Any]) -> dict[str, Any]:
    result = copy.deepcopy(dict(value))
    result.pop(PROVIDER_GATE_RECORD_SHA256_FIELD, None)
    result[PROVIDER_GATE_RECORD_SHA256_FIELD] = _sha256_bytes(
        _canonical_json_bytes(result)
    )
    return result


def provider_gate_artifact_path(usage_output: os.PathLike[str] | str) -> Path:
    """Return the final gate artifact beside an exact usage-output path."""

    path = Path(usage_output)
    name = path.name
    base = name[: -len(".usage.json")] if name.endswith(".usage.json") else path.stem
    if not base or base in (".", ".."):
        raise ProviderGateError("usage output cannot derive a provider-gate name")
    return path.parent / f"{base}{PROVIDER_GATE_FINAL_SUFFIX}"


def provider_gate_live_path(usage_output: os.PathLike[str] | str) -> Path:
    """Return the atomic live gate record beside an exact usage-output path."""

    path = Path(usage_output)
    name = path.name
    base = name[: -len(".usage.json")] if name.endswith(".usage.json") else path.stem
    if not base or base in (".", ".."):
        raise ProviderGateError("usage output cannot derive a provider-gate name")
    return path.parent / f"{base}{PROVIDER_GATE_LIVE_SUFFIX}"


def _require_nonempty_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ProviderGateError(f"{label} must be a nonempty string")
    return value


def _require_sha256(value: Any, label: str) -> str:
    text = _require_nonempty_string(value, label)
    if len(text) != 64 or any(ch not in "0123456789abcdef" for ch in text):
        raise ProviderGateError(f"{label} must be a lowercase SHA-256 digest")
    return text


def _source_sha256() -> str:
    return _sha256_bytes(Path(__file__).read_bytes())


def _read_all_fd(descriptor: int) -> bytes:
    chunks: list[bytes] = []
    while True:
        chunk = os.read(descriptor, 1024 * 1024)
        if not chunk:
            return b"".join(chunks)
        chunks.append(chunk)


def _regular_dependency(
    logical_path: os.PathLike[str] | str,
    *,
    nofollow: bool = False,
) -> tuple[dict[str, Any], bytes]:
    """Read and describe exactly one regular dependency through the same fd."""

    logical = os.fspath(logical_path)
    if not os.path.isabs(logical):
        raise ProviderGateError(f"transport dependency path is not absolute: {logical}")
    try:
        link_metadata = os.lstat(logical)
        symlink_target = (
            os.readlink(logical) if stat.S_ISLNK(link_metadata.st_mode) else None
        )
        flags = os.O_RDONLY | os.O_CLOEXEC
        if nofollow:
            if not hasattr(os, "O_NOFOLLOW"):
                raise ProviderGateError("O_NOFOLLOW is unavailable for CA loading")
            flags |= os.O_NOFOLLOW
        descriptor = os.open(logical, flags)
    except (OSError, ValueError) as exc:
        raise ProviderGateError(
            f"transport dependency cannot be opened: {logical}"
        ) from exc
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            raise ProviderGateError(
                f"transport dependency is not a regular file: {logical}"
            )
        try:
            resolved = os.readlink(f"/proc/self/fd/{descriptor}")
        except OSError as exc:
            raise ProviderGateError(
                f"transport dependency fd cannot be resolved: {logical}"
            ) from exc
        if resolved.endswith(" (deleted)") or not os.path.isabs(resolved):
            raise ProviderGateError(
                f"transport dependency fd is not stable: {logical}"
            )
        payload = _read_all_fd(descriptor)
        if len(payload) != metadata.st_size:
            raise ProviderGateError(
                f"transport dependency changed while being read: {logical}"
            )
    finally:
        os.close(descriptor)
    return (
        {
            "logical_path": logical,
            "resolved_path": os.path.realpath(resolved),
            "symlink_target": symlink_target,
            "sha256": _sha256_bytes(payload),
            "bytes": len(payload),
            "mode": f"{stat.S_IMODE(metadata.st_mode):04o}",
        },
        payload,
    )


def _dependency_descriptor(logical_path: os.PathLike[str] | str) -> dict[str, Any]:
    descriptor, _payload = _regular_dependency(logical_path)
    return descriptor


def _module_descriptor(module: Any, label: str) -> dict[str, Any]:
    path = getattr(module, "__file__", None)
    if not isinstance(path, str) or not path:
        raise ProviderGateError(f"transport module {label} is not file-backed")
    return _dependency_descriptor(path)


def _loaded_library_path(basename_prefix: str) -> str:
    try:
        maps = Path("/proc/self/maps").read_text(encoding="utf-8")
    except (OSError, UnicodeError) as exc:
        raise ProviderGateError("loaded transport libraries cannot be enumerated") from exc
    candidates: set[str] = set()
    for line in maps.splitlines():
        fields = line.split(maxsplit=5)
        if len(fields) != 6:
            continue
        path = fields[5]
        if path.startswith("/") and Path(path).name.startswith(basename_prefix):
            candidates.add(os.path.realpath(path))
    if len(candidates) != 1:
        raise ProviderGateError(
            f"loaded transport library is ambiguous or absent: {basename_prefix}"
        )
    return next(iter(candidates))


def _system_library_path(filename: str) -> str:
    multiarch = sysconfig.get_config_var("MULTIARCH")
    if not isinstance(multiarch, str) or not multiarch:
        raise ProviderGateError("Python MULTIARCH is unavailable")
    candidates = (
        Path("/usr/lib") / multiarch / filename,
        Path("/lib") / multiarch / filename,
    )
    for candidate in candidates:
        if candidate.is_file():
            return os.fspath(candidate)
    raise ProviderGateError(f"required resolver library is absent: {filename}")


def transport_cipher_names_sha256(context: ssl.SSLContext) -> str:
    """Hash the ordered enabled-cipher names using canonical JSON plus newline."""

    names = [cipher.get("name") for cipher in context.get_ciphers()]
    if not names or not all(isinstance(name, str) and name for name in names):
        raise ProviderGateError("TLS context cipher inventory is malformed")
    return _sha256_bytes(_canonical_json_bytes(names))


def build_transport_provenance() -> tuple[ssl.SSLContext, dict[str, Any]]:
    """Build the explicit TLS context and its deterministic local trust record."""

    present = [
        name for name in PROVIDER_TRANSPORT_ENV_REQUIRED_ABSENT if name in os.environ
    ]
    if present:
        raise ProviderGateError(
            "transport override environment must be absent: " + ",".join(present)
        )

    ca_descriptor, ca_payload = _regular_dependency(
        PROVIDER_CA_BUNDLE_PATH, nofollow=True
    )
    try:
        ca_pem = ca_payload.decode("ascii", errors="strict")
    except UnicodeDecodeError as exc:
        raise ProviderGateError("CA bundle is not strict ASCII PEM") from exc
    if not ca_pem or "-----BEGIN CERTIFICATE-----" not in ca_pem or "\x00" in ca_pem:
        raise ProviderGateError("CA bundle is not nonempty PEM certificate data")

    context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    context.verify_mode = ssl.CERT_REQUIRED
    context.check_hostname = True
    context.minimum_version = PROVIDER_TLS_MINIMUM_VERSION
    context.maximum_version = ssl.TLSVersion.MAXIMUM_SUPPORTED
    context.set_alpn_protocols(list(PROVIDER_TLS_ALPN_PROTOCOLS))
    try:
        context.load_verify_locations(cadata=ca_pem)
    except ssl.SSLError as exc:
        raise ProviderGateError("explicit CA bundle could not be loaded") from exc
    if context.keylog_filename is not None:
        raise ProviderGateError("TLS key logging is unexpectedly enabled")
    ca_count = context.cert_store_stats().get("x509_ca")
    if isinstance(ca_count, bool) or not isinstance(ca_count, int) or ca_count < 1:
        raise ProviderGateError("explicit CA bundle loaded no certificate authorities")
    socket_origin = getattr(getattr(_socket, "__spec__", None), "origin", None)
    if socket_origin != "built-in" or getattr(_socket, "__file__", None) is not None:
        raise ProviderGateError("_socket is not the expected CPython built-in")

    provenance = {
        "schema_version": PROVIDER_TRANSPORT_SCHEMA_VERSION,
        "kind": PROVIDER_TRANSPORT_KIND,
        "connection_factory_mode": PROVIDER_CONNECTION_FACTORY_EXPLICIT_TLS,
        "python": {
            "executable": sys.executable,
            "version": sys.version.split()[0],
            "implementation": sys.implementation.name,
            "binary": _dependency_descriptor(sys.executable),
            "ssl_module": _module_descriptor(ssl, "ssl"),
            "http_client_module": _module_descriptor(http.client, "http.client"),
            "socket_module": _module_descriptor(socket, "socket"),
            "http_server_module": _module_descriptor(http_server, "http.server"),
            "json_module": _module_descriptor(json, "json"),
            "json_encoder_module": _module_descriptor(json_encoder, "json.encoder"),
            "json_decoder_module": _module_descriptor(json_decoder, "json.decoder"),
            "json_extension": _module_descriptor(_json, "_json"),
            "hashlib_module": _module_descriptor(hashlib, "hashlib"),
            "hashlib_extension": _module_descriptor(_hashlib, "_hashlib"),
            "ssl_extension": _module_descriptor(_ssl, "_ssl"),
            "socket_implementation": socket_origin,
        },
        "openssl": {
            "version": ssl.OPENSSL_VERSION,
            "version_number": ssl.OPENSSL_VERSION_NUMBER,
            "libssl": _dependency_descriptor(_loaded_library_path("libssl.so")),
            "libcrypto": _dependency_descriptor(
                _loaded_library_path("libcrypto.so")
            ),
            "config": _dependency_descriptor(PROVIDER_OPENSSL_CONFIG_PATH),
        },
        "tls": {
            "protocol": context.protocol.name,
            "protocol_value": int(context.protocol),
            "server_hostname": DEFAULT_UPSTREAM_HOST,
            "server_port": DEFAULT_UPSTREAM_PORT,
            "certificate_source": ca_descriptor,
            "certificate_source_mode": PROVIDER_CERTIFICATE_SOURCE_MODE,
            "certificate_authority_count": ca_count,
            "default_capath_used": False,
            "verify_mode": context.verify_mode.name,
            "verify_mode_value": int(context.verify_mode),
            "check_hostname": context.check_hostname,
            "minimum_version": context.minimum_version.name,
            "minimum_version_value": int(context.minimum_version),
            "maximum_version": context.maximum_version.name,
            "maximum_version_value": int(context.maximum_version),
            "alpn_protocols": list(PROVIDER_TLS_ALPN_PROTOCOLS),
            "keylog_enabled": context.keylog_filename is not None,
            "context_options": int(context.options),
            "verify_flags": int(context.verify_flags),
            "security_level": int(context.security_level),
            "cipher_names_sha256": transport_cipher_names_sha256(context),
        },
        "resolver": {
            "policy": PROVIDER_RESOLVER_POLICY,
            "hostname": DEFAULT_UPSTREAM_HOST,
            "resolv_conf": _dependency_descriptor(PROVIDER_RESOLV_CONF_PATH),
            "nsswitch_conf": _dependency_descriptor(PROVIDER_NSSWITCH_PATH),
            "hosts_file": _dependency_descriptor(PROVIDER_HOSTS_PATH),
            "gai_conf": _dependency_descriptor(PROVIDER_GAI_CONF_PATH),
            "libc": _dependency_descriptor(_loaded_library_path("libc.so")),
            "libnss_dns": _dependency_descriptor(
                _system_library_path("libnss_dns.so.2")
            ),
            "libnss_files": _dependency_descriptor(
                _system_library_path("libnss_files.so.2")
            ),
            "resolved_addresses_frozen": False,
            "variability_classification": (
                PROVIDER_RESOLVER_VARIABILITY_CLASSIFICATION
            ),
        },
        "environment": {
            "required_absent": list(PROVIDER_TRANSPORT_ENV_REQUIRED_ABSENT),
            "observed_absent": list(PROVIDER_TRANSPORT_ENV_REQUIRED_ABSENT),
            "proxy_mode": PROVIDER_PROXY_MODE,
        },
    }
    return context, provenance


def _now() -> tuple[int, int]:
    return time.time_ns(), time.monotonic_ns()


def _normalize_request_metadata(headers: Mapping[str, str]) -> dict[str, str | None]:
    raw = headers.get("x-codex-turn-metadata")
    parsed: Any = None
    if raw:
        try:
            parsed = json.loads(raw)
        except (json.JSONDecodeError, TypeError, ValueError):
            parsed = None
    if not isinstance(parsed, Mapping):
        parsed = {}
    return {
        key: parsed.get(key) if isinstance(parsed.get(key), str) else None
        for key in _REQUEST_METADATA_KEYS
    }


def _empty_request_metadata() -> dict[str, None]:
    return {key: None for key in _REQUEST_METADATA_KEYS}


def _int_token(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 0:
        raise ProviderGateError(f"response usage {label} is not a nonnegative integer")
    return value


def normalize_provider_usage(value: Any) -> dict[str, int]:
    """Validate and normalize one cached-inclusive provider usage object."""

    if not isinstance(value, Mapping):
        raise ProviderGateError("response.completed usage is missing or malformed")
    input_tokens = _int_token(value.get("input_tokens"), "input_tokens")
    output_tokens = _int_token(value.get("output_tokens"), "output_tokens")
    total_tokens = _int_token(value.get("total_tokens"), "total_tokens")
    input_details = value.get("input_tokens_details")
    if input_details is None:
        input_details = {}
    if not isinstance(input_details, Mapping):
        raise ProviderGateError("response usage input_tokens_details is malformed")
    output_details = value.get("output_tokens_details")
    if output_details is None:
        output_details = {}
    if not isinstance(output_details, Mapping):
        raise ProviderGateError("response usage output_tokens_details is malformed")
    cached = _int_token(input_details.get("cached_tokens", 0), "cached_tokens")
    cache_write = _int_token(
        input_details.get("cache_write_tokens", 0), "cache_write_tokens"
    )
    reasoning = _int_token(
        output_details.get("reasoning_tokens", 0), "reasoning_tokens"
    )
    if total_tokens != input_tokens + output_tokens:
        raise ProviderGateError("response usage total is inconsistent")
    if cached > input_tokens:
        raise ProviderGateError("response cached tokens exceed input tokens")
    if cache_write > input_tokens:
        raise ProviderGateError("response cache-write tokens exceed input tokens")
    if reasoning > output_tokens:
        raise ProviderGateError("response reasoning tokens exceed output tokens")
    return {
        "input_tokens": input_tokens,
        "cached_input_tokens": cached,
        "cache_write_input_tokens": cache_write,
        "output_tokens": output_tokens,
        "reasoning_output_tokens": reasoning,
        "total_tokens": total_tokens,
    }


_SSE_CONTENT_TYPE_RE = re.compile(
    r'\A[ \t]*text/event-stream(?:[ \t]*;[ \t]*charset[ \t]*=[ \t]*'
    r'(?:utf-8|"utf-8"))?[ \t]*\Z',
    re.IGNORECASE,
)
_SSE_DIAGNOSTIC_TOKEN_RE = re.compile(
    rf"\A[A-Za-z0-9][A-Za-z0-9_.-]"
    rf"{{0,{PROVIDER_GATE_SSE_DIAGNOSTIC_TOKEN_MAX_LENGTH - 1}}}\Z"
)


def _safe_sse_diagnostic_token(value: Any) -> str:
    """Return a bounded inert token, or the deterministic safe fallback."""

    if (
        not isinstance(value, str)
        or _SSE_DIAGNOSTIC_TOKEN_RE.fullmatch(value) is None
    ):
        return "unknown"
    return value


def _safe_failed_response_code(event: Mapping[str, Any]) -> str:
    """Return only a bounded top-level or ``response.error.code`` diagnostic."""

    top_level_code = _safe_sse_diagnostic_token(event.get("code"))
    if top_level_code != "unknown":
        return top_level_code

    response = event.get("response")
    if not isinstance(response, Mapping):
        return "unknown"
    error = response.get("error")
    if not isinstance(error, Mapping):
        return "unknown"
    return _safe_sse_diagnostic_token(error.get("code"))


def _safe_incomplete_reason(event: Mapping[str, Any]) -> str:
    """Return only a bounded incomplete-details reason from official locations."""

    for owner in (event, event.get("response")):
        if not isinstance(owner, Mapping):
            continue
        details = owner.get("incomplete_details")
        if not isinstance(details, Mapping):
            continue
        reason = _safe_sse_diagnostic_token(details.get("reason"))
        if reason != "unknown":
            return reason
    return "unknown"


def _strict_json_object(data: str) -> dict[str, Any]:
    """Decode one RFC 8259 object without duplicate names or nonfinite numbers."""

    def object_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
        result: dict[str, Any] = {}
        for key, value in pairs:
            if key in result:
                raise ProviderGateError("Responses SSE JSON contains a duplicate key")
            result[key] = value
        return result

    def reject_constant(value: str) -> None:
        raise ProviderGateError(
            f"Responses SSE JSON contains nonfinite number {value}"
        )

    try:
        decoded = json.loads(
            data,
            object_pairs_hook=object_pairs,
            parse_constant=reject_constant,
        )
    except json.JSONDecodeError as exc:
        raise ProviderGateError("Responses SSE contains malformed JSON") from exc
    if not isinstance(decoded, dict):
        raise ProviderGateError("Responses SSE event is not a JSON object")
    return decoded


def _strict_sse_field(line: str) -> tuple[str, str]:
    if ":" in line:
        field, value = line.split(":", 1)
        if value.startswith(" "):
            value = value[1:]
    else:
        field, value = line, ""
    if field not in {"event", "data", "id", "retry"}:
        raise ProviderGateError("Responses SSE contains an unknown field")
    return field, value


def _carried_response_ids(event: Mapping[str, Any]) -> list[str]:
    """Return every response identity explicitly carried by one SSE event."""

    result: list[str] = []
    if "response_id" in event:
        result.append(
            _require_nonempty_string(event.get("response_id"), "event response_id")
        )
    response = event.get("response")
    if isinstance(response, Mapping) and "id" in response:
        result.append(_require_nonempty_string(response.get("id"), "response id"))
    return result


def _header_values(
    headers: Sequence[tuple[str, str]], name: str
) -> list[str]:
    values: list[str] = []
    for header_name, value in headers:
        if not isinstance(header_name, str) or not isinstance(value, str):
            raise ProviderGateError("upstream response headers are malformed")
        if header_name.lower() == name.lower():
            values.append(value)
    return values


def _content_type_basis(values: Sequence[str]) -> str:
    if not values:
        return "authenticated_stream_request_header_absent"
    if len(values) != 1:
        raise ProviderGateError("upstream_content_type_duplicated")
    if _SSE_CONTENT_TYPE_RE.fullmatch(values[0]) is None:
        raise ProviderGateError("upstream_content_type_invalid")
    return "declared_text_event_stream"


def _content_encoding_basis(values: Sequence[str]) -> str:
    if not values:
        return "implicit_identity_header_absent"
    if len(values) != 1:
        raise ProviderGateError("upstream_content_encoding_duplicated")
    if re.fullmatch(r"[ \t]*identity[ \t]*", values[0], re.IGNORECASE) is None:
        raise ProviderGateError("upstream_content_encoding_invalid")
    return "declared_identity"


_WAIT_AGENT_FUNCTION_CALL_KEYS = frozenset(
    {"type", "id", "call_id", "name", "namespace", "arguments"}
)
def _is_action_capable_output_type(item_type: str) -> bool:
    """Conservatively classify response output items that can request an action."""

    return item_type == "function_call" or item_type.endswith("_call")


def _optional_manifest_string(item: Mapping[str, Any], key: str) -> str | None:
    value = item.get(key)
    if value is None:
        return None
    return _require_nonempty_string(value, f"response output item {key}")


def _wait_agent_timeout_ms(item: Mapping[str, Any]) -> int | None:
    """Return the timeout only for the pinned client's exact wait semantics.

    The provider may add opaque envelope fields that the pinned Codex decoder
    ignores.  They cannot alter the dispatched tool: Codex uses only the
    function-call type, ids, name, namespace, and plaintext arguments checked
    below.  Requiring an exact provider envelope made valid completed waits
    depend on service-side serialization details.
    """

    item_keys = set(item)
    if not _WAIT_AGENT_FUNCTION_CALL_KEYS.issubset(item_keys):
        return None
    if "status" in item and item.get("status") not in (None, "completed"):
        return None
    if (
        item.get("type") != "function_call"
        or item.get("name") != "wait_agent"
        or item.get("namespace") != "collaboration"
    ):
        return None
    for key in ("id", "call_id"):
        value = item.get(key)
        if not isinstance(value, str) or not value.strip():
            return None
    arguments = item.get("arguments")
    if not isinstance(arguments, str):
        return None
    try:
        parsed = _strict_json_object(arguments)
    except ProviderGateError:
        return None
    if set(parsed) != {"timeout_ms"}:
        return None
    timeout_ms = parsed.get("timeout_ms")
    if (
        isinstance(timeout_ms, bool)
        or not isinstance(timeout_ms, int)
        or timeout_ms < PROVIDER_GATE_WAIT_AGENT_MIN_TIMEOUT_MS
        or timeout_ms > PROVIDER_GATE_WAIT_AGENT_MAX_TIMEOUT_MS
    ):
        return None
    return timeout_ms


def _response_output_manifest(
    response_id: str,
    output_items: Sequence[Mapping[str, Any]],
) -> dict[str, Any]:
    items: list[dict[str, Any]] = []
    action_capable_item_count = 0
    for index, raw_item in enumerate(output_items):
        item = dict(raw_item)
        item_type = _require_nonempty_string(
            item.get("type"), "response output item type"
        )
        if _is_action_capable_output_type(item_type):
            action_capable_item_count += 1
        payload = _canonical_json_bytes(item)
        arguments = item.get("arguments")
        if arguments is not None and not isinstance(arguments, str):
            raise ProviderGateError("response output item arguments are malformed")
        arguments_payload = (
            arguments.encode("utf-8") if isinstance(arguments, str) else None
        )
        items.append(
            {
                "index": index,
                "id": _optional_manifest_string(item, "id"),
                "type": item_type,
                "name": _optional_manifest_string(item, "name"),
                "namespace": _optional_manifest_string(item, "namespace"),
                "call_id": _optional_manifest_string(item, "call_id"),
                "payload_sha256": _sha256_bytes(payload),
                "payload_bytes": len(payload),
                "arguments_sha256": (
                    _sha256_bytes(arguments_payload)
                    if arguments_payload is not None
                    else None
                ),
                "arguments_bytes": (
                    len(arguments_payload) if arguments_payload is not None else None
                ),
                "wait_timeout_ms": _wait_agent_timeout_ms(item),
            }
        )
    manifest = {
        "schema_version": PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_SCHEMA_VERSION,
        "response_id": response_id,
        "output_item_count": len(items),
        "action_capable_item_count": action_capable_item_count,
        "items": items,
    }
    if set(manifest) != set(PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_KEYS) or any(
        set(item) != set(PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_ITEM_KEYS)
        for item in items
    ):
        raise ProviderGateError("internal response output manifest schema mismatch")
    return manifest


def _manifest_is_exact_collaboration_wait(manifest: Mapping[str, Any]) -> bool:
    items = manifest.get("items")
    if not isinstance(items, list):
        return False
    waits = [
        item
        for item in items
        if isinstance(item, Mapping) and item.get("wait_timeout_ms") is not None
    ]
    return (
        manifest.get("action_capable_item_count") == 1
        and len(waits) == 1
        and all(
            isinstance(item, Mapping)
            and (
                item is waits[0]
                or item.get("type") == "reasoning"
            )
            for item in items
        )
        and waits[0].get("type") == "function_call"
        and waits[0].get("name") == "wait_agent"
        and waits[0].get("namespace") == "collaboration"
        and isinstance(waits[0].get("id"), str)
        and isinstance(waits[0].get("call_id"), str)
    )


def _exact_interrupt_agent_manifest_item(
    manifest: Mapping[str, Any],
) -> Mapping[str, Any] | None:
    """Return the sole authenticated ``interrupt_agent`` item, if exact."""

    items = manifest.get("items")
    if (
        manifest.get("output_item_count") != 1
        or manifest.get("action_capable_item_count") != 1
        or not isinstance(items, list)
        or len(items) != 1
        or not isinstance(items[0], Mapping)
    ):
        return None
    item = items[0]
    if (
        item.get("index") != 0
        or item.get("type") != "function_call"
        or item.get("namespace") != "collaboration"
        or item.get("name") != "interrupt_agent"
        or not isinstance(item.get("id"), str)
        or not item["id"]
        or not isinstance(item.get("call_id"), str)
        or not item["call_id"]
        or not isinstance(item.get("arguments_sha256"), str)
        or not item["arguments_sha256"]
        or isinstance(item.get("arguments_bytes"), bool)
        or not isinstance(item.get("arguments_bytes"), int)
        or item["arguments_bytes"] <= 0
        or item.get("wait_timeout_ms") is not None
    ):
        return None
    return item


def _parse_sse_completed(
    body: bytes,
) -> tuple[
    str,
    dict[str, Any],
    dict[str, int],
    dict[str, Any],
    list[dict[str, Any]],
    dict[str, int],
    dict[str, Any],
]:
    try:
        text = body.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise ProviderGateError("Responses SSE is not UTF-8") from exc
    if text.startswith("\ufeff"):
        raise ProviderGateError("Responses SSE begins with a forbidden BOM")
    if "\x00" in text:
        raise ProviderGateError("Responses SSE contains a forbidden NUL")
    if "\r" in text.replace("\r\n", ""):
        raise ProviderGateError("Responses SSE contains a bare carriage return")
    normalized_text = text.replace("\r\n", "\n")
    if not normalized_text.endswith("\n\n"):
        raise ProviderGateError("Responses SSE has an unterminated final frame")

    completed: Mapping[str, Any] | None = None
    completed_index: int | None = None
    events: list[dict[str, Any]] = []
    carried_ids: list[str] = []
    done_count = 0
    terminal_seen = False
    frame_lines: list[str] = []
    output_items_done: dict[int, dict[str, Any]] = {}

    def consume_frame(lines: Sequence[str]) -> None:
        nonlocal completed, completed_index, done_count, terminal_seen
        event_name: str | None = None
        data_lines: list[str] = []
        identifier_seen = False
        retry_seen = False
        nonempty = False
        for line in lines:
            if line.startswith(":"):
                nonempty = True
                continue
            nonempty = True
            field, value = _strict_sse_field(line)
            if field == "event":
                if event_name is not None:
                    raise ProviderGateError("Responses SSE duplicates an event field")
                event_name = value
            elif field == "data":
                data_lines.append(value)
            elif field == "id":
                if identifier_seen:
                    raise ProviderGateError("Responses SSE duplicates an id field")
                identifier_seen = True
            else:
                if retry_seen:
                    raise ProviderGateError("Responses SSE duplicates a retry field")
                retry_seen = True
                if not value or not value.isascii() or not value.isdecimal():
                    raise ProviderGateError("Responses SSE retry field is malformed")
        if not nonempty:
            return
        if not data_lines:
            if event_name is not None:
                raise ProviderGateError("Responses SSE has an event field without data")
            if terminal_seen:
                raise ProviderGateError("Responses SSE has a frame after completion")
            return
        data = "\n".join(data_lines)
        if data == "[DONE]":
            if event_name is not None:
                raise ProviderGateError("Responses SSE DONE frame has an event field")
            if not terminal_seen or done_count != 0:
                raise ProviderGateError("Responses SSE DONE is misplaced or duplicated")
            done_count = 1
            return
        if terminal_seen:
            raise ProviderGateError("Responses SSE has an event after completion")
        event = _strict_json_object(data)
        event_type = _require_nonempty_string(event.get("type"), "SSE event type")
        if event_name is not None and event_name != event_type:
            raise ProviderGateError("Responses SSE event field disagrees with JSON type")
        if (
            event_type == "error"
            or event_type.endswith(".error")
            or event_type.endswith(".failed")
            or event_type.endswith(".incomplete")
        ):
            safe_event_type = _safe_sse_diagnostic_token(event_type)
            code = _safe_failed_response_code(event)
            incomplete_suffix = ""
            if event_type == "response.incomplete":
                incomplete_suffix = (
                    f", incomplete_reason={_safe_incomplete_reason(event)}"
                )
            raise ProviderGateError(
                "Responses SSE contains a failed response event "
                f"(event_type={safe_event_type}, code={code}{incomplete_suffix})"
            )
        carried_ids.extend(_carried_response_ids(event))
        events.append(copy.deepcopy(event))
        if event_type == "response.output_item.done":
            output_index = event.get("output_index")
            if (
                isinstance(output_index, bool)
                or not isinstance(output_index, int)
                or output_index < 0
            ):
                raise ProviderGateError(
                    "response.output_item.done has an invalid output_index"
                )
            item = event.get("item")
            if not isinstance(item, Mapping):
                raise ProviderGateError(
                    "response.output_item.done lacks an output item"
                )
            if output_index in output_items_done:
                raise ProviderGateError(
                    "Responses SSE duplicates a completed output index"
                )
            output_items_done[output_index] = copy.deepcopy(dict(item))
        if event_type == "response.completed":
            if completed is not None:
                raise ProviderGateError(
                    "Responses SSE contains multiple response.completed events"
                )
            completed = event
            completed_index = len(events) - 1
            terminal_seen = True

    for line in normalized_text.split("\n"):
        if line:
            if done_count:
                raise ProviderGateError("Responses SSE has data after DONE")
            frame_lines.append(line)
            continue
        consume_frame(frame_lines)
        frame_lines = []
    if frame_lines:
        raise ProviderGateError("Responses SSE has an unterminated final frame")
    if completed is None or completed_index != len(events) - 1:
        raise ProviderGateError(
            "Responses SSE must end with exactly one response.completed event"
        )
    response = completed.get("response")
    if not isinstance(response, Mapping):
        raise ProviderGateError("response.completed lacks a response object")
    if response.get("status") in {"failed", "incomplete"} or response.get(
        "error"
    ) is not None:
        raise ProviderGateError("response.completed carries a failed response")
    response_id = _require_nonempty_string(response.get("id"), "response id")
    if any(item != response_id for item in carried_ids):
        raise ProviderGateError("Responses SSE carries conflicting response IDs")
    usage = response.get("usage")
    if not isinstance(usage, Mapping):
        raise ProviderGateError("response.completed lacks exact usage")
    completed_output = response.get("output")
    if not isinstance(completed_output, list) or not all(
        isinstance(item, Mapping) for item in completed_output
    ):
        raise ProviderGateError("response.completed lacks an exact output array")
    expected_indices = list(range(len(output_items_done)))
    if sorted(output_items_done) != expected_indices:
        raise ProviderGateError("Responses SSE completed output indices are not contiguous")
    done_output = [output_items_done[index] for index in expected_indices]
    if completed_output and not _same_json_value(completed_output, done_output):
        raise ProviderGateError(
            "response.completed output disagrees with output_item.done"
        )
    raw_usage = copy.deepcopy(dict(usage))
    return (
        response_id,
        raw_usage,
        normalize_provider_usage(raw_usage),
        copy.deepcopy(dict(completed)),
        events,
        {
            "json_event_count": len(events),
            "completed_event_index": completed_index,
            "done_count": done_count,
        },
        _response_output_manifest(response_id, done_output),
    )


def sanitized_completion_event(
    response_id: str,
    usage: Mapping[str, Any],
    completed_event: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Return the action-free completion event exposed at a terminal boundary."""
    del completed_event
    return {
        "type": "response.completed",
        "response": {
            "id": _require_nonempty_string(response_id, "response id"),
            "usage": copy.deepcopy(dict(usage)),
            "end_turn": True,
            "output": [],
        },
    }


def sanitized_completion_body(
    response_id: str,
    usage: Mapping[str, Any],
    completed_event: Mapping[str, Any] | None = None,
) -> bytes:
    """Build the sole safe SSE frame exposed for a quarantined completion."""

    payload = sanitized_completion_event(response_id, usage, completed_event)
    return _canonical_sse_body([payload])


def _canonical_sse_body(events: Sequence[Mapping[str, Any]]) -> bytes:
    chunks: list[bytes] = []
    for event in events:
        event_type = _require_nonempty_string(event.get("type"), "SSE event type")
        data = json.dumps(
            event, sort_keys=True, separators=(",", ":"), ensure_ascii=False
        ).encode("utf-8")
        chunks.append(b"event: " + event_type.encode("ascii") + b"\ndata: " + data + b"\n\n")
    return b"".join(chunks)


def sanitized_compaction_completion_events(
    response_id: str,
    usage: Mapping[str, Any],
    upstream_events: Sequence[Mapping[str, Any]],
    completed_event: Mapping[str, Any] | None = None,
) -> list[dict[str, Any]]:
    """Return the minimal non-action-capable wire accepted by remote compaction v2."""

    output_items: list[Mapping[str, Any]] = []
    for event in upstream_events:
        if event.get("type") != "response.output_item.done":
            continue
        item = event.get("item")
        if not isinstance(item, Mapping):
            raise ProviderGateError("compaction output-item event is malformed")
        output_items.append(item)
    if len(output_items) != 1 or output_items[0].get("type") != "compaction":
        raise ProviderGateError(
            "compaction crossing must contain exactly one compaction output item"
        )
    encrypted_content = output_items[0].get("encrypted_content")
    if not isinstance(encrypted_content, str) or not encrypted_content:
        raise ProviderGateError("compaction crossing lacks encrypted content")
    compaction_event = {
        "type": "response.output_item.done",
        "item": {
            "type": "compaction",
            "encrypted_content": encrypted_content,
        },
    }
    return [
        compaction_event,
        sanitized_completion_event(response_id, usage, completed_event),
    ]


def _prompt_release_digest(record: Mapping[str, Any]) -> str:
    return _sha256_bytes(_canonical_json_bytes(record))


def _authenticated_record_sha256(record: Mapping[str, Any], hash_field: str) -> str:
    unsigned = {key: value for key, value in record.items() if key != hash_field}
    encoded = json.dumps(
        unsigned, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    return _sha256_bytes(encoded)


class ProviderTokenGate:
    """One-attempt trusted provider gate and durable evidence ledger."""

    def __init__(
        self,
        live_state_path: os.PathLike[str] | str,
        final_artifact_path: os.PathLike[str] | str,
        *,
        token_limit: int,
        response_bound: int = DEFAULT_RESPONSE_BOUND,
        model_catalog_sha256: str,
        model_entry_sha256: str,
        capability_nonce: str | None = None,
        _connection_factory: Callable[[], Any] | None = None,
        max_request_bytes: int = DEFAULT_MAX_REQUEST_BYTES,
        max_response_bytes: int = DEFAULT_MAX_RESPONSE_BYTES,
    ) -> None:
        if isinstance(token_limit, bool) or not isinstance(token_limit, int) or token_limit < 1:
            raise ProviderGateError("token_limit must be a positive integer")
        if (
            isinstance(response_bound, bool)
            or not isinstance(response_bound, int)
            or response_bound < 1
        ):
            raise ProviderGateError("response_bound must be a positive integer")
        self.live_state_path = Path(live_state_path).resolve()
        self.final_artifact_path = Path(final_artifact_path).resolve()
        if self.live_state_path == self.final_artifact_path:
            raise ProviderGateError("live and final artifact paths must differ")
        self.token_limit = token_limit
        self.response_bound = response_bound
        self.model_catalog_sha256 = _require_sha256(
            model_catalog_sha256, "model_catalog_sha256"
        )
        self.model_entry_sha256 = _require_sha256(
            model_entry_sha256, "model_entry_sha256"
        )
        self._implementation_source_sha256 = _source_sha256()
        self._capability_nonce = capability_nonce or secrets.token_urlsafe(32)
        if (
            not isinstance(self._capability_nonce, str)
            or len(self._capability_nonce) < 24
            or "/" in self._capability_nonce
        ):
            raise ProviderGateError("capability_nonce must be at least 24 safe characters")
        self._tls_context, self._transport_provenance = build_transport_provenance()
        if _connection_factory is None:
            self._connection_factory_mode = PROVIDER_CONNECTION_FACTORY_EXPLICIT_TLS
            self._connection_factory = lambda: http.client.HTTPSConnection(
                DEFAULT_UPSTREAM_HOST,
                DEFAULT_UPSTREAM_PORT,
                timeout=1800,
                context=self._tls_context,
            )
        else:
            self._connection_factory_mode = PROVIDER_CONNECTION_FACTORY_TEST_OVERRIDE
            self._transport_provenance["connection_factory_mode"] = (
                PROVIDER_CONNECTION_FACTORY_TEST_OVERRIDE
            )
            self._connection_factory = _connection_factory
        self.max_request_bytes = max_request_bytes
        self.max_response_bytes = max_response_bytes

        self._condition = threading.Condition(threading.RLock())
        self._crossing_event = threading.Event()
        self._phase = PHASE_CONCURRENT
        self._completed_tokens = 0
        self._close_reason: str | None = None
        self._terminal_close_reason: str | None = None
        self._crossing: dict[str, Any] | None = None
        self._poison_reasons: list[str] = []
        self._open: dict[str, dict[str, Any]] = {}
        self._calls: list[dict[str, Any]] = []
        self._calls_by_id: dict[str, dict[str, Any]] = {}
        self._calls_by_response_id: dict[str, dict[str, Any]] = {}
        self._transitions: list[dict[str, Any]] = []
        self._denials: list[dict[str, Any]] = []
        self._setup_requests: list[dict[str, Any]] = []
        self._sequence = 0
        self._post_close_upstream_count = 0
        self._active_handlers = 0
        self._accepting_handlers = True
        self._bindings: dict[str, Any] = {
            "root_thread_id": None,
            "run_id": None,
            "model": None,
            "reasoning_effort": None,
            "prompt_release_sha256": None,
            "prompt_release_protocol": None,
            "prompt_sha256": None,
        }
        self._started = False
        self._stopped = False
        self._finalized = False
        self._server: ThreadingHTTPServer | None = None
        self._server_thread: threading.Thread | None = None
        self._port: int | None = None
        self._lifecycle = {
            "started_unix_ns": None,
            "started_monotonic_ns": None,
            "stopped_unix_ns": None,
            "stopped_monotonic_ns": None,
            "finalized_unix_ns": None,
            "finalized_monotonic_ns": None,
        }

    @property
    def base_url(self) -> str:
        with self._condition:
            if not self._started or self._port is None:
                raise ProviderGateError("provider gate has not started")
            return (
                f"http://127.0.0.1:{self._port}/{self._capability_nonce}"
                f"{DEFAULT_UPSTREAM_BASE_PATH}"
            )

    def static_record(self) -> dict[str, Any]:
        return {
            "schema_version": PROVIDER_GATE_SCHEMA_VERSION,
            "protocol": PROVIDER_GATE_PROTOCOL,
            "implementation": {
                "name": PROVIDER_GATE_IMPLEMENTATION_NAME,
                "version": PROVIDER_GATE_IMPLEMENTATION_VERSION,
                "source_sha256": self._implementation_source_sha256,
            },
            "configuration": {
                "token_limit": self.token_limit,
                "response_bound": self.response_bound,
                "response_bound_enforcement": (
                    "runtime_fail_closed_before_buffered_response_release"
                ),
                "model_catalog_sha256": self.model_catalog_sha256,
                "model_entry_sha256": self.model_entry_sha256,
                "strict_admission_inequality": (
                    "completed_tokens + (open_request_count + 1) * "
                    "response_bound < token_limit"
                ),
                "upstream_origin": DEFAULT_UPSTREAM_ORIGIN,
                "upstream_base_path": DEFAULT_UPSTREAM_BASE_PATH,
                "loopback_only": True,
                "capability_persisted": False,
                "websockets_supported": False,
                "request_retries": 0,
                "stream_retries": 0,
                "request_compression": False,
                "response_compression": "identity",
                "counted_route": f"{COUNTED_METHOD} {COUNTED_ROUTE}",
                "counted_request_kinds": list(
                    PROVIDER_GATE_COUNTED_REQUEST_KINDS
                ),
                "rejected_inference_routes": [
                    f"POST {route}" for route in REJECTED_INFERENCE_ROUTES
                ],
                "allowed_setup_route_prefixes": list(ALLOWED_SETUP_ROUTE_PREFIXES),
                "crossing_release_policy": CROSSING_RELEASE_POLICY,
                "upstream_response_contract": {
                    "schema_version": (
                        PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_SCHEMA_VERSION
                    ),
                    "protocol": PROVIDER_GATE_UPSTREAM_RESPONSE_PROTOCOL,
                    "success_status": 200,
                    "content_type_policy": PROVIDER_GATE_CONTENT_TYPE_POLICY,
                    "content_encoding_policy": (
                        PROVIDER_GATE_CONTENT_ENCODING_POLICY
                    ),
                    "outbound_accept": PROVIDER_GATE_OUTBOUND_ACCEPT,
                    "parser": PROVIDER_GATE_SSE_PARSER,
                    "downstream_content_type": (
                        PROVIDER_GATE_DOWNSTREAM_CONTENT_TYPE
                    ),
                    "downstream_content_encoding": (
                        PROVIDER_GATE_DOWNSTREAM_CONTENT_ENCODING
                    ),
                },
                "transport_provenance": copy.deepcopy(self._transport_provenance),
            },
        }

    def _assert_transport_runtime_locked(self) -> None:
        """Fail before send if any frozen transport input changed at runtime."""

        try:
            _fresh_context, current = build_transport_provenance()
        except ProviderGateError as exc:
            raise ProviderGateError(
                "transport_provenance_runtime_check_failed"
            ) from exc
        current["connection_factory_mode"] = self._connection_factory_mode
        if current != self._transport_provenance:
            raise ProviderGateError("transport_provenance_runtime_mismatch")

    def bind_root(
        self,
        root_thread_id: str,
        *,
        run_id: str,
        model: str,
        reasoning_effort: str,
    ) -> None:
        values = {
            "root_thread_id": _require_nonempty_string(root_thread_id, "root_thread_id"),
            "run_id": _require_nonempty_string(run_id, "run_id"),
            "model": _require_nonempty_string(model, "model"),
            "reasoning_effort": _require_nonempty_string(
                reasoning_effort, "reasoning_effort"
            ),
        }
        with self._condition:
            if self._bindings["root_thread_id"] is not None:
                if any(self._bindings[key] != value for key, value in values.items()):
                    self._poison_locked("conflicting_root_binding")
                    raise ProviderGateError("provider gate root binding conflicts")
                return
            self._bindings.update(values)
            self._persist_locked()
            self._condition.notify_all()

    def _next_sequence_locked(self) -> int:
        self._sequence += 1
        return self._sequence

    def _bindings_complete_locked(self) -> bool:
        return all(self._bindings[key] is not None for key in PROVIDER_GATE_BINDING_KEYS)

    def _transition_locked(
        self, to_phase: str, reason: str, call_id: str | None = None
    ) -> None:
        if to_phase not in PROVIDER_GATE_PHASES:
            raise ProviderGateError(f"invalid provider-gate phase: {to_phase}")
        if self._phase == to_phase:
            return
        unix_ns, monotonic_ns = _now()
        transition = {
            "sequence": self._next_sequence_locked(),
            "from_phase": self._phase,
            "to_phase": to_phase,
            "reason": reason,
            "call_id": call_id,
            "unix_ns": unix_ns,
            "monotonic_ns": monotonic_ns,
        }
        self._phase = to_phase
        self._transitions.append(transition)

    def _poison_locked(self, reason: str) -> None:
        if self._finalized:
            raise ProviderGateError("provider gate cannot mutate after finalization")
        if reason not in self._poison_reasons:
            self._poison_reasons.append(reason)
        self._close_reason = CLOSE_REASON_POISON
        self._terminal_close_reason = CLOSE_REASON_POISON
        if self._phase != PHASE_POISONED:
            self._transition_locked(PHASE_POISONED, reason)
        self._crossing_event.set()
        self._condition.notify_all()
        self._persist_locked()

    def _record_denial_locked(
        self,
        *,
        method: str,
        route: str,
        reason: str,
        request_metadata: Mapping[str, Any] | None = None,
    ) -> dict[str, Any]:
        unix_ns, monotonic_ns = _now()
        sequence = self._next_sequence_locked()
        record = {
            "sequence": sequence,
            "denial_id": f"deny-{sequence:08d}",
            "method": method,
            "route": route,
            "reason": reason,
            "phase": self._phase,
            "upstream_started": False,
            "unix_ns": unix_ns,
            "monotonic_ns": monotonic_ns,
            "request_metadata": dict(request_metadata or _empty_request_metadata()),
        }
        self._denials.append(record)
        self._persist_locked()
        return record

    def _state_locked(self) -> dict[str, Any]:
        no_open = not self._open
        no_post_close = self._no_post_close_upstream_locked()
        crossing_closed = bool(
            self._phase == PHASE_CLOSED
            and self._close_reason == CLOSE_REASON_TOKEN_LIMIT
            and self._crossing is not None
            and self._crossing.get("sole_inflight") is True
            and no_open
            and no_post_close
        )
        return {
            "phase": self._phase,
            "close_reason": self._close_reason,
            "completed_tokens": self._completed_tokens,
            "crossing": copy.deepcopy(self._crossing),
            "crossing_closed": crossing_closed,
            "open_request_ids": sorted(self._open),
            "all_complete": no_open and all(
                call.get("upstream_started") is False
                or call.get("commit_monotonic_ns") is not None
                or call.get("error") is not None
                for call in self._calls
            ),
            "no_post_close_upstream": no_post_close,
            "poisoned": self._phase == PHASE_POISONED,
            "poison_reasons": list(self._poison_reasons),
            "active_handler_count": self._active_handlers,
            "handlers_quiescent": self._active_handlers == 0,
            "sequence": self._sequence,
        }

    def _no_post_close_upstream_locked(self) -> bool:
        terminal_times = [
            transition["monotonic_ns"]
            for transition in self._transitions
            if transition["to_phase"] in (PHASE_CLOSED, PHASE_POISONED)
        ]
        if not terminal_times:
            return self._post_close_upstream_count == 0
        cutoff = min(terminal_times)
        call_starts = [
            call["upstream_start_monotonic_ns"]
            for call in self._calls
            if call.get("upstream_started") is True
        ]
        return self._post_close_upstream_count == 0 and all(
            isinstance(start, int) and start <= cutoff
            for start in call_starts
        )

    def _invariants_locked(self) -> dict[str, bool]:
        completed_calls = [
            call for call in self._calls if call.get("normalized_usage") is not None
        ]
        totals = [call["normalized_usage"]["total_tokens"] for call in completed_calls]
        response_ids = [call["response_id"] for call in completed_calls]
        strict_safe = all(
            call["admission_mode"] != ADMISSION_MODE_CONCURRENT
            or call["reservation_after"] < self.token_limit
            for call in self._calls
        )
        exclusive_serial = all(
            call["admission_mode"] != ADMISSION_MODE_EXCLUSIVE
            or call["open_before"] == 0
            for call in self._calls
        )
        crossing_sole = self._crossing is None or self._crossing.get("sole_inflight") is True
        crossing_rewritten = self._crossing is None or any(
            call.get("call_id") == self._crossing.get("call_id")
            and call.get("release_kind")
            in (
                RELEASE_SANITIZED_CROSSING,
                RELEASE_SANITIZED_COMPACTION_CROSSING,
            )
            for call in self._calls
        )
        all_deliveries_reconciled = all(
            call.get("normalized_usage") is None
            or call.get("appserver_delivery") is not None
            for call in self._calls
        )
        all_within_bound = all(total <= self.response_bound for total in totals)
        return {
            "bindings_complete": self._bindings_complete_locked(),
            "completed_sum_matches": sum(totals) == self._completed_tokens,
            "usage_consistent": all(
                item["total_tokens"] == item["input_tokens"] + item["output_tokens"]
                and item["cached_input_tokens"] <= item["input_tokens"]
                and item["cache_write_input_tokens"] <= item["input_tokens"]
                and item["reasoning_output_tokens"] <= item["output_tokens"]
                for item in (
                    call["normalized_usage"] for call in completed_calls
                )
            ),
            "all_response_totals_within_bound": all_within_bound,
            "response_ids_unique": len(response_ids) == len(set(response_ids)),
            "strict_reservation_safe": strict_safe,
            "exclusive_serial": exclusive_serial,
            "crossing_sole_inflight": crossing_sole,
            "crossing_rewritten": crossing_rewritten,
            "no_action_capable_output_frames_on_crossing": crossing_rewritten,
            "no_post_close_upstream": self._no_post_close_upstream_locked(),
            "all_admitted_terminal": not self._open,
            "all_appserver_deliveries_reconciled": all_deliveries_reconciled,
            "no_open_requests": not self._open,
            "not_poisoned": self._phase != PHASE_POISONED,
        }

    def _record_locked(self, *, final: bool) -> dict[str, Any]:
        static = self.static_record()
        record = {
            **static,
            "bindings": copy.deepcopy(self._bindings),
            "lifecycle": copy.deepcopy(self._lifecycle),
            "state": self._state_locked(),
            "calls": copy.deepcopy(self._calls),
            "transitions": copy.deepcopy(self._transitions),
            "denials": copy.deepcopy(self._denials),
            "setup_requests": copy.deepcopy(self._setup_requests),
            "invariants": self._invariants_locked(),
            "canonical_encoding": PROVIDER_GATE_CANONICAL_ENCODING,
            "sealed_mode": PROVIDER_GATE_SEALED_MODE if final else "0600-live",
        }
        return _self_hashed(record)

    def _persist_locked(self) -> None:
        if not self._started or self._finalized:
            return
        record = self._record_locked(final=False)
        payload = _canonical_json_bytes(record)
        path = self.live_state_path
        path.parent.mkdir(parents=True, exist_ok=True)
        temporary = path.with_name(
            f".{path.name}.{os.getpid()}.{threading.get_ident()}.tmp"
        )
        descriptor = os.open(
            temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC, 0o600
        )
        try:
            offset = 0
            while offset < len(payload):
                written = os.write(descriptor, payload[offset:])
                if written <= 0:
                    raise ProviderGateError("short write of provider-gate live state")
                offset += written
            os.fsync(descriptor)
        finally:
            os.close(descriptor)
        os.replace(temporary, path)
        os.chmod(path, 0o600)
        directory_fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
        try:
            os.fsync(directory_fd)
        finally:
            os.close(directory_fd)

    def snapshot(self) -> dict[str, Any]:
        with self._condition:
            return copy.deepcopy(self._state_locked())

    def wait_for_crossing(self, timeout: float | None = None) -> Mapping[str, Any] | None:
        if not self._crossing_event.wait(timeout):
            return None
        with self._condition:
            return copy.deepcopy(self._crossing)

    def close(self, reason: str) -> dict[str, Any]:
        if reason not in (
            CLOSE_REASON_ACCEPTED_SUBMISSION,
            CLOSE_REASON_NATURAL_END,
            CLOSE_REASON_SYSTEM_ERROR,
        ):
            raise ProviderGateError("explicit close reason is invalid")
        with self._condition:
            won = self._close_reason is None and self._phase not in (
                PHASE_CLOSED,
                PHASE_POISONED,
            )
            if won:
                if self._open:
                    self._poison_locked(f"{reason}_boundary_with_open_provider_request")
                    won = False
                elif any(
                    call.get("normalized_usage") is not None
                    and call.get("appserver_delivery") is None
                    for call in self._calls
                ):
                    self._poison_locked(
                        f"{reason}_boundary_before_appserver_delivery"
                    )
                    won = False
                elif self._calls and (
                    max(
                        (
                            call
                            for call in self._calls
                            if call.get("normalized_usage") is not None
                        ),
                        key=lambda call: (
                            call["commit_monotonic_ns"], call["sequence"]
                        ),
                        default={},
                    ).get("appserver_delivery", {}).get("kind")
                    != PROVIDER_GATE_DELIVERY_DIRECT
                ):
                    self._poison_locked(f"{reason}_boundary_after_suppressed_wait")
                    won = False
                elif self._crossing is not None and (
                    self._calls_by_id[self._crossing["call_id"]]
                    .get("appserver_delivery", {})
                    .get("kind")
                    != PROVIDER_GATE_DELIVERY_DIRECT
                ):
                    self._poison_locked(f"{reason}_crossing_without_direct_delivery")
                    won = False
                else:
                    self._terminal_close_reason = reason
                    self._close_reason = reason
                    self._transition_locked(PHASE_CLOSED, f"terminal_close:{reason}")
                    self._crossing_event.set()
                    self._persist_locked()
                    self._condition.notify_all()
            requested_sequence = self._sequence
            return {
                "won": won,
                "requested_reason": reason,
                "effective_reason": self._close_reason,
                "phase": self._phase,
                "sequence": requested_sequence,
            }

    def close_for_accepted_submission(self) -> dict[str, Any]:
        return self.close(CLOSE_REASON_ACCEPTED_SUBMISSION)

    def bind_prompt_release(self, record: Mapping[str, Any]) -> None:
        if not isinstance(record, Mapping):
            raise ProviderGateError("prompt release record must be a mapping")
        release_sha = _require_sha256(record.get("release_sha256"), "release_sha256")
        if _authenticated_record_sha256(record, "release_sha256") != release_sha:
            raise ProviderGateError("prompt release has an invalid release_sha256")
        digest = _prompt_release_digest(record)
        protocol = record.get("protocol_version")
        prompt_sha = record.get("effective_prompt_sha256")
        values = {
            "prompt_release_sha256": digest,
            "prompt_release_protocol": _require_nonempty_string(
                protocol, "prompt release protocol"
            ),
            "prompt_sha256": _require_sha256(prompt_sha, "prompt_sha256"),
        }
        with self._condition:
            if self._bindings["root_thread_id"] is None:
                self._poison_locked("prompt_release_before_root_binding")
                raise ProviderGateError("root identity must be bound before prompt release")
            identity_fields = {
                "root_thread_id": "root_thread_id",
                "run_id": "run_id",
                "model": "model",
                "reasoning_effort": "reasoning_effort",
            }
            for release_field, binding_field in identity_fields.items():
                if record.get(release_field) != self._bindings[binding_field]:
                    self._poison_locked(
                        f"prompt_release_{release_field}_binding_mismatch"
                    )
                    raise ProviderGateError(
                        f"prompt release {release_field} disagrees with root binding"
                    )
            if self._bindings["prompt_release_sha256"] is not None:
                if any(self._bindings[key] != value for key, value in values.items()):
                    self._poison_locked("conflicting_prompt_release_binding")
                    raise ProviderGateError("provider gate prompt-release binding conflicts")
                return
            self._bindings.update(values)
            self._persist_locked()
            self._condition.notify_all()

    def _make_handler_class(self) -> type[BaseHTTPRequestHandler]:
        gate = self

        class Handler(BaseHTTPRequestHandler):
            protocol_version = "HTTP/1.1"

            def do_GET(self) -> None:  # noqa: N802 - stdlib handler API
                gate._handle_http(self)

            def do_POST(self) -> None:  # noqa: N802 - stdlib handler API
                gate._handle_http(self)

            def do_PUT(self) -> None:  # noqa: N802 - stdlib handler API
                gate._handle_http(self)

            def do_PATCH(self) -> None:  # noqa: N802 - stdlib handler API
                gate._handle_http(self)

            def do_DELETE(self) -> None:  # noqa: N802 - stdlib handler API
                gate._handle_http(self)

            def do_HEAD(self) -> None:  # noqa: N802 - stdlib handler API
                gate._handle_http(self)

            def log_message(self, _format: str, *args: Any) -> None:
                # Request paths include the capability and headers can contain
                # credentials.  The trusted artifact is the only gate log.
                del args

        return Handler

    def start(self) -> str:
        with self._condition:
            if self._started:
                raise ProviderGateError("provider gate was started twice")
            for path in (self.live_state_path, self.final_artifact_path):
                try:
                    path.lstat()
                except FileNotFoundError:
                    pass
                else:
                    raise ProviderGateError(
                        f"provider-gate output already exists: {path.name}"
                    )
            self.live_state_path.parent.mkdir(parents=True, exist_ok=True)
            self.final_artifact_path.parent.mkdir(parents=True, exist_ok=True)
            if self.live_state_path.parent != self.final_artifact_path.parent:
                raise ProviderGateError("provider-gate outputs must share one directory")
            server = ThreadingHTTPServer(("127.0.0.1", 0), self._make_handler_class())
            server.daemon_threads = True
            self._server = server
            self._port = int(server.server_address[1])
            self._started = True
            started_unix_ns, started_monotonic_ns = _now()
            self._lifecycle["started_unix_ns"] = started_unix_ns
            self._lifecycle["started_monotonic_ns"] = started_monotonic_ns
            self._persist_locked()
            thread = threading.Thread(
                target=server.serve_forever,
                name="highambench-provider-token-gate",
                daemon=True,
            )
            self._server_thread = thread
            thread.start()
            return self.base_url

    @staticmethod
    def _send_local_error(
        handler: BaseHTTPRequestHandler, status: int, code: str, message: str
    ) -> None:
        body = _canonical_json_bytes(
            {
                "error": {
                    "code": code,
                    "message": message,
                    "type": "invalid_request_error",
                }
            }
        )
        handler.send_response(status)
        handler.send_header("Content-Type", "application/json")
        handler.send_header("Content-Length", str(len(body)))
        handler.send_header("Connection", "close")
        handler.send_header("x-highambench-provider-gate-error", code)
        handler.end_headers()
        if handler.command != "HEAD":
            try:
                handler.wfile.write(body)
                handler.wfile.flush()
            except (BrokenPipeError, ConnectionError, OSError):
                pass
        handler.close_connection = True

    def _route_for_handler(
        self, handler: BaseHTTPRequestHandler
    ) -> tuple[str, str] | None:
        target = urlsplit(handler.path)
        prefix = f"/{self._capability_nonce}{DEFAULT_UPSTREAM_BASE_PATH}"
        if (
            target.scheme
            or target.netloc
            or not target.path.startswith(prefix)
            or (len(target.path) > len(prefix) and target.path[len(prefix)] != "/")
        ):
            return None
        suffix = target.path[len(prefix) :] or "/"
        if "%" in suffix or "//" in suffix or "/../" in f"{suffix}/":
            return None
        return suffix, target.query

    def _handle_http(self, handler: BaseHTTPRequestHandler) -> None:
        with self._condition:
            if not self._accepting_handlers:
                accepted = False
            else:
                accepted = True
                self._active_handlers += 1
                self._persist_locked()
        if not accepted:
            self._send_local_error(
                handler, 409, "provider_gate_stopped", "provider gate is stopped"
            )
            return
        try:
            self._handle_http_active(handler)
        finally:
            with self._condition:
                self._active_handlers -= 1
                if self._active_handlers < 0:
                    self._active_handlers = 0
                    self._poison_locked("negative_active_handler_count")
                self._persist_locked()
                self._condition.notify_all()

    def _handle_http_active(self, handler: BaseHTTPRequestHandler) -> None:
        method = handler.command.upper()
        metadata = _normalize_request_metadata(handler.headers)
        route = self._route_for_handler(handler)
        if route is None:
            with self._condition:
                self._record_denial_locked(
                    method=method,
                    route="<capability-or-path-mismatch>",
                    reason="capability_or_path_mismatch",
                    request_metadata=metadata,
                )
            self._send_local_error(handler, 404, "gate_route_not_found", "route not found")
            return
        suffix, query = route
        if suffix in REJECTED_INFERENCE_ROUTES:
            with self._condition:
                self._record_denial_locked(
                    method=method,
                    route=suffix,
                    reason="unmetered_inference_route_rejected",
                    request_metadata=metadata,
                )
            self._send_local_error(
                handler,
                422,
                "unmetered_inference_route_rejected",
                "this inference route is disabled",
            )
            return
        if method == COUNTED_METHOD and suffix == COUNTED_ROUTE and not query:
            if (
                any(
                    not isinstance(metadata.get(key), str) or not metadata[key]
                    for key in _REQUEST_METADATA_KEYS
                )
                or metadata.get("request_kind")
                not in PROVIDER_GATE_COUNTED_REQUEST_KINDS
            ):
                with self._condition:
                    self._record_denial_locked(
                        method=method,
                        route=suffix,
                        reason="missing_or_unsupported_request_metadata",
                        request_metadata=metadata,
                    )
                self._send_local_error(
                    handler,
                    422,
                    "missing_or_unsupported_request_metadata",
                    "counted provider request metadata is incomplete",
                )
                return
            self._handle_counted(handler, metadata)
            return
        with self._condition:
            self._record_denial_locked(
                method=method,
                route=suffix,
                reason="unknown_or_disallowed_route",
                request_metadata=metadata,
            )
        self._send_local_error(
            handler, 404, "unknown_or_disallowed_route", "route not found"
        )

    def _read_request_body(
        self, handler: BaseHTTPRequestHandler
    ) -> tuple[bytes, str, bool]:
        transfer_encoding = handler.headers.get("Transfer-Encoding")
        if transfer_encoding:
            raise _LocalDenial(
                422, "chunked_request_rejected", "chunked requests are disabled"
            )
        content_encoding = (handler.headers.get("Content-Encoding") or "identity").lower()
        if content_encoding not in ("", "identity"):
            raise _LocalDenial(
                422,
                "compressed_request_rejected",
                "request compression is disabled",
            )
        raw_length = handler.headers.get("Content-Length")
        try:
            length = int(raw_length) if raw_length is not None else -1
        except ValueError as exc:
            raise _LocalDenial(
                400, "invalid_content_length", "invalid Content-Length"
            ) from exc
        if length < 0 or length > self.max_request_bytes:
            raise _LocalDenial(
                413, "request_body_size_rejected", "request body size is invalid"
            )
        body = handler.rfile.read(length)
        if len(body) != length:
            raise _LocalDenial(
                400, "short_request_body", "request body ended unexpectedly"
            )
        try:
            decoded = json.loads(body)
        except (UnicodeDecodeError, json.JSONDecodeError) as exc:
            raise _LocalDenial(
                400, "malformed_request_json", "request body is not valid JSON"
            ) from exc
        if not isinstance(decoded, Mapping):
            raise _LocalDenial(
                400, "malformed_request_json", "request body must be a JSON object"
            )
        request_model = decoded.get("model")
        if not isinstance(request_model, str) or not request_model:
            raise _LocalDenial(
                422, "request_model_missing", "request model is required"
            )
        if decoded.get("stream") is not True:
            raise _LocalDenial(
                422, "streaming_required", "counted Responses requests must stream"
            )
        return body, request_model, True

    @staticmethod
    def _outbound_headers(
        incoming: Mapping[str, str], body_length: int | None
    ) -> dict[str, str]:
        result: dict[str, str] = {}
        for name, value in incoming.items():
            lower = name.lower()
            if (
                lower in _HOP_BY_HOP_HEADERS
                or lower in {"host", "content-length", "accept", "accept-encoding"}
                or lower.startswith("x-highambench-provider-gate-")
            ):
                continue
            result[name] = value
        result["Host"] = DEFAULT_UPSTREAM_HOST
        result["Accept"] = PROVIDER_GATE_OUTBOUND_ACCEPT
        result["Accept-Encoding"] = "identity"
        if body_length is not None:
            result["Content-Length"] = str(body_length)
        return result

    @staticmethod
    def _read_upstream_response(response: Any, maximum: int) -> bytes:
        body = response.read(maximum + 1)
        if len(body) > maximum:
            raise ProviderGateError("upstream response exceeds trusted buffer limit")
        return body

    def _admit_counted_locked(
        self,
        *,
        body: bytes,
        request_model: str,
        request_stream: bool,
        headers: Mapping[str, str],
        metadata: Mapping[str, Any],
    ) -> dict[str, Any]:
        while not self._bindings_complete_locked() and self._phase not in (
            PHASE_CLOSED,
            PHASE_POISONED,
        ):
            self._condition.wait(timeout=0.25)
        if self._bindings_complete_locked() and request_model != self._bindings["model"]:
            self._record_denial_locked(
                method=COUNTED_METHOD,
                route=COUNTED_ROUTE,
                reason="request_model_binding_mismatch",
                request_metadata=metadata,
            )
            raise _LocalDenial(
                422,
                "request_model_binding_mismatch",
                "request model disagrees with the frozen attempt model",
            )
        while True:
            if self._phase in (PHASE_CLOSED, PHASE_POISONED):
                reason = (
                    "provider_gate_poisoned"
                    if self._phase == PHASE_POISONED
                    else "provider_gate_closed"
                )
                self._record_denial_locked(
                    method=COUNTED_METHOD,
                    route=COUNTED_ROUTE,
                    reason=reason,
                    request_metadata=metadata,
                )
                raise _LocalDenial(409, reason, "provider admission is closed")
            if self._phase == PHASE_CONCURRENT:
                reservation_after = (
                    self._completed_tokens
                    + (len(self._open) + 1) * self.response_bound
                )
                if reservation_after < self.token_limit:
                    admission_mode = ADMISSION_MODE_CONCURRENT
                    break
                self._transition_locked(
                    PHASE_DRAINING, "concurrent_reservation_would_reach_limit"
                )
                self._persist_locked()
                self._condition.notify_all()
                continue
            if self._phase == PHASE_DRAINING:
                if self._terminal_close_reason is not None:
                    self._record_denial_locked(
                        method=COUNTED_METHOD,
                        route=COUNTED_ROUTE,
                        reason="terminal_close_pending",
                        request_metadata=metadata,
                    )
                    raise _LocalDenial(
                        409, "terminal_close_pending", "provider admission is closing"
                    )
                if self._open:
                    self._condition.wait(timeout=0.25)
                    continue
                self._transition_locked(PHASE_EXCLUSIVE, "concurrent_requests_drained")
                self._persist_locked()
                self._condition.notify_all()
                continue
            if self._phase == PHASE_EXCLUSIVE:
                if self._open:
                    self._condition.wait(timeout=0.25)
                    continue
                admission_mode = ADMISSION_MODE_EXCLUSIVE
                reservation_after = self._completed_tokens + self.response_bound
                break
            raise ProviderGateError(f"unhandled provider-gate phase {self._phase}")

        unix_ns, monotonic_ns = _now()
        sequence = self._next_sequence_locked()
        call_id = f"provider-call-{sequence:08d}"
        open_before = len(self._open)
        reserved_before = self._completed_tokens + open_before * self.response_bound
        credential_headers = sorted(
            name.lower()
            for name in headers
            if name.lower() in _CREDENTIAL_HEADERS
        )
        call: dict[str, Any] = {
            "sequence": sequence,
            "call_id": call_id,
            "method": COUNTED_METHOD,
            "route": COUNTED_ROUTE,
            "request_body_sha256": _sha256_bytes(body),
            "request_bytes": len(body),
            "request_model": request_model,
            "request_stream": request_stream,
            "request_metadata": dict(metadata),
            "credential_headers_present": credential_headers,
            "admission_mode": admission_mode,
            "response_bound": self.response_bound,
            "completed_before": self._completed_tokens,
            "open_before": open_before,
            "reserved_before": reserved_before,
            "reservation_after": reservation_after,
            "admitted_unix_ns": unix_ns,
            "admitted_monotonic_ns": monotonic_ns,
            "upstream_started": False,
            "upstream_start_unix_ns": None,
            "upstream_start_monotonic_ns": None,
            "upstream_status": None,
            "upstream_content_type_occurrences": None,
            "upstream_content_type": None,
            "upstream_content_encoding_occurrences": None,
            "upstream_content_encoding": None,
            "upstream_sse_authentication": None,
            "upstream_body_sha256": None,
            "upstream_body_bytes": None,
            "response_id": None,
            "usage": None,
            "normalized_usage": None,
            "previous_total": None,
            "committed_total": None,
            "commit_unix_ns": None,
            "commit_monotonic_ns": None,
            "crossed_cap": False,
            "release_kind": RELEASE_NONE,
            "released_body_sha256": None,
            "released_body_bytes": 0,
            "released_sanitized_event": None,
            "released_sanitized_events": None,
            "released_sanitized_body_utf8": None,
            "client_release_complete": False,
            "response_output_manifest": None,
            "appserver_crossbind": None,
            "appserver_delivery": None,
            "error": None,
        }
        self._calls.append(call)
        self._calls_by_id[call_id] = call
        self._open[call_id] = call
        self._persist_locked()
        return call

    def _fail_call_locked(
        self,
        call: MutableMapping[str, Any],
        reason: str,
        *,
        status: int | None = None,
        content_type_occurrences: int | None = None,
        content_type: str | None = None,
        content_encoding_occurrences: int | None = None,
        content_encoding: str | None = None,
        body: bytes | None = None,
    ) -> None:
        call["upstream_status"] = status
        call["upstream_content_type_occurrences"] = content_type_occurrences
        call["upstream_content_type"] = content_type
        call["upstream_content_encoding_occurrences"] = (
            content_encoding_occurrences
        )
        call["upstream_content_encoding"] = content_encoding
        call["upstream_sse_authentication"] = None
        if body is not None:
            call["upstream_body_sha256"] = _sha256_bytes(body)
            call["upstream_body_bytes"] = len(body)
        call["error"] = reason
        self._open.pop(str(call["call_id"]), None)
        self._poison_locked(reason)
        self._condition.notify_all()

    def _commit_response_locked(
        self,
        call: MutableMapping[str, Any],
        *,
        status: int,
        content_type_occurrences: int,
        content_type: str | None,
        content_encoding_occurrences: int,
        content_encoding: str | None,
        sse_authentication: Mapping[str, Any],
        upstream_body: bytes,
        response_id: str,
        raw_usage: Mapping[str, Any],
        normalized_usage: Mapping[str, int],
        completed_event: Mapping[str, Any],
        upstream_events: Sequence[Mapping[str, Any]],
        response_output_manifest: Mapping[str, Any],
    ) -> bytes:
        call_id = str(call["call_id"])
        if call_id not in self._open:
            self._poison_locked("completion_for_nonopen_call")
            raise ProviderGateError("provider completion has no open admission")
        if normalized_usage["total_tokens"] > self.response_bound:
            self._fail_call_locked(
                call,
                "response_total_exceeds_bound",
                status=status,
                content_type_occurrences=content_type_occurrences,
                content_type=content_type,
                content_encoding_occurrences=content_encoding_occurrences,
                content_encoding=content_encoding,
                body=upstream_body,
            )
            raise ProviderGateError("provider response total exceeds frozen bound")
        if response_id in self._calls_by_response_id:
            self._fail_call_locked(
                call,
                "duplicate_response_id",
                status=status,
                content_type_occurrences=content_type_occurrences,
                content_type=content_type,
                content_encoding_occurrences=content_encoding_occurrences,
                content_encoding=content_encoding,
                body=upstream_body,
            )
            raise ProviderGateError("provider response ID is duplicated")

        previous_total = self._completed_tokens
        committed_total = previous_total + normalized_usage["total_tokens"]
        commit_unix_ns, commit_monotonic_ns = _now()
        open_at_commit = len(self._open)
        crossed = committed_total >= self.token_limit and self._close_reason is None
        if crossed and (
            self._phase != PHASE_EXCLUSIVE or open_at_commit != 1
        ):
            self._fail_call_locked(
                call,
                "nonexclusive_cap_crossing",
                status=status,
                content_type_occurrences=content_type_occurrences,
                content_type=content_type,
                content_encoding_occurrences=content_encoding_occurrences,
                content_encoding=content_encoding,
                body=upstream_body,
            )
            raise ProviderGateError("cap crossing was not the sole in-flight response")

        released_body = upstream_body
        release_kind = RELEASE_BYTE_IDENTITY
        sanitized_events: list[dict[str, Any]] | None = None
        if crossed:
            if call.get("request_metadata", {}).get("request_kind") == "compaction":
                sanitized_events = sanitized_compaction_completion_events(
                    response_id,
                    raw_usage,
                    upstream_events,
                    completed_event,
                )
                released_body = _canonical_sse_body(sanitized_events)
                release_kind = RELEASE_SANITIZED_COMPACTION_CROSSING
            else:
                sanitized_events = [
                    sanitized_completion_event(
                        response_id, raw_usage, completed_event
                    )
                ]
                released_body = _canonical_sse_body(sanitized_events)
                release_kind = RELEASE_SANITIZED_CROSSING
        elif self._close_reason is not None:
            sanitized_events = [
                sanitized_completion_event(response_id, raw_usage, completed_event)
            ]
            released_body = _canonical_sse_body(sanitized_events)
            release_kind = RELEASE_SANITIZED_TERMINAL

        call.update(
            {
                "upstream_status": status,
                "upstream_content_type_occurrences": content_type_occurrences,
                "upstream_content_type": content_type,
                "upstream_content_encoding_occurrences": (
                    content_encoding_occurrences
                ),
                "upstream_content_encoding": content_encoding,
                "upstream_sse_authentication": copy.deepcopy(
                    dict(sse_authentication)
                ),
                "upstream_body_sha256": _sha256_bytes(upstream_body),
                "upstream_body_bytes": len(upstream_body),
                "response_id": response_id,
                "response_output_manifest": copy.deepcopy(
                    dict(response_output_manifest)
                ),
                "usage": copy.deepcopy(dict(raw_usage)),
                "normalized_usage": copy.deepcopy(dict(normalized_usage)),
                "previous_total": previous_total,
                "committed_total": committed_total,
                "commit_unix_ns": commit_unix_ns,
                "commit_monotonic_ns": commit_monotonic_ns,
                "crossed_cap": crossed,
                "release_kind": release_kind,
                "released_body_sha256": _sha256_bytes(released_body),
                "released_body_bytes": len(released_body),
                "released_sanitized_event": (
                    copy.deepcopy(sanitized_events[-1])
                    if sanitized_events is not None
                    else None
                ),
                "released_sanitized_events": copy.deepcopy(sanitized_events),
                "released_sanitized_body_utf8": (
                    released_body.decode("utf-8")
                    if sanitized_events is not None
                    else None
                ),
            }
        )
        self._completed_tokens = committed_total
        self._calls_by_response_id[response_id] = call  # type: ignore[assignment]
        self._open.pop(call_id, None)

        if crossed:
            crossing_sequence = self._next_sequence_locked()
            self._crossing = {
                "call_id": call_id,
                "response_id": response_id,
                "sequence": crossing_sequence,
                "previous_total": previous_total,
                "response_tokens": normalized_usage["total_tokens"],
                "completed_tokens": committed_total,
                "overshoot_tokens": committed_total - self.token_limit,
                "commit_unix_ns": commit_unix_ns,
                "commit_monotonic_ns": commit_monotonic_ns,
                "sole_inflight": True,
                "release_kind": release_kind,
                "request_kind": call.get("request_metadata", {}).get("request_kind"),
            }
            self._close_reason = CLOSE_REASON_TOKEN_LIMIT
            self._terminal_close_reason = CLOSE_REASON_TOKEN_LIMIT
            self._transition_locked(PHASE_CLOSED, "first_token_limit_crossing", call_id)
            self._crossing_event.set()
        self._persist_locked()
        self._condition.notify_all()
        return released_body

    def _handle_counted(
        self,
        handler: BaseHTTPRequestHandler,
        metadata: Mapping[str, Any],
    ) -> None:
        try:
            body, request_model, request_stream = self._read_request_body(handler)
        except _LocalDenial as denial:
            with self._condition:
                self._record_denial_locked(
                    method=COUNTED_METHOD,
                    route=COUNTED_ROUTE,
                    reason=denial.code,
                    request_metadata=metadata,
                )
            self._send_local_error(handler, denial.status, denial.code, denial.message)
            return

        headers = {name: value for name, value in handler.headers.items()}
        try:
            with self._condition:
                call = self._admit_counted_locked(
                    body=body,
                    request_model=request_model,
                    request_stream=request_stream,
                    headers=headers,
                    metadata=metadata,
                )
        except _LocalDenial as denial:
            self._send_local_error(handler, denial.status, denial.code, denial.message)
            return

        connection: Any = None
        try:
            connection = self._connection_factory()
            outbound = self._outbound_headers(headers, len(body))
            with self._condition:
                if self._phase == PHASE_POISONED or call["call_id"] not in self._open:
                    call["error"] = "admission_closed_before_upstream_send"
                    self._open.pop(str(call["call_id"]), None)
                    self._persist_locked()
                    self._condition.notify_all()
                    raise _LocalDenial(
                        409,
                        "admission_closed_before_upstream_send",
                        "provider admission closed before request send",
                    )
                self._assert_transport_runtime_locked()
                upstream_start_unix_ns, upstream_start_monotonic_ns = _now()
                call["upstream_started"] = True
                call["upstream_start_unix_ns"] = upstream_start_unix_ns
                call["upstream_start_monotonic_ns"] = upstream_start_monotonic_ns
                self._persist_locked()
                # The same lock orders physical provider start against token,
                # proof, natural-end, and poison terminal transitions.
                connection.request(
                    COUNTED_METHOD,
                    DEFAULT_UPSTREAM_BASE_PATH + COUNTED_ROUTE,
                    body=body,
                    headers=outbound,
                )
            response = connection.getresponse()
            response_headers = response.getheaders()
            content_type_values = _header_values(response_headers, "Content-Type")
            content_encoding_values = _header_values(
                response_headers, "Content-Encoding"
            )
            content_type_occurrences = len(content_type_values)
            content_encoding_occurrences = len(content_encoding_values)
            content_type = (
                content_type_values[0] if content_type_occurrences == 1 else None
            )
            content_encoding = (
                content_encoding_values[0]
                if content_encoding_occurrences == 1
                else None
            )
            status = int(response.status)
            upstream_body = self._read_upstream_response(
                response, self.max_response_bytes
            )
            if status != 200:
                raise ProviderGateError(f"upstream_http_status_{status}")
            content_type_basis = _content_type_basis(content_type_values)
            content_encoding_basis = _content_encoding_basis(
                content_encoding_values
            )
            (
                response_id,
                raw_usage,
                normalized_usage,
                completed_event,
                upstream_events,
                sse_state,
                response_output_manifest,
            ) = _parse_sse_completed(upstream_body)
            sse_authentication = {
                "schema_version": 1,
                "protocol": PROVIDER_GATE_UPSTREAM_RESPONSE_PROTOCOL,
                "parser": PROVIDER_GATE_SSE_PARSER,
                "complete": True,
                "content_type_basis": content_type_basis,
                "content_encoding_basis": content_encoding_basis,
                "json_event_count": sse_state["json_event_count"],
                "completed_event_index": sse_state["completed_event_index"],
                "done_count": sse_state["done_count"],
                "body_sha256": _sha256_bytes(upstream_body),
                "body_bytes": len(upstream_body),
                "response_id": response_id,
                "downstream_content_type_synthesized": (
                    content_type_occurrences == 0
                ),
            }
            if set(sse_authentication) != PROVIDER_GATE_SSE_AUTHENTICATION_KEYS:
                raise ProviderGateError("internal SSE authentication schema mismatch")
            with self._condition:
                released_body = self._commit_response_locked(
                    call,
                    status=status,
                    content_type_occurrences=content_type_occurrences,
                    content_type=content_type,
                    content_encoding_occurrences=content_encoding_occurrences,
                    content_encoding=content_encoding,
                    sse_authentication=sse_authentication,
                    upstream_body=upstream_body,
                    response_id=response_id,
                    raw_usage=raw_usage,
                    normalized_usage=normalized_usage,
                    completed_event=completed_event,
                    upstream_events=upstream_events,
                    response_output_manifest=response_output_manifest,
                )
            forwarded_response_headers = [
                (name, value)
                for name, value in response_headers
                if name.lower() not in _HOP_BY_HOP_HEADERS
                and name.lower()
                not in {"content-length", "content-encoding", "content-type"}
            ]
            handler.send_response(status)
            for name, value in forwarded_response_headers:
                handler.send_header(name, value)
            handler.send_header(
                "Content-Type", PROVIDER_GATE_DOWNSTREAM_CONTENT_TYPE
            )
            handler.send_header("Content-Length", str(len(released_body)))
            handler.send_header(
                "Content-Encoding", PROVIDER_GATE_DOWNSTREAM_CONTENT_ENCODING
            )
            handler.end_headers()
            handler.wfile.write(released_body)
            handler.wfile.flush()
            with self._condition:
                call["client_release_complete"] = True
                self._persist_locked()
        except (BrokenPipeError, ConnectionError, OSError) as exc:
            with self._condition:
                if call.get("commit_monotonic_ns") is None:
                    self._fail_call_locked(
                        call,
                        "provider_or_client_disconnect",
                        status=(
                            status if isinstance(locals().get("status"), int) else None
                        ),
                        content_type_occurrences=(
                            content_type_occurrences
                            if isinstance(
                                locals().get("content_type_occurrences"), int
                            )
                            else None
                        ),
                        content_type=(
                            content_type
                            if isinstance(locals().get("content_type"), str)
                            else None
                        ),
                        content_encoding_occurrences=(
                            content_encoding_occurrences
                            if isinstance(
                                locals().get("content_encoding_occurrences"), int
                            )
                            else None
                        ),
                        content_encoding=(
                            content_encoding
                            if isinstance(locals().get("content_encoding"), str)
                            else None
                        ),
                    )
                    send_failure = True
                else:
                    delivery = call.get("appserver_delivery")
                    if (
                        isinstance(delivery, Mapping)
                        and delivery.get("kind") == PROVIDER_GATE_DELIVERY_DIRECT
                        and call.get("appserver_crossbind") is not None
                    ):
                        call["error"] = None
                        call["client_release_complete"] = True
                    else:
                        call["error"] = "client_disconnect_after_commit"
                    # Without direct delivery evidence, keep this completion
                    # pending long enough for the adapter to authenticate an
                    # exact parent/child interrupt race.  Every unresolved or
                    # ineligible disconnect still poisons at the terminal
                    # boundary/finalization.
                    self._persist_locked()
                    self._condition.notify_all()
                    send_failure = False
            if send_failure:
                self._send_local_error(
                    handler,
                    502,
                    "provider_disconnect",
                    "provider response disconnected before completion",
                )
            handler.close_connection = True
        except _LocalDenial as denial:
            self._send_local_error(handler, denial.status, denial.code, denial.message)
        except (ProviderGateError, http.client.HTTPException) as exc:
            with self._condition:
                if call.get("commit_monotonic_ns") is None:
                    status_value = locals().get("status")
                    content_type_occurrences_value = locals().get(
                        "content_type_occurrences"
                    )
                    content_type_value = locals().get("content_type")
                    content_encoding_occurrences_value = locals().get(
                        "content_encoding_occurrences"
                    )
                    content_encoding_value = locals().get("content_encoding")
                    upstream_body_value = locals().get("upstream_body")
                    self._fail_call_locked(
                        call,
                        str(exc),
                        status=status_value if isinstance(status_value, int) else None,
                        content_type_occurrences=(
                            content_type_occurrences_value
                            if isinstance(content_type_occurrences_value, int)
                            else None
                        ),
                        content_type=(
                            content_type_value
                            if isinstance(content_type_value, str)
                            else None
                        ),
                        content_encoding_occurrences=(
                            content_encoding_occurrences_value
                            if isinstance(content_encoding_occurrences_value, int)
                            else None
                        ),
                        content_encoding=(
                            content_encoding_value
                            if isinstance(content_encoding_value, str)
                            else None
                        ),
                        body=(
                            upstream_body_value
                            if isinstance(upstream_body_value, bytes)
                            else None
                        ),
                    )
            self._send_local_error(
                handler, 502, "provider_response_rejected", "provider response rejected"
            )
        finally:
            if connection is not None:
                try:
                    connection.close()
                except Exception:
                    pass

    @staticmethod
    def _normalize_appserver_usage(value: Mapping[str, Any]) -> dict[str, int]:
        if not isinstance(value, Mapping):
            raise ProviderGateError("app-server usage must be a mapping")
        snake_required = {
            "input_tokens",
            "cached_input_tokens",
            "output_tokens",
            "total_tokens",
        }
        if snake_required.issubset(value):
            normalized = {
                "input_tokens": _int_token(value.get("input_tokens"), "input_tokens"),
                "cached_input_tokens": _int_token(
                    value.get("cached_input_tokens"), "cached_input_tokens"
                ),
                "cache_write_input_tokens": _int_token(
                    value.get("cache_write_input_tokens", 0),
                    "cache_write_input_tokens",
                ),
                "output_tokens": _int_token(
                    value.get("output_tokens"), "output_tokens"
                ),
                "reasoning_output_tokens": _int_token(
                    value.get("reasoning_output_tokens", 0),
                    "reasoning_output_tokens",
                ),
                "total_tokens": _int_token(
                    value.get("total_tokens"), "total_tokens"
                ),
            }
        else:
            camel_required = {
                "inputTokens",
                "cachedInputTokens",
                "outputTokens",
                "totalTokens",
            }
            if not camel_required.issubset(value):
                # Provider-shaped raw usage is also accepted for direct tests.
                return normalize_provider_usage(value)
            normalized = {
                "input_tokens": _int_token(value.get("inputTokens"), "inputTokens"),
                "cached_input_tokens": _int_token(
                    value.get("cachedInputTokens"), "cachedInputTokens"
                ),
                "cache_write_input_tokens": _int_token(
                    value.get("cacheWriteInputTokens", 0),
                    "cacheWriteInputTokens",
                ),
                "output_tokens": _int_token(value.get("outputTokens"), "outputTokens"),
                "reasoning_output_tokens": _int_token(
                    value.get("reasoningOutputTokens", 0),
                    "reasoningOutputTokens",
                ),
                "total_tokens": _int_token(value.get("totalTokens"), "totalTokens"),
            }
        if normalized["total_tokens"] != (
            normalized["input_tokens"] + normalized["output_tokens"]
        ):
            raise ProviderGateError("app-server usage total is inconsistent")
        if normalized["cached_input_tokens"] > normalized["input_tokens"]:
            raise ProviderGateError("app-server cached usage exceeds input")
        if normalized["cache_write_input_tokens"] > normalized["input_tokens"]:
            raise ProviderGateError("app-server cache-write usage exceeds input")
        if normalized["reasoning_output_tokens"] > normalized["output_tokens"]:
            raise ProviderGateError("app-server reasoning usage exceeds output")
        return normalized

    def crossbind_appserver_response(
        self,
        response_id: str,
        usage: Mapping[str, Any],
        *,
        thread_id: str | None = None,
        turn_id: str | None = None,
        event_sequence: int | None = None,
    ) -> None:
        response_id = _require_nonempty_string(response_id, "response_id")
        normalized = self._normalize_appserver_usage(usage)
        if thread_id is not None:
            thread_id = _require_nonempty_string(thread_id, "thread_id")
        if turn_id is not None:
            turn_id = _require_nonempty_string(turn_id, "turn_id")
        if event_sequence is not None and (
            isinstance(event_sequence, bool)
            or not isinstance(event_sequence, int)
            or event_sequence < 0
        ):
            raise ProviderGateError("event_sequence must be a nonnegative integer")
        with self._condition:
            call = self._calls_by_response_id.get(response_id)
            if call is None:
                self._poison_locked("unknown_appserver_response_crossbind")
                raise ProviderGateError("app-server response ID is unknown to provider gate")
            if (
                call.get("appserver_crossbind") is not None
                or call.get("appserver_delivery") is not None
            ):
                self._poison_locked("duplicate_appserver_response_crossbind")
                raise ProviderGateError("app-server response delivery was bound twice")
            if call.get("normalized_usage") != normalized:
                self._poison_locked("appserver_provider_usage_mismatch")
                raise ProviderGateError("app-server usage disagrees with provider usage")
            if call.get("error") not in (None, "client_disconnect_after_commit"):
                self._poison_locked("appserver_crossbind_for_failed_provider_call")
                raise ProviderGateError(
                    "app-server response cannot bind a failed provider call"
                )
            request_metadata = call.get("request_metadata")
            if isinstance(request_metadata, Mapping):
                expected_thread = request_metadata.get("thread_id")
                expected_turn = request_metadata.get("turn_id")
                if expected_thread is not None and thread_id != expected_thread:
                    self._poison_locked("appserver_thread_id_mismatch")
                    raise ProviderGateError("app-server thread ID disagrees with request")
                if expected_turn is not None and turn_id != expected_turn:
                    self._poison_locked("appserver_turn_id_mismatch")
                    raise ProviderGateError("app-server turn ID disagrees with request")
            bind_unix_ns, bind_monotonic_ns = _now()
            call["appserver_crossbind"] = {
                "thread_id": thread_id,
                "turn_id": turn_id,
                "event_sequence": event_sequence,
                "normalized_usage": copy.deepcopy(normalized),
                "bind_unix_ns": bind_unix_ns,
                "bind_monotonic_ns": bind_monotonic_ns,
            }
            call["appserver_delivery"] = {
                "kind": PROVIDER_GATE_DELIVERY_DIRECT,
                "successor_call_id": None,
                "successor_response_id": None,
                "bind_unix_ns": bind_unix_ns,
                "bind_monotonic_ns": bind_monotonic_ns,
            }
            # A parsed rawResponse/completed event proves the complete terminal
            # SSE frame reached Codex, even if this handler has not yet reacquired
            # the ledger lock after flushing its socket.
            call["error"] = None
            call["client_release_complete"] = True
            self._persist_locked()
            self._condition.notify_all()

    @staticmethod
    def _same_thread_turn(
        first: Mapping[str, Any], second: Mapping[str, Any]
    ) -> bool:
        first_metadata = first.get("request_metadata")
        second_metadata = second.get("request_metadata")
        return (
            isinstance(first_metadata, Mapping)
            and isinstance(second_metadata, Mapping)
            and first_metadata.get("thread_id") == second_metadata.get("thread_id")
            and first_metadata.get("turn_id") == second_metadata.get("turn_id")
        )

    @staticmethod
    def _same_request_metadata(
        first: Mapping[str, Any], second: Mapping[str, Any]
    ) -> bool:
        """Return whether two calls have the same complete request identity."""

        first_metadata = first.get("request_metadata")
        second_metadata = second.get("request_metadata")
        return (
            isinstance(first_metadata, Mapping)
            and isinstance(second_metadata, Mapping)
            and set(first_metadata) == set(PROVIDER_GATE_REQUEST_METADATA_KEYS)
            and set(second_metadata) == set(PROVIDER_GATE_REQUEST_METADATA_KEYS)
            and _same_json_value(dict(first_metadata), dict(second_metadata))
        )

    @staticmethod
    def _suppressed_wait_base_eligible(call: Mapping[str, Any]) -> bool:
        manifest = call.get("response_output_manifest")
        return (
            call.get("normalized_usage") is not None
            and call.get("error") is None
            and call.get("crossed_cap") is False
            and call.get("release_kind") == RELEASE_BYTE_IDENTITY
            and call.get("released_body_sha256") == call.get("upstream_body_sha256")
            and call.get("released_body_bytes") == call.get("upstream_body_bytes")
            and call.get("client_release_complete") is True
            and call.get("appserver_crossbind") is None
            and isinstance(call.get("request_metadata"), Mapping)
            and call["request_metadata"].get("request_kind") == "turn"
            and isinstance(manifest, Mapping)
            and _manifest_is_exact_collaboration_wait(manifest)
        )

    @staticmethod
    def _superseded_collaboration_message_base_eligible(
        call: Mapping[str, Any],
    ) -> bool:
        """Recognize a complete ordinary response awaiting delivery evidence."""

        authentication = call.get("upstream_sse_authentication")
        manifest = call.get("response_output_manifest")
        return (
            call.get("normalized_usage") is not None
            and call.get("error") is None
            and call.get("crossed_cap") is False
            and call.get("release_kind") == RELEASE_BYTE_IDENTITY
            and call.get("released_body_sha256") == call.get("upstream_body_sha256")
            and call.get("released_body_bytes") == call.get("upstream_body_bytes")
            and call.get("client_release_complete") is True
            and call.get("appserver_crossbind") is None
            and isinstance(call.get("request_metadata"), Mapping)
            and call["request_metadata"].get("request_kind") == "turn"
            and isinstance(manifest, Mapping)
            and isinstance(authentication, Mapping)
            and authentication.get("schema_version")
            == PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_SCHEMA_VERSION
            and authentication.get("protocol")
            == PROVIDER_GATE_UPSTREAM_RESPONSE_PROTOCOL
            and authentication.get("parser") == PROVIDER_GATE_SSE_PARSER
            and authentication.get("complete") is True
            and authentication.get("body_sha256") == call.get("upstream_body_sha256")
            and authentication.get("body_bytes") == call.get("upstream_body_bytes")
            and authentication.get("response_id") == call.get("response_id")
        )

    @staticmethod
    def _authenticated_completed_ordinary_turn(call: Mapping[str, Any]) -> bool:
        """Recognize a complete, below-cap, byte-identical ordinary turn."""

        authentication = call.get("upstream_sse_authentication")
        manifest = call.get("response_output_manifest")
        metadata = call.get("request_metadata")
        return (
            call.get("normalized_usage") is not None
            and call.get("crossed_cap") is False
            and call.get("release_kind") == RELEASE_BYTE_IDENTITY
            and call.get("released_body_sha256") == call.get("upstream_body_sha256")
            and call.get("released_body_bytes") == call.get("upstream_body_bytes")
            and isinstance(metadata, Mapping)
            and metadata.get("request_kind") == "turn"
            and isinstance(manifest, Mapping)
            and isinstance(authentication, Mapping)
            and authentication.get("schema_version")
            == PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_SCHEMA_VERSION
            and authentication.get("protocol")
            == PROVIDER_GATE_UPSTREAM_RESPONSE_PROTOCOL
            and authentication.get("parser") == PROVIDER_GATE_SSE_PARSER
            and authentication.get("complete") is True
            and authentication.get("body_sha256") == call.get("upstream_body_sha256")
            and authentication.get("body_bytes") == call.get("upstream_body_bytes")
            and authentication.get("response_id") == call.get("response_id")
        )

    @classmethod
    def _discarded_after_explicit_child_interrupt_base_eligible(
        cls, call: Mapping[str, Any]
    ) -> bool:
        """Recognize a committed response pending exact interrupt evidence."""

        return (
            cls._authenticated_completed_ordinary_turn(call)
            and call.get("error") == "client_disconnect_after_commit"
            and call.get("client_release_complete") is False
            and call.get("appserver_crossbind") is None
            and call.get("appserver_delivery") is None
        )

    @classmethod
    def _explicit_child_interrupt_pair_eligible(
        cls,
        target: Mapping[str, Any],
        interrupting: Mapping[str, Any],
    ) -> bool:
        """Re-derive the provider-side half of an explicit child interrupt."""

        if not cls._discarded_after_explicit_child_interrupt_base_eligible(target):
            return False
        target_metadata = target.get("request_metadata")
        interrupt_metadata = interrupting.get("request_metadata")
        interrupt_manifest = interrupting.get("response_output_manifest")
        interrupt_delivery = interrupting.get("appserver_delivery")
        interrupt_crossbind = interrupting.get("appserver_crossbind")
        if (
            not cls._authenticated_completed_ordinary_turn(interrupting)
            or interrupting.get("error") is not None
            or interrupting.get("client_release_complete") is not True
            or not isinstance(target_metadata, Mapping)
            or not isinstance(interrupt_metadata, Mapping)
            or target_metadata.get("thread_id") == interrupt_metadata.get("thread_id")
            or not isinstance(interrupt_manifest, Mapping)
            or _exact_interrupt_agent_manifest_item(interrupt_manifest) is None
            or not isinstance(interrupt_delivery, Mapping)
            or interrupt_delivery.get("kind") != PROVIDER_GATE_DELIVERY_DIRECT
            or interrupt_delivery.get("successor_call_id") is not None
            or interrupt_delivery.get("successor_response_id") is not None
            or not isinstance(interrupt_crossbind, Mapping)
            or interrupt_crossbind.get("thread_id")
            != interrupt_metadata.get("thread_id")
            or interrupt_crossbind.get("turn_id") != interrupt_metadata.get("turn_id")
            or interrupt_delivery.get("bind_unix_ns")
            != interrupt_crossbind.get("bind_unix_ns")
            or interrupt_delivery.get("bind_monotonic_ns")
            != interrupt_crossbind.get("bind_monotonic_ns")
        ):
            return False
        for suffix in ("unix_ns", "monotonic_ns"):
            target_admitted = target.get(f"admitted_{suffix}")
            interrupt_admitted = interrupting.get(f"admitted_{suffix}")
            interrupt_commit = interrupting.get(f"commit_{suffix}")
            interrupt_bind = interrupt_delivery.get(f"bind_{suffix}")
            target_commit = target.get(f"commit_{suffix}")
            values = (
                target_admitted,
                interrupt_admitted,
                interrupt_commit,
                interrupt_bind,
                target_commit,
            )
            if not all(type(value) is int for value in values) or not (
                max(target_admitted, interrupt_admitted)
                < interrupt_commit
                < interrupt_bind
                < target_commit
            ):
                return False
        return True

    def _immediate_same_metadata_successor_locked(
        self, call: Mapping[str, Any]
    ) -> MutableMapping[str, Any] | None:
        """Return the immediate later admitted complete call, without skipping gaps."""

        commit = call.get("commit_monotonic_ns")
        if isinstance(commit, bool) or not isinstance(commit, int):
            return None
        later = [
            candidate
            for candidate in self._calls
            if isinstance(candidate.get("admitted_monotonic_ns"), int)
            and not isinstance(candidate.get("admitted_monotonic_ns"), bool)
            and candidate["admitted_monotonic_ns"] > commit
            and self._same_request_metadata(call, candidate)
            and isinstance(candidate.get("request_metadata"), Mapping)
            and candidate["request_metadata"].get("request_kind") == "turn"
        ]
        if not later:
            return None
        successor = min(
            later,
            key=lambda candidate: (
                candidate["admitted_monotonic_ns"],
                candidate["sequence"],
            ),
        )
        delivery = successor.get("appserver_delivery")
        if (
            successor.get("normalized_usage") is None
            or successor.get("error") is not None
            or successor.get("client_release_complete") is not True
            or not isinstance(successor.get("response_id"), str)
            or (
                delivery is not None
                and (
                    not isinstance(delivery, Mapping)
                    or delivery.get("kind")
                    not in (
                        PROVIDER_GATE_DELIVERY_DIRECT,
                        PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE,
                    )
                )
            )
        ):
            return None
        return successor

    def _earliest_direct_successor_locked(
        self, call: Mapping[str, Any]
    ) -> MutableMapping[str, Any] | None:
        commit = call.get("commit_monotonic_ns")
        if isinstance(commit, bool) or not isinstance(commit, int):
            return None
        candidates = [
            candidate
            for candidate in self._calls
            if candidate.get("commit_monotonic_ns") is not None
            and candidate.get("commit_monotonic_ns") > commit
            and candidate.get("admitted_monotonic_ns") > commit
            and candidate.get("error") is None
            and self._same_thread_turn(call, candidate)
            and isinstance(candidate.get("request_metadata"), Mapping)
            and candidate["request_metadata"].get("request_kind") == "turn"
            and isinstance(candidate.get("appserver_delivery"), Mapping)
            and candidate["appserver_delivery"].get("kind")
            == PROVIDER_GATE_DELIVERY_DIRECT
            and candidate.get("appserver_crossbind") is not None
        ]
        if not candidates:
            return None
        return min(
            candidates,
            key=lambda candidate: (
                candidate["commit_monotonic_ns"],
                candidate["sequence"],
            ),
        )

    def suppressed_collaboration_wait_candidates(
        self, thread_id: str, turn_id: str
    ) -> list[dict[str, Any]]:
        """Return private-content-free waits eligible for adapter reconciliation."""

        thread_id = _require_nonempty_string(thread_id, "thread_id")
        turn_id = _require_nonempty_string(turn_id, "turn_id")
        with self._condition:
            result: list[dict[str, Any]] = []
            ordered = sorted(
                self._calls,
                key=lambda call: (
                    call.get("commit_monotonic_ns")
                    if isinstance(call.get("commit_monotonic_ns"), int)
                    else -1,
                    call.get("sequence", -1),
                ),
            )
            for call in ordered:
                metadata = call.get("request_metadata")
                if (
                    not isinstance(metadata, Mapping)
                    or metadata.get("thread_id") != thread_id
                    or metadata.get("turn_id") != turn_id
                    or call.get("appserver_delivery") is not None
                    or not self._suppressed_wait_base_eligible(call)
                ):
                    continue
                successor = self._earliest_direct_successor_locked(call)
                if successor is None:
                    continue
                manifest = call["response_output_manifest"]
                assert isinstance(manifest, Mapping)
                wait_items = [
                    item
                    for item in manifest["items"]
                    if item.get("wait_timeout_ms") is not None
                ]
                wait_item = wait_items[0]
                result.append(
                    {
                        "response_id": call["response_id"],
                        "call_id": call["call_id"],
                        "thread_id": thread_id,
                        "turn_id": turn_id,
                        "normalized_usage": copy.deepcopy(
                            call["normalized_usage"]
                        ),
                        "commit_unix_ns": call["commit_unix_ns"],
                        "commit_monotonic_ns": call["commit_monotonic_ns"],
                        "wait_call_id": wait_item["call_id"],
                        "wait_timeout_ms": wait_item["wait_timeout_ms"],
                        "response_output_manifest_sha256": _sha256_bytes(
                            _canonical_json_bytes(manifest)
                        ),
                        "successor_response_id": successor["response_id"],
                        "successor_call_id": successor["call_id"],
                        "successor_admitted_unix_ns": successor[
                            "admitted_unix_ns"
                        ],
                        "successor_admitted_monotonic_ns": successor[
                            "admitted_monotonic_ns"
                        ],
                    }
                )
                if set(result[-1]) != set(
                    PROVIDER_GATE_SUPPRESSED_WAIT_CANDIDATE_KEYS
                ):
                    raise ProviderGateError(
                        "internal suppressed-wait candidate schema mismatch"
                    )
            return copy.deepcopy(result)

    def superseded_by_collaboration_message_candidates(
        self, thread_id: str, turn_id: str
    ) -> list[dict[str, Any]]:
        """Return responses that a later collaboration message may supersede."""

        thread_id = _require_nonempty_string(thread_id, "thread_id")
        turn_id = _require_nonempty_string(turn_id, "turn_id")
        with self._condition:
            result: list[dict[str, Any]] = []
            ordered = sorted(
                self._calls,
                key=lambda call: (
                    call.get("commit_monotonic_ns")
                    if isinstance(call.get("commit_monotonic_ns"), int)
                    else -1,
                    call.get("sequence", -1),
                ),
            )
            for call in ordered:
                metadata = call.get("request_metadata")
                if (
                    not isinstance(metadata, Mapping)
                    or metadata.get("thread_id") != thread_id
                    or metadata.get("turn_id") != turn_id
                    or call.get("appserver_delivery") is not None
                    or not self._superseded_collaboration_message_base_eligible(call)
                ):
                    continue
                successor = self._immediate_same_metadata_successor_locked(call)
                if successor is None:
                    continue
                manifest = call["response_output_manifest"]
                assert isinstance(manifest, Mapping)
                result.append(
                    {
                        "response_id": call["response_id"],
                        "call_id": call["call_id"],
                        "thread_id": thread_id,
                        "turn_id": turn_id,
                        "normalized_usage": copy.deepcopy(call["normalized_usage"]),
                        "commit_unix_ns": call["commit_unix_ns"],
                        "commit_monotonic_ns": call["commit_monotonic_ns"],
                        "action_capable_item_count": manifest[
                            "action_capable_item_count"
                        ],
                        "response_output_manifest_sha256": _sha256_bytes(
                            _canonical_json_bytes(manifest)
                        ),
                        "successor_response_id": successor["response_id"],
                        "successor_call_id": successor["call_id"],
                        "successor_admitted_unix_ns": successor[
                            "admitted_unix_ns"
                        ],
                        "successor_admitted_monotonic_ns": successor[
                            "admitted_monotonic_ns"
                        ],
                    }
                )
                if set(result[-1]) != set(
                    PROVIDER_GATE_SUPERSEDED_COLLABORATION_MESSAGE_CANDIDATE_KEYS
                ):
                    raise ProviderGateError(
                        "internal superseded-collaboration-message candidate schema mismatch"
                    )
            return copy.deepcopy(result)

    def discarded_after_explicit_child_interrupt_candidates(
        self, thread_id: str, turn_id: str
    ) -> list[dict[str, Any]]:
        """Return exact provider pairs awaiting app-server interrupt evidence."""

        thread_id = _require_nonempty_string(thread_id, "thread_id")
        turn_id = _require_nonempty_string(turn_id, "turn_id")
        with self._condition:
            result: list[dict[str, Any]] = []
            targets = sorted(
                self._calls,
                key=lambda call: (
                    call.get("commit_monotonic_ns")
                    if type(call.get("commit_monotonic_ns")) is int
                    else -1,
                    call.get("sequence", -1),
                ),
            )
            interrupting_calls = sorted(
                self._calls,
                key=lambda call: (
                    call.get("commit_monotonic_ns")
                    if type(call.get("commit_monotonic_ns")) is int
                    else -1,
                    call.get("sequence", -1),
                ),
            )
            for call in targets:
                metadata = call.get("request_metadata")
                if (
                    not isinstance(metadata, Mapping)
                    or metadata.get("thread_id") != thread_id
                    or metadata.get("turn_id") != turn_id
                    or not self._discarded_after_explicit_child_interrupt_base_eligible(
                        call
                    )
                ):
                    continue
                target_manifest = call["response_output_manifest"]
                assert isinstance(target_manifest, Mapping)
                for interrupting in interrupting_calls:
                    if not self._explicit_child_interrupt_pair_eligible(
                        call, interrupting
                    ):
                        continue
                    interrupt_metadata = interrupting["request_metadata"]
                    interrupt_manifest = interrupting["response_output_manifest"]
                    interrupt_delivery = interrupting["appserver_delivery"]
                    assert isinstance(interrupt_metadata, Mapping)
                    assert isinstance(interrupt_manifest, Mapping)
                    assert isinstance(interrupt_delivery, Mapping)
                    interrupt_item = _exact_interrupt_agent_manifest_item(
                        interrupt_manifest
                    )
                    assert interrupt_item is not None
                    result.append(
                        {
                            "response_id": call["response_id"],
                            "call_id": call["call_id"],
                            "thread_id": thread_id,
                            "turn_id": turn_id,
                            "normalized_usage": copy.deepcopy(
                                call["normalized_usage"]
                            ),
                            "admitted_unix_ns": call["admitted_unix_ns"],
                            "admitted_monotonic_ns": call[
                                "admitted_monotonic_ns"
                            ],
                            "commit_unix_ns": call["commit_unix_ns"],
                            "commit_monotonic_ns": call["commit_monotonic_ns"],
                            "action_capable_item_count": target_manifest[
                                "action_capable_item_count"
                            ],
                            "response_output_manifest_sha256": _sha256_bytes(
                                _canonical_json_bytes(target_manifest)
                            ),
                            "interrupting_response_id": interrupting[
                                "response_id"
                            ],
                            "interrupting_call_id": interrupting["call_id"],
                            "interrupt_parent_thread_id": interrupt_metadata[
                                "thread_id"
                            ],
                            "interrupt_parent_turn_id": interrupt_metadata[
                                "turn_id"
                            ],
                            "interrupt_admitted_unix_ns": interrupting[
                                "admitted_unix_ns"
                            ],
                            "interrupt_admitted_monotonic_ns": interrupting[
                                "admitted_monotonic_ns"
                            ],
                            "interrupt_commit_unix_ns": interrupting[
                                "commit_unix_ns"
                            ],
                            "interrupt_commit_monotonic_ns": interrupting[
                                "commit_monotonic_ns"
                            ],
                            "interrupt_bind_unix_ns": interrupt_delivery[
                                "bind_unix_ns"
                            ],
                            "interrupt_bind_monotonic_ns": interrupt_delivery[
                                "bind_monotonic_ns"
                            ],
                            "interrupt_function_item_id": interrupt_item["id"],
                            "interrupt_function_call_id": interrupt_item[
                                "call_id"
                            ],
                            "interrupt_function_arguments_sha256": interrupt_item[
                                "arguments_sha256"
                            ],
                            "interrupt_function_arguments_bytes": interrupt_item[
                                "arguments_bytes"
                            ],
                            "interrupt_response_output_manifest_sha256": _sha256_bytes(
                                _canonical_json_bytes(interrupt_manifest)
                            ),
                        }
                    )
                    if set(result[-1]) != set(
                        PROVIDER_GATE_DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_CANDIDATE_KEYS
                    ):
                        raise ProviderGateError(
                            "internal explicit-child-interrupt candidate schema mismatch"
                        )
            return copy.deepcopy(result)

    def completed_response_usage_snapshot(self) -> list[dict[str, Any]]:
        """Return all committed response usage without response body content."""

        with self._condition:
            result: list[dict[str, Any]] = []
            completed = sorted(
                (
                    call
                    for call in self._calls
                    if call.get("normalized_usage") is not None
                ),
                key=lambda call: (
                    call["commit_monotonic_ns"], call["sequence"]
                ),
            )
            for call in completed:
                metadata = call.get("request_metadata")
                delivery = call.get("appserver_delivery")
                result.append(
                    {
                        "response_id": call["response_id"],
                        "call_id": call["call_id"],
                        "commit_unix_ns": call["commit_unix_ns"],
                        "commit_monotonic_ns": call["commit_monotonic_ns"],
                        "normalized_usage": copy.deepcopy(
                            call["normalized_usage"]
                        ),
                        "thread_id": (
                            metadata.get("thread_id")
                            if isinstance(metadata, Mapping)
                            else None
                        ),
                        "turn_id": (
                            metadata.get("turn_id")
                            if isinstance(metadata, Mapping)
                            else None
                        ),
                        "appserver_delivery_kind": (
                            delivery.get("kind")
                            if isinstance(delivery, Mapping)
                            else None
                        ),
                        "successor_call_id": (
                            delivery.get("successor_call_id")
                            if isinstance(delivery, Mapping)
                            else None
                        ),
                        "successor_response_id": (
                            delivery.get("successor_response_id")
                            if isinstance(delivery, Mapping)
                            else None
                        ),
                    }
                )
                if set(result[-1]) != set(
                    PROVIDER_GATE_COMPLETED_RESPONSE_USAGE_SNAPSHOT_KEYS
                ):
                    raise ProviderGateError(
                        "internal completed-usage snapshot schema mismatch"
                    )
            return copy.deepcopy(result)

    def crossbind_suppressed_collaboration_wait(
        self,
        response_id: str,
        thread_id: str,
        turn_id: str,
        successor_response_id: str,
    ) -> None:
        """Bind one exact wait response suppressed by collaboration delivery."""

        response_id = _require_nonempty_string(response_id, "response_id")
        thread_id = _require_nonempty_string(thread_id, "thread_id")
        turn_id = _require_nonempty_string(turn_id, "turn_id")
        successor_response_id = _require_nonempty_string(
            successor_response_id, "successor_response_id"
        )
        with self._condition:
            call = self._calls_by_response_id.get(response_id)
            if call is None:
                self._poison_locked("unknown_suppressed_collaboration_wait")
                raise ProviderGateError("suppressed response ID is unknown to provider gate")
            if (
                call.get("appserver_crossbind") is not None
                or call.get("appserver_delivery") is not None
            ):
                self._poison_locked("duplicate_suppressed_collaboration_wait_crossbind")
                raise ProviderGateError("suppressed response delivery was bound twice")
            metadata = call.get("request_metadata")
            if (
                not isinstance(metadata, Mapping)
                or metadata.get("thread_id") != thread_id
                or metadata.get("turn_id") != turn_id
            ):
                self._poison_locked("suppressed_collaboration_wait_identity_mismatch")
                raise ProviderGateError(
                    "suppressed response thread or turn ID disagrees with request"
                )
            if not self._suppressed_wait_base_eligible(call):
                self._poison_locked("ineligible_suppressed_collaboration_wait")
                raise ProviderGateError(
                    "response is not an eligible exact collaboration wait"
                )
            successor = self._earliest_direct_successor_locked(call)
            if (
                successor is None
                or successor.get("response_id") != successor_response_id
            ):
                self._poison_locked("suppressed_collaboration_wait_successor_mismatch")
                raise ProviderGateError(
                    "successor is not the earliest later directly bound response"
                )
            bind_unix_ns, bind_monotonic_ns = _now()
            call["appserver_delivery"] = {
                "kind": PROVIDER_GATE_DELIVERY_SUPPRESSED_WAIT,
                "successor_call_id": successor["call_id"],
                "successor_response_id": successor_response_id,
                "bind_unix_ns": bind_unix_ns,
                "bind_monotonic_ns": bind_monotonic_ns,
            }
            self._persist_locked()
            self._condition.notify_all()

    def crossbind_superseded_by_collaboration_message(
        self,
        response_id: str,
        thread_id: str,
        turn_id: str,
        successor_response_id: str,
    ) -> None:
        """Bind one response replaced in Codex by later collaboration messages."""

        response_id = _require_nonempty_string(response_id, "response_id")
        thread_id = _require_nonempty_string(thread_id, "thread_id")
        turn_id = _require_nonempty_string(turn_id, "turn_id")
        successor_response_id = _require_nonempty_string(
            successor_response_id, "successor_response_id"
        )
        with self._condition:
            call = self._calls_by_response_id.get(response_id)
            if call is None:
                self._poison_locked(
                    "unknown_superseded_by_collaboration_message_response"
                )
                raise ProviderGateError("superseded response ID is unknown to provider gate")
            if (
                call.get("appserver_crossbind") is not None
                or call.get("appserver_delivery") is not None
            ):
                self._poison_locked(
                    "duplicate_superseded_by_collaboration_message_crossbind"
                )
                raise ProviderGateError("superseded response delivery was bound twice")
            metadata = call.get("request_metadata")
            if (
                not isinstance(metadata, Mapping)
                or metadata.get("thread_id") != thread_id
                or metadata.get("turn_id") != turn_id
            ):
                self._poison_locked(
                    "superseded_by_collaboration_message_identity_mismatch"
                )
                raise ProviderGateError(
                    "superseded response thread or turn ID disagrees with request"
                )
            if not self._superseded_collaboration_message_base_eligible(call):
                self._poison_locked(
                    "ineligible_superseded_by_collaboration_message_response"
                )
                raise ProviderGateError(
                    "response is not eligible to be superseded by a collaboration message"
                )
            successor = self._immediate_same_metadata_successor_locked(call)
            if (
                successor is None
                or successor.get("response_id") != successor_response_id
            ):
                self._poison_locked(
                    "superseded_by_collaboration_message_successor_mismatch"
                )
                raise ProviderGateError(
                    "successor is not the immediate later same-metadata response"
                )
            bind_unix_ns, bind_monotonic_ns = _now()
            call["appserver_delivery"] = {
                "kind": PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE,
                "successor_call_id": successor["call_id"],
                "successor_response_id": successor_response_id,
                "bind_unix_ns": bind_unix_ns,
                "bind_monotonic_ns": bind_monotonic_ns,
            }
            self._persist_locked()
            self._condition.notify_all()

    def crossbind_discarded_after_explicit_child_interrupt(
        self,
        response_id: str,
        thread_id: str,
        turn_id: str,
        interrupting_response_id: str,
    ) -> None:
        """Bind a child response discarded after its parent's exact interrupt."""

        response_id = _require_nonempty_string(response_id, "response_id")
        thread_id = _require_nonempty_string(thread_id, "thread_id")
        turn_id = _require_nonempty_string(turn_id, "turn_id")
        interrupting_response_id = _require_nonempty_string(
            interrupting_response_id, "interrupting_response_id"
        )
        with self._condition:
            call = self._calls_by_response_id.get(response_id)
            if call is None:
                self._poison_locked(
                    "unknown_discarded_after_explicit_child_interrupt_response"
                )
                raise ProviderGateError(
                    "discarded response ID is unknown to provider gate"
                )
            if (
                call.get("appserver_crossbind") is not None
                or call.get("appserver_delivery") is not None
            ):
                self._poison_locked(
                    "duplicate_discarded_after_explicit_child_interrupt_crossbind"
                )
                raise ProviderGateError("discarded response delivery was bound twice")
            metadata = call.get("request_metadata")
            if (
                not isinstance(metadata, Mapping)
                or metadata.get("thread_id") != thread_id
                or metadata.get("turn_id") != turn_id
            ):
                self._poison_locked(
                    "discarded_after_explicit_child_interrupt_identity_mismatch"
                )
                raise ProviderGateError(
                    "discarded response thread or turn ID disagrees with request"
                )
            interrupting = self._calls_by_response_id.get(interrupting_response_id)
            if interrupting is None:
                self._poison_locked(
                    "unknown_explicit_child_interrupt_response"
                )
                raise ProviderGateError(
                    "interrupting response ID is unknown to provider gate"
                )
            if not self._explicit_child_interrupt_pair_eligible(call, interrupting):
                self._poison_locked(
                    "ineligible_discarded_after_explicit_child_interrupt_pair"
                )
                raise ProviderGateError(
                    "response pair is not an eligible explicit child interrupt"
                )
            bind_unix_ns, bind_monotonic_ns = _now()
            call["error"] = None
            call["appserver_delivery"] = {
                "kind": (
                    PROVIDER_GATE_DELIVERY_DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT
                ),
                "successor_call_id": interrupting["call_id"],
                "successor_response_id": interrupting_response_id,
                "bind_unix_ns": bind_unix_ns,
                "bind_monotonic_ns": bind_monotonic_ns,
            }
            self._persist_locked()
            self._condition.notify_all()

    def stop(self) -> None:
        with self._condition:
            if not self._started:
                raise ProviderGateError("provider gate was never started")
            if self._stopped:
                return
            self._accepting_handlers = False
            if self._phase not in (PHASE_CLOSED, PHASE_POISONED):
                if self._open:
                    for call in list(self._open.values()):
                        if call.get("error") is None:
                            call["error"] = "gate_stopped_with_open_provider_request"
                    self._open.clear()
                    self._poison_locked("gate_stopped_with_open_provider_request")
                else:
                    self._close_reason = CLOSE_REASON_SYSTEM_ERROR
                    self._terminal_close_reason = CLOSE_REASON_SYSTEM_ERROR
                    self._transition_locked(
                        PHASE_CLOSED, "stop_without_terminal_close"
                    )
                    self._persist_locked()
            self._condition.notify_all()
            server = self._server
            thread = self._server_thread
        if server is not None:
            server.shutdown()
            server.server_close()
        if thread is not None:
            thread.join(timeout=10.0)
        with self._condition:
            if thread is not None and thread.is_alive():
                self._poison_locked("provider_gate_server_thread_did_not_stop")
            deadline = time.monotonic() + 30.0
            while self._active_handlers and time.monotonic() < deadline:
                self._condition.wait(timeout=min(0.25, deadline - time.monotonic()))
            if self._active_handlers:
                self._poison_locked("provider_gate_handlers_did_not_quiesce")
            self._stopped = True
            stopped_unix_ns, stopped_monotonic_ns = _now()
            self._lifecycle["stopped_unix_ns"] = stopped_unix_ns
            self._lifecycle["stopped_monotonic_ns"] = stopped_monotonic_ns
            self._persist_locked()

    def finalize(self) -> dict[str, Any]:
        with self._condition:
            if not self._started or not self._stopped:
                raise ProviderGateError("provider gate must be stopped before finalize")
            if self._active_handlers:
                raise ProviderGateError(
                    "provider gate handlers must quiesce before finalization"
                )
            if self._finalized:
                raise ProviderGateError("provider gate was finalized twice")
            if not self._bindings_complete_locked():
                self._poison_locked("finalize_with_incomplete_bindings")
            if self._open:
                self._open.clear()
                self._poison_locked("finalize_with_open_provider_requests")
            missing_release = any(
                call.get("normalized_usage") is not None
                and call.get("client_release_complete") is not True
                and (
                    not isinstance(call.get("appserver_delivery"), Mapping)
                    or call["appserver_delivery"].get("kind")
                    != PROVIDER_GATE_DELIVERY_DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT
                )
                for call in self._calls
            )
            if missing_release:
                self._poison_locked("finalize_before_client_response_release")
            missing_delivery = any(
                call.get("normalized_usage") is not None
                and call.get("appserver_delivery") is None
                for call in self._calls
            )
            if missing_delivery:
                self._poison_locked("finalize_before_appserver_delivery")
            completed_calls = [
                call
                for call in self._calls
                if call.get("normalized_usage") is not None
            ]
            if completed_calls:
                latest = max(
                    completed_calls,
                    key=lambda call: (
                        call["commit_monotonic_ns"], call["sequence"]
                    ),
                )
                latest_delivery = latest.get("appserver_delivery")
                if (
                    isinstance(latest_delivery, Mapping)
                    and latest_delivery.get("kind")
                    != PROVIDER_GATE_DELIVERY_DIRECT
                ):
                    self._poison_locked("finalize_after_suppressed_wait")
            if self._crossing is not None:
                crossing_call = self._calls_by_id[self._crossing["call_id"]]
                crossing_delivery = crossing_call.get("appserver_delivery")
                if (
                    isinstance(crossing_delivery, Mapping)
                    and crossing_delivery.get("kind")
                    != PROVIDER_GATE_DELIVERY_DIRECT
                ):
                    self._poison_locked("finalize_crossing_without_direct_delivery")
            if self._phase not in (PHASE_CLOSED, PHASE_POISONED):
                self._poison_locked("finalize_without_terminal_phase")
            finalized_unix_ns, finalized_monotonic_ns = _now()
            self._lifecycle["finalized_unix_ns"] = finalized_unix_ns
            self._lifecycle["finalized_monotonic_ns"] = finalized_monotonic_ns
            self._persist_locked()
            record = self._record_locked(final=True)
            payload = _canonical_json_bytes(record)
            path = self.final_artifact_path
            descriptor = os.open(
                path,
                os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC,
                0o600,
            )
            try:
                offset = 0
                while offset < len(payload):
                    written = os.write(descriptor, payload[offset:])
                    if written <= 0:
                        raise ProviderGateError("short write of final provider-gate artifact")
                    offset += written
                os.fsync(descriptor)
                os.fchmod(descriptor, 0o444)
                os.fsync(descriptor)
            finally:
                os.close(descriptor)
            directory_fd = os.open(path.parent, os.O_RDONLY | os.O_DIRECTORY)
            try:
                os.fsync(directory_fd)
            finally:
                os.close(directory_fd)
            self._finalized = True
        return validate_artifact(path)


def _exact_keys(value: Any, expected: frozenset[str], label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping) or set(value) != set(expected):
        raise ProviderGateValidationError(f"{label} has unexpected fields")
    return value


def _validation_int(value: Any, label: str, *, positive: bool = False) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise ProviderGateValidationError(f"{label} is not an integer")
    if (positive and value <= 0) or (not positive and value < 0):
        raise ProviderGateValidationError(f"{label} is out of range")
    return value


def _validation_digest(value: Any, label: str) -> str:
    try:
        return _require_sha256(value, label)
    except ProviderGateError as exc:
        raise ProviderGateValidationError(str(exc)) from exc


def _same_json_value(actual: Any, expected: Any) -> bool:
    """Compare JSON values without Python's bool/int/float equality aliases."""

    if isinstance(expected, Mapping):
        return (
            isinstance(actual, Mapping)
            and set(actual) == set(expected)
            and all(_same_json_value(actual[key], value) for key, value in expected.items())
        )
    if isinstance(expected, list):
        return (
            isinstance(actual, list)
            and len(actual) == len(expected)
            and all(_same_json_value(item, value) for item, value in zip(actual, expected))
        )
    if expected is None:
        return actual is None
    return type(actual) is type(expected) and actual == expected


def _validate_transport_dependency(value: Any, label: str) -> Mapping[str, Any]:
    dependency = _exact_keys(value, PROVIDER_TRANSPORT_DEPENDENCY_KEYS, label)
    logical = dependency.get("logical_path")
    resolved = dependency.get("resolved_path")
    if not isinstance(logical, str) or not os.path.isabs(logical):
        raise ProviderGateValidationError(f"{label} logical path is not absolute")
    if (
        not isinstance(resolved, str)
        or not os.path.isabs(resolved)
        or resolved.endswith(" (deleted)")
    ):
        raise ProviderGateValidationError(f"{label} resolved path is not stable")
    symlink_target = dependency.get("symlink_target")
    if symlink_target is not None and not isinstance(symlink_target, str):
        raise ProviderGateValidationError(f"{label} symlink target is malformed")
    _validation_digest(dependency.get("sha256"), f"{label} SHA-256")
    _validation_int(dependency.get("bytes"), f"{label} byte count", positive=True)
    mode = dependency.get("mode")
    if (
        not isinstance(mode, str)
        or len(mode) != 4
        or mode[0] != "0"
        or any(character not in "01234567" for character in mode)
    ):
        raise ProviderGateValidationError(f"{label} mode is not four-digit octal")
    return dependency


def _validate_transport_provenance(value: Any) -> Mapping[str, Any]:
    provenance = _exact_keys(
        value,
        PROVIDER_TRANSPORT_PROVENANCE_KEYS,
        "provider transport provenance",
    )
    if not _same_json_value(
        provenance.get("schema_version"), PROVIDER_TRANSPORT_SCHEMA_VERSION
    ):
        raise ProviderGateValidationError("provider transport schema is unsupported")
    if provenance.get("kind") != PROVIDER_TRANSPORT_KIND:
        raise ProviderGateValidationError("provider transport kind is unsupported")
    if provenance.get("connection_factory_mode") not in PROVIDER_CONNECTION_FACTORY_MODES:
        raise ProviderGateValidationError("provider connection-factory mode is invalid")

    python = _exact_keys(
        provenance.get("python"), PROVIDER_TRANSPORT_PYTHON_KEYS, "transport Python"
    )
    if (
        not isinstance(python.get("executable"), str)
        or not os.path.isabs(python["executable"])
        or not isinstance(python.get("version"), str)
        or not python["version"]
        or not isinstance(python.get("implementation"), str)
        or not python["implementation"]
        or python.get("socket_implementation") != "built-in"
    ):
        raise ProviderGateValidationError("transport Python identity is malformed")
    for key in (
        "binary",
        "ssl_module",
        "http_client_module",
        "socket_module",
        "http_server_module",
        "json_module",
        "json_encoder_module",
        "json_decoder_module",
        "json_extension",
        "hashlib_module",
        "hashlib_extension",
        "ssl_extension",
    ):
        _validate_transport_dependency(python.get(key), f"transport Python {key}")

    openssl = _exact_keys(
        provenance.get("openssl"),
        PROVIDER_TRANSPORT_OPENSSL_KEYS,
        "transport OpenSSL",
    )
    if not isinstance(openssl.get("version"), str) or not openssl["version"]:
        raise ProviderGateValidationError("transport OpenSSL version is malformed")
    _validation_int(
        openssl.get("version_number"), "transport OpenSSL version number", positive=True
    )
    for key in ("libssl", "libcrypto", "config"):
        _validate_transport_dependency(openssl.get(key), f"transport OpenSSL {key}")
    if openssl["config"].get("logical_path") != PROVIDER_OPENSSL_CONFIG_PATH:
        raise ProviderGateValidationError("transport OpenSSL config path is wrong")

    tls = _exact_keys(
        provenance.get("tls"), PROVIDER_TRANSPORT_TLS_KEYS, "transport TLS"
    )
    expected_tls = {
        "protocol": "PROTOCOL_TLS_CLIENT",
        "protocol_value": int(ssl.PROTOCOL_TLS_CLIENT),
        "server_hostname": DEFAULT_UPSTREAM_HOST,
        "server_port": DEFAULT_UPSTREAM_PORT,
        "certificate_source_mode": PROVIDER_CERTIFICATE_SOURCE_MODE,
        "default_capath_used": False,
        "verify_mode": "CERT_REQUIRED",
        "verify_mode_value": int(ssl.CERT_REQUIRED),
        "check_hostname": True,
        "minimum_version": PROVIDER_TLS_MINIMUM_VERSION.name,
        "minimum_version_value": int(PROVIDER_TLS_MINIMUM_VERSION),
        "maximum_version": ssl.TLSVersion.MAXIMUM_SUPPORTED.name,
        "maximum_version_value": int(ssl.TLSVersion.MAXIMUM_SUPPORTED),
        "alpn_protocols": list(PROVIDER_TLS_ALPN_PROTOCOLS),
        "keylog_enabled": False,
    }
    for key, expected in expected_tls.items():
        if not _same_json_value(tls.get(key), expected):
            raise ProviderGateValidationError(f"provider transport TLS {key} is wrong")
    ca = _validate_transport_dependency(
        tls.get("certificate_source"), "transport TLS certificate source"
    )
    if (
        ca.get("logical_path") != PROVIDER_CA_BUNDLE_PATH
        or ca.get("symlink_target") is not None
    ):
        raise ProviderGateValidationError("transport CA source is not the fixed regular file")
    _validation_int(
        tls.get("certificate_authority_count"),
        "transport CA count",
        positive=True,
    )
    for key in ("context_options", "verify_flags", "security_level"):
        _validation_int(tls.get(key), f"transport TLS {key}")
    _validation_digest(tls.get("cipher_names_sha256"), "transport cipher-name hash")

    resolver = _exact_keys(
        provenance.get("resolver"),
        PROVIDER_TRANSPORT_RESOLVER_KEYS,
        "transport resolver",
    )
    expected_resolver = {
        "policy": PROVIDER_RESOLVER_POLICY,
        "hostname": DEFAULT_UPSTREAM_HOST,
        "resolved_addresses_frozen": False,
        "variability_classification": PROVIDER_RESOLVER_VARIABILITY_CLASSIFICATION,
    }
    for key, expected in expected_resolver.items():
        if not _same_json_value(resolver.get(key), expected):
            raise ProviderGateValidationError(f"provider resolver {key} is wrong")
    resolver_paths = {
        "resolv_conf": PROVIDER_RESOLV_CONF_PATH,
        "nsswitch_conf": PROVIDER_NSSWITCH_PATH,
        "hosts_file": PROVIDER_HOSTS_PATH,
        "gai_conf": PROVIDER_GAI_CONF_PATH,
    }
    for key in (
        "resolv_conf",
        "nsswitch_conf",
        "hosts_file",
        "gai_conf",
        "libc",
        "libnss_dns",
        "libnss_files",
    ):
        dependency = _validate_transport_dependency(
            resolver.get(key), f"transport resolver {key}"
        )
        if key in resolver_paths and dependency.get("logical_path") != resolver_paths[key]:
            raise ProviderGateValidationError(f"transport resolver {key} path is wrong")

    environment = _exact_keys(
        provenance.get("environment"),
        PROVIDER_TRANSPORT_ENVIRONMENT_KEYS,
        "transport environment",
    )
    absent = list(PROVIDER_TRANSPORT_ENV_REQUIRED_ABSENT)
    if (
        environment.get("required_absent") != absent
        or environment.get("observed_absent") != absent
        or environment.get("proxy_mode") != PROVIDER_PROXY_MODE
    ):
        raise ProviderGateValidationError("provider transport environment is wrong")
    return provenance


def _assert_expected_subset(actual: Any, expected: Any, label: str) -> None:
    if isinstance(expected, Mapping):
        if not isinstance(actual, Mapping):
            raise ProviderGateValidationError(f"{label} is not a mapping")
        for key, value in expected.items():
            if key not in actual:
                raise ProviderGateValidationError(f"{label} lacks expected {key}")
            _assert_expected_subset(actual[key], value, f"{label}.{key}")
        return
    if not _same_json_value(actual, expected):
        raise ProviderGateValidationError(f"{label} disagrees with expected value")


def _validate_sanitized_call(call: Mapping[str, Any]) -> None:
    text = call.get("released_sanitized_body_utf8")
    event = call.get("released_sanitized_event")
    events = call.get("released_sanitized_events")
    if (
        not isinstance(text, str)
        or not isinstance(event, Mapping)
        or not isinstance(events, list)
        or not events
        or any(not isinstance(item, Mapping) for item in events)
    ):
        raise ProviderGateValidationError("sanitized release evidence is missing")
    release_kind = call.get("release_kind")
    if release_kind == RELEASE_SANITIZED_COMPACTION_CROSSING:
        if (
            call.get("request_metadata", {}).get("request_kind") != "compaction"
            or len(events) != 2
        ):
            raise ProviderGateValidationError(
                "sanitized compaction crossing has the wrong request kind or frame count"
            )
        item_event = events[0]
        if set(item_event) != {"type", "item"} or item_event.get("type") != (
            "response.output_item.done"
        ):
            raise ProviderGateValidationError(
                "sanitized compaction crossing output event is not minimal"
            )
        item = item_event.get("item")
        if (
            not isinstance(item, Mapping)
            or set(item) != {"type", "encrypted_content"}
            or item.get("type") != "compaction"
            or not isinstance(item.get("encrypted_content"), str)
            or not item["encrypted_content"]
        ):
            raise ProviderGateValidationError(
                "sanitized compaction crossing item is not minimal"
            )
    elif release_kind in (RELEASE_SANITIZED_CROSSING, RELEASE_SANITIZED_TERMINAL):
        if (
            call.get("request_metadata", {}).get("request_kind") != "turn"
            or len(events) != 1
        ):
            raise ProviderGateValidationError(
                "sanitized ordinary crossing has the wrong request kind or frame count"
            )
    else:
        raise ProviderGateValidationError("sanitized release kind is invalid")
    if not _same_json_value(events[-1], event):
        raise ProviderGateValidationError(
            "sanitized completion event does not terminate the released event list"
        )
    try:
        expected_body = _canonical_sse_body(events)
    except ProviderGateError as exc:
        raise ProviderGateValidationError(str(exc)) from exc
    if text.encode("utf-8") != expected_body:
        raise ProviderGateValidationError("sanitized release wire is not canonical")
    if call.get("released_body_sha256") != _sha256_bytes(expected_body):
        raise ProviderGateValidationError("sanitized release SHA-256 is stale")
    released_body_bytes = _validation_int(
        call.get("released_body_bytes"), "sanitized release byte count", positive=True
    )
    if released_body_bytes != len(expected_body):
        raise ProviderGateValidationError("sanitized release byte count is stale")
    if set(event) != {"type", "response"} or event.get("type") != "response.completed":
        raise ProviderGateValidationError("sanitized release has extra SSE event fields")
    response = event.get("response")
    if not isinstance(response, Mapping) or set(response) != {
        "id",
        "usage",
        "end_turn",
        "output",
    }:
        raise ProviderGateValidationError("sanitized completion response is not minimal")
    if (
        response.get("id") != call.get("response_id")
        or not _same_json_value(response.get("usage"), call.get("usage"))
        or response.get("end_turn") is not True
        or response.get("output") != []
    ):
        raise ProviderGateValidationError("sanitized completion changed identity or usage")


def _validate_response_output_manifest(
    value: Any, response_id: str
) -> bool:
    manifest = _exact_keys(
        value,
        PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_KEYS,
        "response output manifest",
    )
    if not _same_json_value(
        manifest.get("schema_version"),
        PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_SCHEMA_VERSION,
    ):
        raise ProviderGateValidationError(
            "response output manifest schema version is unsupported"
        )
    if manifest.get("response_id") != response_id:
        raise ProviderGateValidationError(
            "response output manifest identity is inconsistent"
        )
    output_item_count = _validation_int(
        manifest.get("output_item_count"), "response output item count"
    )
    action_capable_item_count = _validation_int(
        manifest.get("action_capable_item_count"),
        "action-capable output item count",
    )
    items = manifest.get("items")
    if not isinstance(items, list) or len(items) != output_item_count:
        raise ProviderGateValidationError(
            "response output manifest item count is inconsistent"
        )
    computed_action_count = 0
    for index, item_value in enumerate(items):
        item = _exact_keys(
            item_value,
            PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_ITEM_KEYS,
            f"response output manifest item {index}",
        )
        if _validation_int(item.get("index"), "response output item index") != index:
            raise ProviderGateValidationError(
                "response output manifest indices are not contiguous"
            )
        item_type = item.get("type")
        if not isinstance(item_type, str) or not item_type.strip():
            raise ProviderGateValidationError(
                "response output manifest item type is malformed"
            )
        if _is_action_capable_output_type(item_type):
            computed_action_count += 1
        for key in ("id", "name", "namespace", "call_id"):
            field = item.get(key)
            if field is not None and (
                not isinstance(field, str) or not field.strip()
            ):
                raise ProviderGateValidationError(
                    f"response output manifest item {key} is malformed"
                )
        _validation_digest(
            item.get("payload_sha256"), "response output payload SHA-256"
        )
        _validation_int(
            item.get("payload_bytes"),
            "response output payload byte count",
            positive=True,
        )
        arguments_sha256 = item.get("arguments_sha256")
        arguments_bytes = item.get("arguments_bytes")
        if arguments_sha256 is None or arguments_bytes is None:
            if arguments_sha256 is not None or arguments_bytes is not None:
                raise ProviderGateValidationError(
                    "response output argument digest evidence is incomplete"
                )
        else:
            _validation_digest(
                arguments_sha256, "response output arguments SHA-256"
            )
            _validation_int(arguments_bytes, "response output argument byte count")
        wait_timeout_ms = item.get("wait_timeout_ms")
        if wait_timeout_ms is not None:
            timeout = _validation_int(
                wait_timeout_ms,
                "collaboration wait timeout",
                positive=True,
            )
            if not (
                PROVIDER_GATE_WAIT_AGENT_MIN_TIMEOUT_MS
                <= timeout
                <= PROVIDER_GATE_WAIT_AGENT_MAX_TIMEOUT_MS
            ):
                raise ProviderGateValidationError(
                    "collaboration wait timeout is outside the supported bound"
                )
            if (
                item_type != "function_call"
                or item.get("name") != "wait_agent"
                or item.get("namespace") != "collaboration"
                or not isinstance(item.get("id"), str)
                or not isinstance(item.get("call_id"), str)
                or arguments_sha256 is None
            ):
                raise ProviderGateValidationError(
                    "collaboration wait manifest identity is inconsistent"
                )
    if computed_action_count != action_capable_item_count:
        raise ProviderGateValidationError(
            "action-capable output item count is inconsistent"
        )
    return _manifest_is_exact_collaboration_wait(manifest)


def _validate_provider_gate_record(record: Mapping[str, Any]) -> None:
    _exact_keys(record, PROVIDER_GATE_TOP_LEVEL_KEYS, "provider-gate artifact")
    if not _same_json_value(record.get("schema_version"), PROVIDER_GATE_SCHEMA_VERSION):
        raise ProviderGateValidationError("provider-gate schema version is unsupported")
    if record.get("protocol") != PROVIDER_GATE_PROTOCOL:
        raise ProviderGateValidationError("provider-gate protocol is unsupported")
    if record.get("canonical_encoding") != PROVIDER_GATE_CANONICAL_ENCODING:
        raise ProviderGateValidationError("provider-gate canonical encoding is wrong")
    if record.get("sealed_mode") != PROVIDER_GATE_SEALED_MODE:
        raise ProviderGateValidationError("provider-gate artifact is not final/sealed")
    digest = _validation_digest(
        record.get(PROVIDER_GATE_RECORD_SHA256_FIELD), "provider-gate self-hash"
    )
    if _document_sha256(record) != digest:
        raise ProviderGateValidationError("provider-gate self-hash is stale")

    implementation = _exact_keys(
        record.get("implementation"),
        PROVIDER_GATE_IMPLEMENTATION_KEYS,
        "provider-gate implementation",
    )
    if (
        implementation.get("name") != PROVIDER_GATE_IMPLEMENTATION_NAME
        or implementation.get("version") != PROVIDER_GATE_IMPLEMENTATION_VERSION
    ):
        raise ProviderGateValidationError("provider-gate implementation identity is wrong")
    _validation_digest(implementation.get("source_sha256"), "gate source SHA-256")

    configuration = _exact_keys(
        record.get("configuration"),
        PROVIDER_GATE_CONFIGURATION_KEYS,
        "provider-gate configuration",
    )
    limit = _validation_int(configuration.get("token_limit"), "token limit", positive=True)
    bound = _validation_int(
        configuration.get("response_bound"), "response bound", positive=True
    )
    expected_configuration_literals = {
        "response_bound_enforcement": (
            "runtime_fail_closed_before_buffered_response_release"
        ),
        "strict_admission_inequality": (
            "completed_tokens + (open_request_count + 1) * response_bound < token_limit"
        ),
        "upstream_origin": DEFAULT_UPSTREAM_ORIGIN,
        "upstream_base_path": DEFAULT_UPSTREAM_BASE_PATH,
        "loopback_only": True,
        "capability_persisted": False,
        "websockets_supported": False,
        "request_retries": 0,
        "stream_retries": 0,
        "request_compression": False,
        "response_compression": "identity",
        "counted_route": f"{COUNTED_METHOD} {COUNTED_ROUTE}",
        "counted_request_kinds": list(PROVIDER_GATE_COUNTED_REQUEST_KINDS),
        "rejected_inference_routes": [
            f"POST {route}" for route in REJECTED_INFERENCE_ROUTES
        ],
        "allowed_setup_route_prefixes": list(ALLOWED_SETUP_ROUTE_PREFIXES),
        "crossing_release_policy": CROSSING_RELEASE_POLICY,
    }
    for key, value in expected_configuration_literals.items():
        if not _same_json_value(configuration.get(key), value):
            raise ProviderGateValidationError(f"provider-gate configuration {key} is wrong")
    _validation_digest(configuration.get("model_catalog_sha256"), "catalog SHA-256")
    _validation_digest(configuration.get("model_entry_sha256"), "model-entry SHA-256")
    upstream_contract = _exact_keys(
        configuration.get("upstream_response_contract"),
        PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_KEYS,
        "upstream response contract",
    )
    expected_upstream_contract = {
        "schema_version": PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_SCHEMA_VERSION,
        "protocol": PROVIDER_GATE_UPSTREAM_RESPONSE_PROTOCOL,
        "success_status": 200,
        "content_type_policy": PROVIDER_GATE_CONTENT_TYPE_POLICY,
        "content_encoding_policy": PROVIDER_GATE_CONTENT_ENCODING_POLICY,
        "outbound_accept": PROVIDER_GATE_OUTBOUND_ACCEPT,
        "parser": PROVIDER_GATE_SSE_PARSER,
        "downstream_content_type": PROVIDER_GATE_DOWNSTREAM_CONTENT_TYPE,
        "downstream_content_encoding": PROVIDER_GATE_DOWNSTREAM_CONTENT_ENCODING,
    }
    if not _same_json_value(dict(upstream_contract), expected_upstream_contract):
        raise ProviderGateValidationError("upstream response contract is stale")
    _validate_transport_provenance(configuration.get("transport_provenance"))

    bindings = _exact_keys(
        record.get("bindings"), PROVIDER_GATE_BINDING_KEYS, "provider-gate bindings"
    )
    for key in ("root_thread_id", "run_id", "model", "reasoning_effort", "prompt_release_protocol"):
        if not isinstance(bindings.get(key), str) or not bindings[key]:
            raise ProviderGateValidationError(f"provider-gate binding {key} is missing")
    _validation_digest(bindings.get("prompt_release_sha256"), "prompt release SHA-256")
    _validation_digest(bindings.get("prompt_sha256"), "prompt SHA-256")

    lifecycle = _exact_keys(
        record.get("lifecycle"), PROVIDER_GATE_LIFECYCLE_KEYS, "gate lifecycle"
    )
    for key in PROVIDER_GATE_LIFECYCLE_KEYS:
        _validation_int(lifecycle.get(key), f"lifecycle {key}", positive=True)
    if not (
        lifecycle["started_monotonic_ns"] <= lifecycle["stopped_monotonic_ns"]
        <= lifecycle["finalized_monotonic_ns"]
    ):
        raise ProviderGateValidationError("provider-gate monotonic lifecycle is unordered")

    state = _exact_keys(record.get("state"), PROVIDER_GATE_STATE_KEYS, "gate state")
    completed_tokens = _validation_int(
        state.get("completed_tokens"), "provider-gate completed tokens"
    )
    state_sequence = _validation_int(
        state.get("sequence"), "provider-gate final sequence"
    )
    active_handler_count = _validation_int(
        state.get("active_handler_count"), "provider-gate active handler count"
    )
    phase = state.get("phase")
    if phase not in PROVIDER_GATE_PHASES or phase not in (PHASE_CLOSED, PHASE_POISONED):
        raise ProviderGateValidationError("final provider-gate phase is not terminal")
    if state.get("close_reason") not in PROVIDER_GATE_CLOSE_REASONS:
        raise ProviderGateValidationError("provider-gate close reason is invalid")
    if state.get("poisoned") is not (phase == PHASE_POISONED):
        raise ProviderGateValidationError("provider-gate poisoned flag is inconsistent")
    poison_reasons = state.get("poison_reasons")
    if not isinstance(poison_reasons, list) or not all(
        isinstance(item, str) and item for item in poison_reasons
    ):
        raise ProviderGateValidationError("provider-gate poison reasons are malformed")
    if (phase == PHASE_POISONED) != bool(poison_reasons):
        raise ProviderGateValidationError("provider-gate poison evidence is inconsistent")
    for key in (
        "crossing_closed",
        "all_complete",
        "no_post_close_upstream",
        "poisoned",
        "handlers_quiescent",
    ):
        if type(state.get(key)) is not bool:
            raise ProviderGateValidationError(
                f"provider-gate state {key} is not a boolean"
            )
    if active_handler_count != 0 or state.get("handlers_quiescent") is not True:
        raise ProviderGateValidationError("provider-gate handlers were not quiescent")
    if state.get("open_request_ids") != []:
        raise ProviderGateValidationError("final provider-gate artifact has open calls")

    calls = record.get("calls")
    transitions = record.get("transitions")
    denials = record.get("denials")
    setup_requests = record.get("setup_requests")
    if not all(isinstance(value, list) for value in (calls, transitions, denials, setup_requests)):
        raise ProviderGateValidationError("provider-gate event ledgers must be arrays")
    assert isinstance(calls, list)
    assert isinstance(transitions, list)
    assert isinstance(denials, list)
    assert isinstance(setup_requests, list)
    if setup_requests:
        raise ProviderGateValidationError("provider-gate setup forwarding must be absent")

    sequences: list[int] = []
    response_ids: set[str] = set()
    completed_calls: list[Mapping[str, Any]] = []
    exact_wait_responses: dict[str, bool] = {}
    for index, call_value in enumerate(calls):
        call = _exact_keys(
            call_value, PROVIDER_GATE_CALL_KEYS, f"provider call {index}"
        )
        sequence = _validation_int(call.get("sequence"), "call sequence", positive=True)
        sequences.append(sequence)
        if call.get("call_id") != f"provider-call-{sequence:08d}":
            raise ProviderGateValidationError("provider call ID is not sequence-bound")
        if call.get("method") != COUNTED_METHOD or call.get("route") != COUNTED_ROUTE:
            raise ProviderGateValidationError("provider call used an uncounted route")
        _validation_digest(call.get("request_body_sha256"), "request body SHA-256")
        _validation_int(call.get("request_bytes"), "request byte count")
        if call.get("request_model") != bindings.get("model"):
            raise ProviderGateValidationError("provider call model is not frozen")
        if call.get("request_stream") is not True:
            raise ProviderGateValidationError("provider call is not streaming")
        metadata = _exact_keys(
            call.get("request_metadata"),
            PROVIDER_GATE_REQUEST_METADATA_KEYS,
            "request metadata",
        )
        if (
            not all(
                isinstance(value, str) and value for value in metadata.values()
            )
            or metadata.get("request_kind")
            not in PROVIDER_GATE_COUNTED_REQUEST_KINDS
        ):
            raise ProviderGateValidationError("request metadata values are malformed")
        credential_names = call.get("credential_headers_present")
        if (
            not isinstance(credential_names, list)
            or credential_names != sorted(set(credential_names))
            or any(name not in _CREDENTIAL_HEADERS for name in credential_names)
        ):
            raise ProviderGateValidationError("credential header evidence is malformed")
        mode = call.get("admission_mode")
        if mode not in PROVIDER_GATE_ADMISSION_MODES:
            raise ProviderGateValidationError("provider admission mode is invalid")
        call_bound = _validation_int(
            call.get("response_bound"), "provider call response bound", positive=True
        )
        if call_bound != bound:
            raise ProviderGateValidationError("provider call response bound is stale")
        completed_before = _validation_int(
            call.get("completed_before"), "completed-before"
        )
        open_before = _validation_int(call.get("open_before"), "open-before")
        reserved_before = _validation_int(
            call.get("reserved_before"), "reserved-before"
        )
        reservation_after = _validation_int(
            call.get("reservation_after"), "reservation-after"
        )
        if reserved_before != completed_before + open_before * bound:
            raise ProviderGateValidationError("provider reservation-before is inconsistent")
        if reservation_after != reserved_before + bound:
            raise ProviderGateValidationError("provider reservation-after is inconsistent")
        if mode == ADMISSION_MODE_CONCURRENT and reservation_after >= limit:
            raise ProviderGateValidationError("unsafe concurrent provider admission")
        if mode == ADMISSION_MODE_EXCLUSIVE and open_before != 0:
            raise ProviderGateValidationError("exclusive provider admission overlapped")
        for key in ("admitted_unix_ns", "admitted_monotonic_ns"):
            _validation_int(call.get(key), f"provider call {key}", positive=True)
        if type(call.get("upstream_started")) is not bool:
            raise ProviderGateValidationError("upstream-start flag is malformed")
        if call.get("upstream_started") is True:
            for key in ("upstream_start_unix_ns", "upstream_start_monotonic_ns"):
                _validation_int(call.get(key), f"provider call {key}", positive=True)
        elif (
            call.get("upstream_start_unix_ns") is not None
            or call.get("upstream_start_monotonic_ns") is not None
        ):
            raise ProviderGateValidationError(
                "provider call has timestamps without an upstream start"
            )
        content_type_occurrences_value = call.get(
            "upstream_content_type_occurrences"
        )
        content_encoding_occurrences_value = call.get(
            "upstream_content_encoding_occurrences"
        )
        for occurrence_value, field in (
            (content_type_occurrences_value, "content type occurrences"),
            (content_encoding_occurrences_value, "content encoding occurrences"),
        ):
            if occurrence_value is not None:
                _validation_int(occurrence_value, field)
        content_type = call.get("upstream_content_type")
        content_encoding = call.get("upstream_content_encoding")
        if (content_type_occurrences_value == 1) is not isinstance(
            content_type, str
        ):
            raise ProviderGateValidationError(
                "provider content-type occurrence evidence is inconsistent"
            )
        if (content_encoding_occurrences_value == 1) is not isinstance(
            content_encoding, str
        ):
            raise ProviderGateValidationError(
                "provider content-encoding occurrence evidence is inconsistent"
            )
        if call.get("normalized_usage") is None:
            if (
                call.get("response_id") is not None
                or call.get("error") is None
                or call.get("upstream_sse_authentication") is not None
                or call.get("response_output_manifest") is not None
                or call.get("appserver_crossbind") is not None
                or call.get("appserver_delivery") is not None
            ):
                raise ProviderGateValidationError("unterminated provider call lacks failure")
            continue
        normalized = _exact_keys(
            call.get("normalized_usage"),
            PROVIDER_GATE_NORMALIZED_USAGE_KEYS,
            "normalized provider usage",
        )
        try:
            normalized_checked = ProviderTokenGate._normalize_appserver_usage(normalized)
        except ProviderGateError as exc:
            raise ProviderGateValidationError(str(exc)) from exc
        if dict(normalized) != normalized_checked:
            raise ProviderGateValidationError("normalized provider usage is not canonical")
        try:
            raw_normalized = normalize_provider_usage(call.get("usage"))
        except ProviderGateError as exc:
            raise ProviderGateValidationError(str(exc)) from exc
        if raw_normalized != normalized_checked:
            raise ProviderGateValidationError("raw and normalized provider usage disagree")
        if normalized_checked["total_tokens"] > bound:
            raise ProviderGateValidationError("provider completion exceeded response bound")
        response_id = call.get("response_id")
        if not isinstance(response_id, str) or not response_id or response_id in response_ids:
            raise ProviderGateValidationError("provider response ID is missing or duplicated")
        response_ids.add(response_id)
        completed_calls.append(call)
        exact_wait_responses[response_id] = _validate_response_output_manifest(
            call.get("response_output_manifest"), response_id
        )
        if call.get("upstream_started") is not True:
            raise ProviderGateValidationError(
                "completed provider call did not start upstream"
            )
        upstream_status = _validation_int(
            call.get("upstream_status"), "upstream HTTP status", positive=True
        )
        if upstream_status != 200:
            raise ProviderGateValidationError("completed provider call has bad HTTP status")
        if content_type_occurrences_value not in (0, 1):
            raise ProviderGateValidationError(
                "completed provider call has ambiguous Content-Type"
            )
        if content_encoding_occurrences_value not in (0, 1):
            raise ProviderGateValidationError(
                "completed provider call has ambiguous Content-Encoding"
            )
        expected_content_type_basis = (
            "authenticated_stream_request_header_absent"
            if content_type_occurrences_value == 0
            else "declared_text_event_stream"
        )
        expected_content_encoding_basis = (
            "implicit_identity_header_absent"
            if content_encoding_occurrences_value == 0
            else "declared_identity"
        )
        if content_type_occurrences_value == 1 and (
            not isinstance(content_type, str)
            or _SSE_CONTENT_TYPE_RE.fullmatch(content_type) is None
        ):
            raise ProviderGateValidationError("completed provider call is not SSE")
        if content_encoding_occurrences_value == 1 and (
            not isinstance(content_encoding, str)
            or re.fullmatch(
                r"[ \t]*identity[ \t]*", content_encoding, re.IGNORECASE
            )
            is None
        ):
            raise ProviderGateValidationError(
                "completed provider call has compressed content"
            )
        for key, positive in (
            ("upstream_body_bytes", True),
            ("released_body_bytes", True),
            ("previous_total", False),
            ("committed_total", True),
            ("commit_unix_ns", True),
            ("commit_monotonic_ns", True),
        ):
            _validation_int(call.get(key), f"provider call {key}", positive=positive)
        if type(call.get("crossed_cap")) is not bool:
            raise ProviderGateValidationError(
                "provider call crossing flag is not a boolean"
            )
        if phase != PHASE_POISONED and call.get("error") is not None:
            raise ProviderGateValidationError(
                "non-poisoned completed provider call has an error"
            )
        _validation_digest(call.get("upstream_body_sha256"), "upstream body SHA-256")
        _validation_digest(call.get("released_body_sha256"), "released body SHA-256")
        authentication = _exact_keys(
            call.get("upstream_sse_authentication"),
            PROVIDER_GATE_SSE_AUTHENTICATION_KEYS,
            "upstream SSE authentication",
        )
        if (
            not _same_json_value(authentication.get("schema_version"), 1)
            or authentication.get("protocol")
            != PROVIDER_GATE_UPSTREAM_RESPONSE_PROTOCOL
            or authentication.get("parser") != PROVIDER_GATE_SSE_PARSER
            or authentication.get("complete") is not True
            or authentication.get("content_type_basis")
            != expected_content_type_basis
            or authentication.get("content_encoding_basis")
            != expected_content_encoding_basis
            or authentication.get("downstream_content_type_synthesized")
            is not (content_type_occurrences_value == 0)
            or authentication.get("body_sha256")
            != call.get("upstream_body_sha256")
            or authentication.get("body_bytes") != call.get("upstream_body_bytes")
            or authentication.get("response_id") != response_id
        ):
            raise ProviderGateValidationError(
                "upstream SSE authentication is inconsistent"
            )
        json_event_count = _validation_int(
            authentication.get("json_event_count"),
            "upstream SSE JSON event count",
            positive=True,
        )
        completed_event_index = _validation_int(
            authentication.get("completed_event_index"),
            "upstream SSE completion event index",
        )
        done_count = _validation_int(
            authentication.get("done_count"), "upstream SSE DONE count"
        )
        if completed_event_index != json_event_count - 1 or done_count not in (0, 1):
            raise ProviderGateValidationError(
                "upstream SSE terminal framing evidence is inconsistent"
            )
        if call.get("release_kind") == RELEASE_BYTE_IDENTITY:
            if (
                call.get("released_body_sha256") != call.get("upstream_body_sha256")
                or call.get("released_body_bytes") != call.get("upstream_body_bytes")
                or call.get("released_sanitized_event") is not None
                or call.get("released_sanitized_events") is not None
                or call.get("released_sanitized_body_utf8") is not None
            ):
                raise ProviderGateValidationError("below-cap body was not byte-identical")
        elif call.get("release_kind") in (
            RELEASE_SANITIZED_CROSSING,
            RELEASE_SANITIZED_COMPACTION_CROSSING,
            RELEASE_SANITIZED_TERMINAL,
        ):
            _validate_sanitized_call(call)
        else:
            raise ProviderGateValidationError("completed call has invalid release kind")
        crossbind_value = call.get("appserver_crossbind")
        crossbind: Mapping[str, Any] | None = None
        if crossbind_value is None:
            pass
        else:
            crossbind = _exact_keys(
                crossbind_value,
                PROVIDER_GATE_CROSSBIND_KEYS,
                "app-server crossbind",
            )
            if crossbind.get("normalized_usage") != normalized:
                raise ProviderGateValidationError("app-server crossbind usage is stale")
            for key in ("thread_id", "turn_id"):
                if crossbind.get(key) is not None and (
                    not isinstance(crossbind.get(key), str) or not crossbind[key]
                ):
                    raise ProviderGateValidationError(
                        f"app-server crossbind {key} is malformed"
                    )
                if crossbind.get(key) != metadata.get(key):
                    raise ProviderGateValidationError(
                        f"app-server crossbind {key} disagrees with request"
                    )
            _validation_int(
                crossbind.get("event_sequence"),
                "app-server crossbind event sequence",
            )
            for key in ("bind_unix_ns", "bind_monotonic_ns"):
                _validation_int(
                    crossbind.get(key), f"app-server crossbind {key}", positive=True
                )
        delivery_value = call.get("appserver_delivery")
        if delivery_value is None:
            if phase != PHASE_POISONED:
                raise ProviderGateValidationError(
                    "completed provider call lacks app-server delivery"
                )
        else:
            delivery = _exact_keys(
                delivery_value,
                PROVIDER_GATE_APPSERVER_DELIVERY_KEYS,
                "app-server delivery",
            )
            kind = delivery.get("kind")
            if kind not in PROVIDER_GATE_DELIVERY_KINDS:
                raise ProviderGateValidationError(
                    "app-server delivery kind is invalid"
                )
            for key in ("bind_unix_ns", "bind_monotonic_ns"):
                _validation_int(
                    delivery.get(key), f"app-server delivery {key}", positive=True
                )
            if kind == PROVIDER_GATE_DELIVERY_DIRECT:
                if (
                    crossbind is None
                    or delivery.get("successor_call_id") is not None
                    or delivery.get("successor_response_id") is not None
                    or delivery.get("bind_unix_ns")
                    != crossbind.get("bind_unix_ns")
                    or delivery.get("bind_monotonic_ns")
                    != crossbind.get("bind_monotonic_ns")
                ):
                    raise ProviderGateValidationError(
                        "direct app-server delivery is inconsistent"
                    )
            elif kind == PROVIDER_GATE_DELIVERY_SUPPRESSED_WAIT:
                if (
                    crossbind is not None
                    or not exact_wait_responses[response_id]
                    or metadata.get("request_kind") != "turn"
                    or call.get("error") is not None
                    or call.get("crossed_cap") is not False
                    or call.get("release_kind") != RELEASE_BYTE_IDENTITY
                    or call.get("released_body_sha256")
                    != call.get("upstream_body_sha256")
                    or call.get("released_body_bytes")
                    != call.get("upstream_body_bytes")
                    or call.get("client_release_complete") is not True
                ):
                    raise ProviderGateValidationError(
                        "suppressed collaboration wait is ineligible"
                    )
                for key in ("successor_call_id", "successor_response_id"):
                    if not isinstance(delivery.get(key), str) or not delivery[key]:
                        raise ProviderGateValidationError(
                            f"suppressed collaboration wait {key} is malformed"
                        )
            elif kind == PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE:
                if (
                    crossbind is not None
                    or metadata.get("request_kind") != "turn"
                    or call.get("error") is not None
                    or call.get("crossed_cap") is not False
                    or call.get("release_kind") != RELEASE_BYTE_IDENTITY
                    or call.get("released_body_sha256")
                    != call.get("upstream_body_sha256")
                    or call.get("released_body_bytes")
                    != call.get("upstream_body_bytes")
                    or call.get("client_release_complete") is not True
                ):
                    raise ProviderGateValidationError(
                        "collaboration-message-superseded response is ineligible"
                    )
                for key in ("successor_call_id", "successor_response_id"):
                    if not isinstance(delivery.get(key), str) or not delivery[key]:
                        raise ProviderGateValidationError(
                            "collaboration-message-superseded response "
                            f"{key} is malformed"
                        )
            else:
                if (
                    kind
                    != PROVIDER_GATE_DELIVERY_DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT
                    or crossbind is not None
                    or metadata.get("request_kind") != "turn"
                    or call.get("error") is not None
                    or call.get("crossed_cap") is not False
                    or call.get("release_kind") != RELEASE_BYTE_IDENTITY
                    or call.get("released_body_sha256")
                    != call.get("upstream_body_sha256")
                    or call.get("released_body_bytes")
                    != call.get("upstream_body_bytes")
                    or call.get("client_release_complete") is not False
                ):
                    raise ProviderGateValidationError(
                        "explicit-child-interrupt discard is ineligible"
                    )
                for key in ("successor_call_id", "successor_response_id"):
                    if not isinstance(delivery.get(key), str) or not delivery[key]:
                        raise ProviderGateValidationError(
                            f"explicit-child-interrupt discard {key} is malformed"
                        )
        release_was_authenticated_discard = (
            isinstance(delivery_value, Mapping)
            and delivery_value.get("kind")
            == PROVIDER_GATE_DELIVERY_DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT
        )
        unresolved_poisoned_disconnect = (
            phase == PHASE_POISONED
            and delivery_value is None
            and call.get("error") == "client_disconnect_after_commit"
        )
        if (
            call.get("client_release_complete") is not True
            and not release_was_authenticated_discard
            and not unresolved_poisoned_disconnect
        ):
            raise ProviderGateValidationError("provider completion was not released")

    commits = sorted(completed_calls, key=lambda call: call["commit_monotonic_ns"])
    running_total = 0
    first_crossing: Mapping[str, Any] | None = None
    for call in commits:
        if call.get("previous_total") != running_total:
            raise ProviderGateValidationError("provider completion order is inconsistent")
        running_total += call["normalized_usage"]["total_tokens"]
        if call.get("committed_total") != running_total:
            raise ProviderGateValidationError("provider committed total is inconsistent")
        expected_crossed = first_crossing is None and running_total >= limit
        if call.get("crossed_cap") is not expected_crossed:
            raise ProviderGateValidationError("first-crossing flag is inconsistent")
        if expected_crossed:
            first_crossing = call
    if completed_tokens != running_total:
        raise ProviderGateValidationError("final completed-token total is inconsistent")

    calls_by_response_id = {
        call["response_id"]: call for call in completed_calls
    }
    for call in completed_calls:
        delivery = call.get("appserver_delivery")
        if (
            not isinstance(delivery, Mapping)
            or delivery.get("kind") != PROVIDER_GATE_DELIVERY_SUPPRESSED_WAIT
        ):
            continue
        successor = calls_by_response_id.get(delivery.get("successor_response_id"))
        if successor is None or successor.get("call_id") != delivery.get(
            "successor_call_id"
        ):
            raise ProviderGateValidationError(
                "suppressed collaboration wait successor is missing"
            )
        successor_delivery = successor.get("appserver_delivery")
        if (
            not isinstance(successor_delivery, Mapping)
            or successor_delivery.get("kind") != PROVIDER_GATE_DELIVERY_DIRECT
            or successor.get("appserver_crossbind") is None
            or successor.get("commit_monotonic_ns")
            <= call.get("commit_monotonic_ns")
            or successor.get("admitted_monotonic_ns")
            <= call.get("commit_monotonic_ns")
            or not ProviderTokenGate._same_thread_turn(call, successor)
            or successor.get("request_metadata", {}).get("request_kind") != "turn"
        ):
            raise ProviderGateValidationError(
                "suppressed collaboration wait successor is not directly bound"
            )
        eligible_direct_successors = [
            candidate
            for candidate in completed_calls
            if candidate.get("commit_monotonic_ns")
            > call.get("commit_monotonic_ns")
            and candidate.get("admitted_monotonic_ns")
            > call.get("commit_monotonic_ns")
            and ProviderTokenGate._same_thread_turn(call, candidate)
            and candidate.get("request_metadata", {}).get("request_kind") == "turn"
            and isinstance(candidate.get("appserver_delivery"), Mapping)
            and candidate["appserver_delivery"].get("kind")
            == PROVIDER_GATE_DELIVERY_DIRECT
            and candidate.get("appserver_crossbind") is not None
        ]
        earliest = min(
            eligible_direct_successors,
            key=lambda candidate: (
                candidate["commit_monotonic_ns"], candidate["sequence"]
            ),
        )
        if earliest.get("response_id") != successor.get("response_id"):
            raise ProviderGateValidationError(
                "suppressed collaboration wait did not bind the earliest direct successor"
            )
        if delivery.get("bind_monotonic_ns") < successor_delivery.get(
            "bind_monotonic_ns"
        ):
            raise ProviderGateValidationError(
                "suppressed collaboration wait was classified before its successor"
            )

    superseded_calls: dict[str, Mapping[str, Any]] = {}
    for call in completed_calls:
        delivery = call.get("appserver_delivery")
        if (
            not isinstance(delivery, Mapping)
            or delivery.get("kind")
            != PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE
        ):
            continue
        response_id = call["response_id"]
        superseded_calls[response_id] = call
        successor = calls_by_response_id.get(delivery.get("successor_response_id"))
        if successor is None or successor.get("call_id") != delivery.get(
            "successor_call_id"
        ):
            raise ProviderGateValidationError(
                "collaboration-message successor is missing"
            )
        successor_delivery = successor.get("appserver_delivery")
        if (
            (
                successor_delivery is not None
                and (
                    not isinstance(successor_delivery, Mapping)
                    or successor_delivery.get("kind")
                    not in (
                        PROVIDER_GATE_DELIVERY_DIRECT,
                        PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE,
                    )
                )
            )
            or (successor_delivery is None and phase != PHASE_POISONED)
            or successor.get("normalized_usage") is None
            or successor.get("error") is not None
            or successor.get("client_release_complete") is not True
            or successor.get("admitted_monotonic_ns")
            <= call.get("commit_monotonic_ns")
            or successor.get("commit_monotonic_ns")
            <= call.get("commit_monotonic_ns")
            or not ProviderTokenGate._same_request_metadata(call, successor)
            or successor.get("request_metadata", {}).get("request_kind") != "turn"
        ):
            raise ProviderGateValidationError(
                "collaboration-message successor is not an eligible later response"
            )
        later_same_metadata = [
            candidate
            for candidate in calls
            if candidate.get("admitted_monotonic_ns")
            > call.get("commit_monotonic_ns")
            and ProviderTokenGate._same_request_metadata(call, candidate)
            and candidate.get("request_metadata", {}).get("request_kind") == "turn"
        ]
        if not later_same_metadata:
            raise ProviderGateValidationError(
                "collaboration-message successor admission is missing"
            )
        immediate = min(
            later_same_metadata,
            key=lambda candidate: (
                candidate["admitted_monotonic_ns"], candidate["sequence"]
            ),
        )
        if immediate.get("response_id") != successor.get("response_id"):
            raise ProviderGateValidationError(
                "collaboration-message response skipped its immediate successor"
            )
        if delivery.get("bind_monotonic_ns") < successor.get(
            "commit_monotonic_ns"
        ):
            raise ProviderGateValidationError(
                "collaboration-message response was classified before its successor"
            )

    for response_id, call in superseded_calls.items():
        visited: set[str] = set()
        cursor = call
        while True:
            cursor_id = cursor.get("response_id")
            if cursor_id in visited:
                raise ProviderGateValidationError(
                    "collaboration-message successor chain contains a cycle"
                )
            assert isinstance(cursor_id, str)
            visited.add(cursor_id)
            cursor_delivery = cursor.get("appserver_delivery")
            if not isinstance(cursor_delivery, Mapping):
                if cursor_delivery is None and phase == PHASE_POISONED:
                    break
                raise ProviderGateValidationError(
                    "collaboration-message successor chain is incomplete"
                )
            if cursor_delivery.get("kind") == PROVIDER_GATE_DELIVERY_DIRECT:
                break
            if (
                cursor_delivery.get("kind")
                != PROVIDER_GATE_DELIVERY_SUPERSEDED_COLLABORATION_MESSAGE
            ):
                raise ProviderGateValidationError(
                    "collaboration-message successor chain did not end directly"
                )
            next_cursor = calls_by_response_id.get(
                cursor_delivery.get("successor_response_id")
            )
            if next_cursor is None:
                raise ProviderGateValidationError(
                    "collaboration-message successor chain is incomplete"
                )
            cursor = next_cursor

    for call in completed_calls:
        delivery = call.get("appserver_delivery")
        if (
            not isinstance(delivery, Mapping)
            or delivery.get("kind")
            != PROVIDER_GATE_DELIVERY_DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT
        ):
            continue
        interrupting = calls_by_response_id.get(
            delivery.get("successor_response_id")
        )
        if interrupting is None or interrupting.get("call_id") != delivery.get(
            "successor_call_id"
        ):
            raise ProviderGateValidationError(
                "explicit child interrupt response is missing"
            )
        interrupt_delivery = interrupting.get("appserver_delivery")
        interrupt_crossbind = interrupting.get("appserver_crossbind")
        target_metadata = call.get("request_metadata")
        interrupt_metadata = interrupting.get("request_metadata")
        interrupt_manifest = interrupting.get("response_output_manifest")
        if (
            not isinstance(interrupt_delivery, Mapping)
            or interrupt_delivery.get("kind") != PROVIDER_GATE_DELIVERY_DIRECT
            or interrupting.get("error") is not None
            or interrupting.get("client_release_complete") is not True
            or not isinstance(interrupt_crossbind, Mapping)
            or not isinstance(target_metadata, Mapping)
            or not isinstance(interrupt_metadata, Mapping)
            or target_metadata.get("thread_id")
            == interrupt_metadata.get("thread_id")
            or interrupting.get("request_metadata", {}).get("request_kind")
            != "turn"
            or not isinstance(interrupt_manifest, Mapping)
            or _exact_interrupt_agent_manifest_item(interrupt_manifest) is None
        ):
            raise ProviderGateValidationError(
                "explicit child interrupt provider evidence is ineligible"
            )
        for suffix in ("unix_ns", "monotonic_ns"):
            target_admitted = call.get(f"admitted_{suffix}")
            interrupt_admitted = interrupting.get(f"admitted_{suffix}")
            interrupt_commit = interrupting.get(f"commit_{suffix}")
            interrupt_bind = interrupt_delivery.get(f"bind_{suffix}")
            target_commit = call.get(f"commit_{suffix}")
            discard_bind = delivery.get(f"bind_{suffix}")
            ordered = (
                target_admitted,
                interrupt_admitted,
                interrupt_commit,
                interrupt_bind,
                target_commit,
                discard_bind,
            )
            if not all(type(value) is int for value in ordered) or not (
                max(target_admitted, interrupt_admitted)
                < interrupt_commit
                < interrupt_bind
                < target_commit
                < discard_bind
            ):
                raise ProviderGateValidationError(
                    "explicit child interrupt timing is inconsistent"
                )

    if completed_calls and phase != PHASE_POISONED:
        latest = commits[-1]
        latest_delivery = latest.get("appserver_delivery")
        if (
            not isinstance(latest_delivery, Mapping)
            or latest_delivery.get("kind") != PROVIDER_GATE_DELIVERY_DIRECT
        ):
            raise ProviderGateValidationError(
                "final provider response was not directly delivered"
            )

    crossing = state.get("crossing")
    if first_crossing is None:
        if crossing is not None or state.get("crossing_closed") is not False:
            raise ProviderGateValidationError("provider-gate crossing was fabricated")
    else:
        crossing = _exact_keys(
            crossing, PROVIDER_GATE_CROSSING_KEYS, "provider-gate crossing"
        )
        crossing_sequence = _validation_int(
            crossing.get("sequence"), "crossing sequence", positive=True
        )
        sequences.append(crossing_sequence)
        for key, positive in (
            ("previous_total", False),
            ("response_tokens", True),
            ("completed_tokens", True),
            ("overshoot_tokens", False),
            ("commit_unix_ns", True),
            ("commit_monotonic_ns", True),
        ):
            _validation_int(
                crossing.get(key), f"provider-gate crossing {key}", positive=positive
            )
        if (
            crossing.get("call_id") != first_crossing.get("call_id")
            or crossing.get("response_id") != first_crossing.get("response_id")
            or crossing.get("previous_total") != first_crossing.get("previous_total")
            or crossing.get("completed_tokens") != first_crossing.get("committed_total")
            or crossing.get("response_tokens")
            != first_crossing["normalized_usage"]["total_tokens"]
            or crossing.get("overshoot_tokens") != running_total - limit
            or crossing.get("sole_inflight") is not True
            or crossing.get("release_kind") != first_crossing.get("release_kind")
            or crossing.get("release_kind")
            not in (
                RELEASE_SANITIZED_CROSSING,
                RELEASE_SANITIZED_COMPACTION_CROSSING,
            )
            or crossing.get("request_kind")
            != first_crossing.get("request_metadata", {}).get("request_kind")
            or (
                crossing.get("release_kind")
                == RELEASE_SANITIZED_COMPACTION_CROSSING
            )
            is not (crossing.get("request_kind") == "compaction")
            or first_crossing.get("admission_mode") != ADMISSION_MODE_EXCLUSIVE
            or first_crossing.get("open_before") != 0
        ):
            raise ProviderGateValidationError("provider-gate crossing evidence is inconsistent")
        if state.get("close_reason") != CLOSE_REASON_TOKEN_LIMIT:
            raise ProviderGateValidationError("token crossing did not close for token limit")
        first_crossing_delivery = first_crossing.get("appserver_delivery")
        if (
            not isinstance(first_crossing_delivery, Mapping)
            or first_crossing_delivery.get("kind")
            != PROVIDER_GATE_DELIVERY_DIRECT
        ):
            raise ProviderGateValidationError(
                "token-crossing provider response was not directly delivered"
            )
        if state.get("crossing_closed") is not (
            phase == PHASE_CLOSED and state.get("no_post_close_upstream") is True
        ):
            raise ProviderGateValidationError("crossing-closed predicate is inconsistent")

    for index, transition_value in enumerate(transitions):
        transition = _exact_keys(
            transition_value,
            PROVIDER_GATE_TRANSITION_KEYS,
            f"provider-gate transition {index}",
        )
        sequences.append(
            _validation_int(transition.get("sequence"), "transition sequence", positive=True)
        )
        if transition.get("from_phase") not in PROVIDER_GATE_PHASES or transition.get(
            "to_phase"
        ) not in PROVIDER_GATE_PHASES:
            raise ProviderGateValidationError("provider-gate transition phase is invalid")
        if not isinstance(transition.get("reason"), str) or not transition["reason"]:
            raise ProviderGateValidationError("provider-gate transition reason is malformed")
        if transition.get("call_id") is not None and (
            not isinstance(transition.get("call_id"), str) or not transition["call_id"]
        ):
            raise ProviderGateValidationError("provider-gate transition call ID is malformed")
        for key in ("unix_ns", "monotonic_ns"):
            _validation_int(
                transition.get(key), f"provider-gate transition {key}", positive=True
            )
    for index, denial_value in enumerate(denials):
        denial = _exact_keys(
            denial_value, PROVIDER_GATE_DENIAL_KEYS, f"provider denial {index}"
        )
        sequences.append(
            _validation_int(denial.get("sequence"), "denial sequence", positive=True)
        )
        if denial.get("upstream_started") is not False:
            raise ProviderGateValidationError("denied request reached upstream")
        if denial.get("denial_id") != f"deny-{denial['sequence']:08d}":
            raise ProviderGateValidationError("provider denial ID is not sequence-bound")
        if denial.get("phase") not in PROVIDER_GATE_PHASES:
            raise ProviderGateValidationError("provider denial phase is invalid")
        for key in ("method", "route", "reason"):
            if not isinstance(denial.get(key), str) or not denial[key]:
                raise ProviderGateValidationError(
                    f"provider denial {key} is malformed"
                )
        denial_metadata = _exact_keys(
            denial.get("request_metadata"),
            PROVIDER_GATE_REQUEST_METADATA_KEYS,
            "provider denial request metadata",
        )
        if not all(
            item is None or isinstance(item, str) for item in denial_metadata.values()
        ):
            raise ProviderGateValidationError(
                "provider denial request metadata is malformed"
            )
        for key in ("unix_ns", "monotonic_ns"):
            _validation_int(denial.get(key), f"provider denial {key}", positive=True)
    if len(sequences) != len(set(sequences)):
        raise ProviderGateValidationError("provider-gate global sequences are duplicated")
    expected_max_sequence = max(sequences, default=0)
    if state_sequence != expected_max_sequence:
        raise ProviderGateValidationError("provider-gate final sequence is inconsistent")
    if sorted(sequences) != list(range(1, state_sequence + 1)):
        raise ProviderGateValidationError("provider-gate global sequence has a gap")
    if state.get("all_complete") is not True or state.get("no_post_close_upstream") is not True:
        raise ProviderGateValidationError("provider-gate did not quiesce exactly")

    terminal_monotonic = [
        transition["monotonic_ns"]
        for transition in transitions
        if transition["to_phase"] in (PHASE_CLOSED, PHASE_POISONED)
    ]
    if terminal_monotonic:
        terminal_cutoff = min(terminal_monotonic)
        upstream_starts = [
            call["upstream_start_monotonic_ns"]
            for call in calls
            if call.get("upstream_started") is True
        ]
        if not all(
            isinstance(start, int) and start <= terminal_cutoff
            for start in upstream_starts
        ):
            raise ProviderGateValidationError("upstream request started after gate close")

    invariants = _exact_keys(
        record.get("invariants"), PROVIDER_GATE_INVARIANT_KEYS, "gate invariants"
    )
    expected_invariants = {
        "bindings_complete": True,
        "completed_sum_matches": True,
        "usage_consistent": True,
        "all_response_totals_within_bound": True,
        "response_ids_unique": True,
        "strict_reservation_safe": True,
        "exclusive_serial": True,
        "crossing_sole_inflight": True,
        "crossing_rewritten": True,
        "no_action_capable_output_frames_on_crossing": True,
        "no_post_close_upstream": True,
        "all_admitted_terminal": True,
        "all_appserver_deliveries_reconciled": all(
            call.get("normalized_usage") is None
            or call.get("appserver_delivery") is not None
            for call in calls
        ),
        "no_open_requests": True,
        "not_poisoned": phase != PHASE_POISONED,
    }
    if not _same_json_value(dict(invariants), expected_invariants):
        raise ProviderGateValidationError("provider-gate invariant summary is stale")


def validate_artifact(
    path: os.PathLike[str] | str,
    expected: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Validate and return one canonical, mode-0444 final gate artifact."""

    artifact_path = Path(path)
    try:
        metadata = artifact_path.lstat()
    except FileNotFoundError as exc:
        raise ProviderGateValidationError("provider-gate artifact is missing") from exc
    if not stat.S_ISREG(metadata.st_mode):
        raise ProviderGateValidationError("provider-gate artifact is not a regular file")
    if stat.S_IMODE(metadata.st_mode) != 0o444:
        raise ProviderGateValidationError("provider-gate artifact mode is not 0444")
    payload = artifact_path.read_bytes()
    try:
        value = json.loads(payload)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise ProviderGateValidationError("provider-gate artifact is not valid JSON") from exc
    if not isinstance(value, Mapping):
        raise ProviderGateValidationError("provider-gate artifact is not a JSON object")
    record = dict(value)
    if payload != _canonical_json_bytes(record):
        raise ProviderGateValidationError("provider-gate artifact is not canonical JSON")
    _validate_provider_gate_record(record)
    if expected is not None:
        _assert_expected_subset(record, expected, "provider-gate expected binding")
    return record


def _main(argv: Sequence[str] | None = None) -> int:
    arguments = list(sys.argv[1:] if argv is None else argv)
    if arguments != ["--print-transport-provenance"]:
        raise SystemExit(
            "usage: provider_token_gate.py --print-transport-provenance"
        )
    _context, provenance = build_transport_provenance()
    sys.stdout.buffer.write(_canonical_json_bytes(provenance))
    sys.stdout.buffer.flush()
    return 0


if __name__ == "__main__":
    raise SystemExit(_main())
