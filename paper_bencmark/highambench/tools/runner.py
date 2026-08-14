#!/usr/bin/env python3
"""Stage and execute one fresh HighamBench N or L run.

The runner is agent-agnostic.  It can pass a seed and token limit to an agent
adapter, but it cannot make an arbitrary Codex CLI honor either value.  Those
controls are therefore explicit protocol claims in every raw record; runs are
marked unscored when required controls or exact provider token usage are absent.

The trusted adapter publishes atomic usage outside the model-writable
workspace. Legacy attempts check cumulative usage before every submission
validation. Ultra attempts use a root-only dynamic submit tool: the adapter
snapshots fixed ``Candidate.lean`` bytes, waits for the matching exact raw
response ledger, and leaves the tool call blocked while this runner validates
those immutable bytes. Acceptance closes app-server without a tool response or
another inference.
"""

from __future__ import annotations

import argparse
import _hashlib
import _json
import _socket
import _ssl
import contextlib
import ctypes
import hashlib
import http.client
import http.server as http_server
import json
import json.decoder as json_decoder
import json.encoder as json_encoder
import os
from pathlib import Path
from pathlib import PurePosixPath
import re
import secrets
import shutil
import socket
import ssl
import stat
import struct
import subprocess
import sys
import sysconfig
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
    from .provider_token_gate import (
        PROVIDER_GATE_BINDING_KEYS as CORE_PROVIDER_GATE_BINDING_KEYS,
        PROVIDER_GATE_APPSERVER_DELIVERY_KEYS as CORE_PROVIDER_GATE_APPSERVER_DELIVERY_KEYS,
        PROVIDER_GATE_CALL_KEYS as CORE_PROVIDER_GATE_CALL_KEYS,
        PROVIDER_GATE_CONFIGURATION_KEYS as CORE_PROVIDER_GATE_CONFIGURATION_KEYS,
        PROVIDER_GATE_CROSSBIND_KEYS as CORE_PROVIDER_GATE_CROSSBIND_KEYS,
        PROVIDER_GATE_CROSSING_KEYS as CORE_PROVIDER_GATE_CROSSING_KEYS,
        PROVIDER_GATE_DENIAL_KEYS as CORE_PROVIDER_GATE_DENIAL_KEYS,
        PROVIDER_GATE_IMPLEMENTATION_KEYS as CORE_PROVIDER_GATE_IMPLEMENTATION_KEYS,
        PROVIDER_GATE_INVARIANT_KEYS as CORE_PROVIDER_GATE_INVARIANT_KEYS,
        PROVIDER_GATE_LIFECYCLE_KEYS as CORE_PROVIDER_GATE_LIFECYCLE_KEYS,
        PROVIDER_GATE_NORMALIZED_USAGE_KEYS as CORE_PROVIDER_GATE_NORMALIZED_USAGE_KEYS,
        PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_ITEM_KEYS as CORE_PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_ITEM_KEYS,
        PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_KEYS as CORE_PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_KEYS,
        PROVIDER_GATE_WAIT_AGENT_MAX_TIMEOUT_MS as CORE_PROVIDER_GATE_WAIT_AGENT_MAX_TIMEOUT_MS,
        PROVIDER_GATE_WAIT_AGENT_MIN_TIMEOUT_MS as CORE_PROVIDER_GATE_WAIT_AGENT_MIN_TIMEOUT_MS,
        PROVIDER_GATE_REQUEST_METADATA_KEYS as CORE_PROVIDER_GATE_REQUEST_METADATA_KEYS,
        PROVIDER_GATE_STATE_KEYS as CORE_PROVIDER_GATE_STATE_KEYS,
        PROVIDER_GATE_SSE_AUTHENTICATION_KEYS as CORE_PROVIDER_GATE_SSE_AUTHENTICATION_KEYS,
        PROVIDER_GATE_SSE_CONTENT_ENCODING_BASES as CORE_PROVIDER_GATE_SSE_CONTENT_ENCODING_BASES,
        PROVIDER_GATE_SSE_CONTENT_TYPE_BASES as CORE_PROVIDER_GATE_SSE_CONTENT_TYPE_BASES,
        PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_KEYS as CORE_PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_KEYS,
        PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_SCHEMA_VERSION as CORE_PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_SCHEMA_VERSION,
        PROVIDER_GATE_UPSTREAM_RESPONSE_PROTOCOL as CORE_PROVIDER_GATE_UPSTREAM_RESPONSE_PROTOCOL,
        PROVIDER_GATE_SSE_PARSER as CORE_PROVIDER_GATE_SSE_PARSER,
        PROVIDER_GATE_CONTENT_TYPE_POLICY as CORE_PROVIDER_GATE_CONTENT_TYPE_POLICY,
        PROVIDER_GATE_CONTENT_ENCODING_POLICY as CORE_PROVIDER_GATE_CONTENT_ENCODING_POLICY,
        PROVIDER_GATE_OUTBOUND_ACCEPT as CORE_PROVIDER_GATE_OUTBOUND_ACCEPT,
        PROVIDER_GATE_DOWNSTREAM_CONTENT_TYPE as CORE_PROVIDER_GATE_DOWNSTREAM_CONTENT_TYPE,
        PROVIDER_GATE_DOWNSTREAM_CONTENT_ENCODING as CORE_PROVIDER_GATE_DOWNSTREAM_CONTENT_ENCODING,
        PROVIDER_GATE_TOP_LEVEL_KEYS as CORE_PROVIDER_GATE_TOP_LEVEL_KEYS,
        PROVIDER_GATE_TRANSITION_KEYS as CORE_PROVIDER_GATE_TRANSITION_KEYS,
        PROVIDER_GATE_SCHEMA_VERSION as CORE_PROVIDER_GATE_SCHEMA_VERSION,
        PROVIDER_GATE_PROTOCOL as CORE_PROVIDER_GATE_PROTOCOL,
        PROVIDER_GATE_IMPLEMENTATION_NAME as CORE_PROVIDER_GATE_IMPLEMENTATION_NAME,
        PROVIDER_GATE_IMPLEMENTATION_VERSION as CORE_PROVIDER_GATE_IMPLEMENTATION_VERSION,
        PROVIDER_TRANSPORT_DEPENDENCY_KEYS as CORE_PROVIDER_TRANSPORT_DEPENDENCY_KEYS,
        PROVIDER_TRANSPORT_ENVIRONMENT_KEYS as CORE_PROVIDER_TRANSPORT_ENVIRONMENT_KEYS,
        PROVIDER_TRANSPORT_OPENSSL_KEYS as CORE_PROVIDER_TRANSPORT_OPENSSL_KEYS,
        PROVIDER_TRANSPORT_PROVENANCE_KEYS as CORE_PROVIDER_TRANSPORT_PROVENANCE_KEYS,
        PROVIDER_TRANSPORT_PYTHON_KEYS as CORE_PROVIDER_TRANSPORT_PYTHON_KEYS,
        PROVIDER_TRANSPORT_RESOLVER_KEYS as CORE_PROVIDER_TRANSPORT_RESOLVER_KEYS,
        PROVIDER_TRANSPORT_TLS_KEYS as CORE_PROVIDER_TRANSPORT_TLS_KEYS,
        provider_gate_artifact_path as core_provider_gate_artifact_path,
        provider_gate_live_path as core_provider_gate_live_path,
    )
    from .codex_isolated import (
        APP_SERVER_CLIENT_NAME,
        APP_SERVER_CLIENT_VERSION,
        MAX_REJECTION_NOTE_BYTES,
        NESTED_SUBMISSION_WIRE_FORMAT,
        NESTED_SUBMISSION_EXEC_SOURCE_BYTES,
        NESTED_SUBMISSION_EXEC_SOURCE_SHA256,
        NESTED_SUBMISSION_EXEC_YIELD_TIME_MS,
        NESTED_SUBMISSION_EXEC_YIELD_ATTEMPT_WALL_SECONDS,
        NESTED_SUBMISSION_EXEC_YIELD_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS,
        PROMPT_GO_KIND,
        PROMPT_RELEASED_KIND,
        PROMPT_RELEASE_ADAPTER_NAME,
        PROMPT_RELEASE_ADAPTER_VERSION,
        PROMPT_RELEASE_PROTOCOL_VERSION,
        PROMPT_RELEASE_SCHEMA_VERSION,
        PROMPT_READY_KIND,
        PROVIDER_USAGE_RECONCILIATION_KEYS,
        PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION,
        COLLABORATION_MESSAGE_EVIDENCE_KEYS,
        DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_EVIDENCE_KEYS,
        EXPLICIT_CHILD_INTERRUPT_RECONCILIATION_GRACE_SECONDS,
        SUPERSEDED_BY_COLLABORATION_MESSAGE_EVIDENCE_KEYS,
        SUPPRESSED_COLLABORATION_WAIT_EVIDENCE_KEYS,
        SUBMISSION_BARRIER_SCHEMA_VERSION,
        SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE,
        SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER,
        TURN_START_REQUEST_ID,
        ULTRA_FORK_POLICY_ALLOWED_RESOLUTION_STATUS,
        ULTRA_FORK_POLICY_ALLOW_DECISION,
        ULTRA_FORK_POLICY_ALLOW_STATUS,
        ULTRA_FORK_POLICY_AWAITING_HOOK_STATUS,
        ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS,
        ULTRA_FORK_POLICY_BLOCK_DECISION,
        ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE,
        ULTRA_FORK_POLICY_BLOCK_STATUS,
        ULTRA_FORK_POLICY_INVALID_RESOLUTION_STATUS,
        authenticated_record,
        canonical_protocol_wire,
        is_canonical_nested_submit_exec_input,
        nested_submission_exec_yield_record,
        prompt_handshake_paths,
        prompt_turn_start_request,
        read_authenticated_record_file,
        submission_barrier_paths,
        ultra_fork_policy_static_record,
        verify_authenticated_record,
        write_authenticated_record_atomic,
    )
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
    from provider_token_gate import (  # type: ignore
        PROVIDER_GATE_BINDING_KEYS as CORE_PROVIDER_GATE_BINDING_KEYS,
        PROVIDER_GATE_APPSERVER_DELIVERY_KEYS as CORE_PROVIDER_GATE_APPSERVER_DELIVERY_KEYS,
        PROVIDER_GATE_CALL_KEYS as CORE_PROVIDER_GATE_CALL_KEYS,
        PROVIDER_GATE_CONFIGURATION_KEYS as CORE_PROVIDER_GATE_CONFIGURATION_KEYS,
        PROVIDER_GATE_CROSSBIND_KEYS as CORE_PROVIDER_GATE_CROSSBIND_KEYS,
        PROVIDER_GATE_CROSSING_KEYS as CORE_PROVIDER_GATE_CROSSING_KEYS,
        PROVIDER_GATE_DENIAL_KEYS as CORE_PROVIDER_GATE_DENIAL_KEYS,
        PROVIDER_GATE_IMPLEMENTATION_KEYS as CORE_PROVIDER_GATE_IMPLEMENTATION_KEYS,
        PROVIDER_GATE_INVARIANT_KEYS as CORE_PROVIDER_GATE_INVARIANT_KEYS,
        PROVIDER_GATE_LIFECYCLE_KEYS as CORE_PROVIDER_GATE_LIFECYCLE_KEYS,
        PROVIDER_GATE_NORMALIZED_USAGE_KEYS as CORE_PROVIDER_GATE_NORMALIZED_USAGE_KEYS,
        PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_ITEM_KEYS as CORE_PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_ITEM_KEYS,
        PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_KEYS as CORE_PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_KEYS,
        PROVIDER_GATE_WAIT_AGENT_MAX_TIMEOUT_MS as CORE_PROVIDER_GATE_WAIT_AGENT_MAX_TIMEOUT_MS,
        PROVIDER_GATE_WAIT_AGENT_MIN_TIMEOUT_MS as CORE_PROVIDER_GATE_WAIT_AGENT_MIN_TIMEOUT_MS,
        PROVIDER_GATE_REQUEST_METADATA_KEYS as CORE_PROVIDER_GATE_REQUEST_METADATA_KEYS,
        PROVIDER_GATE_STATE_KEYS as CORE_PROVIDER_GATE_STATE_KEYS,
        PROVIDER_GATE_SSE_AUTHENTICATION_KEYS as CORE_PROVIDER_GATE_SSE_AUTHENTICATION_KEYS,
        PROVIDER_GATE_SSE_CONTENT_ENCODING_BASES as CORE_PROVIDER_GATE_SSE_CONTENT_ENCODING_BASES,
        PROVIDER_GATE_SSE_CONTENT_TYPE_BASES as CORE_PROVIDER_GATE_SSE_CONTENT_TYPE_BASES,
        PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_KEYS as CORE_PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_KEYS,
        PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_SCHEMA_VERSION as CORE_PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_SCHEMA_VERSION,
        PROVIDER_GATE_UPSTREAM_RESPONSE_PROTOCOL as CORE_PROVIDER_GATE_UPSTREAM_RESPONSE_PROTOCOL,
        PROVIDER_GATE_SSE_PARSER as CORE_PROVIDER_GATE_SSE_PARSER,
        PROVIDER_GATE_CONTENT_TYPE_POLICY as CORE_PROVIDER_GATE_CONTENT_TYPE_POLICY,
        PROVIDER_GATE_CONTENT_ENCODING_POLICY as CORE_PROVIDER_GATE_CONTENT_ENCODING_POLICY,
        PROVIDER_GATE_OUTBOUND_ACCEPT as CORE_PROVIDER_GATE_OUTBOUND_ACCEPT,
        PROVIDER_GATE_DOWNSTREAM_CONTENT_TYPE as CORE_PROVIDER_GATE_DOWNSTREAM_CONTENT_TYPE,
        PROVIDER_GATE_DOWNSTREAM_CONTENT_ENCODING as CORE_PROVIDER_GATE_DOWNSTREAM_CONTENT_ENCODING,
        PROVIDER_GATE_TOP_LEVEL_KEYS as CORE_PROVIDER_GATE_TOP_LEVEL_KEYS,
        PROVIDER_GATE_TRANSITION_KEYS as CORE_PROVIDER_GATE_TRANSITION_KEYS,
        PROVIDER_GATE_SCHEMA_VERSION as CORE_PROVIDER_GATE_SCHEMA_VERSION,
        PROVIDER_GATE_PROTOCOL as CORE_PROVIDER_GATE_PROTOCOL,
        PROVIDER_GATE_IMPLEMENTATION_NAME as CORE_PROVIDER_GATE_IMPLEMENTATION_NAME,
        PROVIDER_GATE_IMPLEMENTATION_VERSION as CORE_PROVIDER_GATE_IMPLEMENTATION_VERSION,
        PROVIDER_TRANSPORT_DEPENDENCY_KEYS as CORE_PROVIDER_TRANSPORT_DEPENDENCY_KEYS,
        PROVIDER_TRANSPORT_ENVIRONMENT_KEYS as CORE_PROVIDER_TRANSPORT_ENVIRONMENT_KEYS,
        PROVIDER_TRANSPORT_OPENSSL_KEYS as CORE_PROVIDER_TRANSPORT_OPENSSL_KEYS,
        PROVIDER_TRANSPORT_PROVENANCE_KEYS as CORE_PROVIDER_TRANSPORT_PROVENANCE_KEYS,
        PROVIDER_TRANSPORT_PYTHON_KEYS as CORE_PROVIDER_TRANSPORT_PYTHON_KEYS,
        PROVIDER_TRANSPORT_RESOLVER_KEYS as CORE_PROVIDER_TRANSPORT_RESOLVER_KEYS,
        PROVIDER_TRANSPORT_TLS_KEYS as CORE_PROVIDER_TRANSPORT_TLS_KEYS,
        provider_gate_artifact_path as core_provider_gate_artifact_path,
        provider_gate_live_path as core_provider_gate_live_path,
    )
    from codex_isolated import (  # type: ignore
        APP_SERVER_CLIENT_NAME,
        APP_SERVER_CLIENT_VERSION,
        MAX_REJECTION_NOTE_BYTES,
        EXPLICIT_CHILD_INTERRUPT_RECONCILIATION_GRACE_SECONDS,
        NESTED_SUBMISSION_WIRE_FORMAT,
        NESTED_SUBMISSION_EXEC_SOURCE_BYTES,
        NESTED_SUBMISSION_EXEC_SOURCE_SHA256,
        NESTED_SUBMISSION_EXEC_YIELD_TIME_MS,
        NESTED_SUBMISSION_EXEC_YIELD_ATTEMPT_WALL_SECONDS,
        NESTED_SUBMISSION_EXEC_YIELD_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS,
        PROMPT_GO_KIND,
        PROMPT_RELEASED_KIND,
        PROMPT_RELEASE_ADAPTER_NAME,
        PROMPT_RELEASE_ADAPTER_VERSION,
        PROMPT_RELEASE_PROTOCOL_VERSION,
        PROMPT_RELEASE_SCHEMA_VERSION,
        PROMPT_READY_KIND,
        PROVIDER_USAGE_RECONCILIATION_KEYS,
        PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION,
        COLLABORATION_MESSAGE_EVIDENCE_KEYS,
        DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_EVIDENCE_KEYS,
        SUPERSEDED_BY_COLLABORATION_MESSAGE_EVIDENCE_KEYS,
        SUPPRESSED_COLLABORATION_WAIT_EVIDENCE_KEYS,
        SUBMISSION_BARRIER_SCHEMA_VERSION,
        SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE,
        SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER,
        TURN_START_REQUEST_ID,
        ULTRA_FORK_POLICY_ALLOWED_RESOLUTION_STATUS,
        ULTRA_FORK_POLICY_ALLOW_DECISION,
        ULTRA_FORK_POLICY_ALLOW_STATUS,
        ULTRA_FORK_POLICY_AWAITING_HOOK_STATUS,
        ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS,
        ULTRA_FORK_POLICY_BLOCK_DECISION,
        ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE,
        ULTRA_FORK_POLICY_BLOCK_STATUS,
        ULTRA_FORK_POLICY_INVALID_RESOLUTION_STATUS,
        authenticated_record,
        canonical_protocol_wire,
        is_canonical_nested_submit_exec_input,
        nested_submission_exec_yield_record,
        prompt_handshake_paths,
        prompt_turn_start_request,
        read_authenticated_record_file,
        submission_barrier_paths,
        ultra_fork_policy_static_record,
        verify_authenticated_record,
        write_authenticated_record_atomic,
    )


MAX_USAGE_GRACE_SECONDS = 5.0
ACCEPTED_SUBMISSION_CLOSE_TIMEOUT_SECONDS = 5.0
PROVIDER_GATE_CLEANUP_GRACE_SECONDS = (
    EXPLICIT_CHILD_INTERRUPT_RECONCILIATION_GRACE_SECONDS
)
FORCED_TERMINATION_GRACE_SECONDS = 2.0
FORCED_TERMINATION_WINDOWS = 2
PROMPT_GO_MINIMUM_RELEASE_WINDOW_SECONDS = 5.0
NETWORK_VIOLATION_MARKER_ENV = "HIGHAMBENCH_NETWORK_VIOLATION_MARKER"
NETWORK_VIOLATION_MARKER_LIMIT = 4096
ULTRA_WALL_TIMEOUT_USAGE_ERROR = (
    "the frozen Codex app-server reports exact usage only for completed upstream "
    "responses; interrupting active Ultra work at the wall-clock boundary can "
    "omit partial in-flight response tokens, so the retained completed-response "
    "aggregate is only a lower bound and cannot be scored"
)
TOKEN_USAGE_MEASUREMENT_SOURCE = "codex_app_server_thread/tokenUsage/updated"
TOKEN_MEASUREMENT_SOURCE = (
    "Codex app-server thread/tokenUsage/updated live cumulative notification"
)
TOKEN_USAGE_NOTIFICATION = "thread/tokenUsage/updated"
TOKEN_LIMIT_ENFORCEMENT_MODE = "first_live_cumulative_update_at_or_above_limit"
ULTRA_USAGE_MEASUREMENT_SOURCE = "codex_app_server_rawResponse/completed"
ULTRA_TOKEN_MEASUREMENT_SOURCE = (
    "Codex app-server rawResponse/completed exact rooted-thread-tree ledger"
)
ULTRA_USAGE_NOTIFICATION = "rawResponse/completed"
ULTRA_USAGE_SCOPE = "rooted_attempt_thread_tree_completed_responses"
ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION = 6
ULTRA_RESPONSE_LEDGER_KEYS = {
    "response_id",
    "thread_id",
    "turn_id",
    "raw_response_notification_sequence",
    "raw_response_observed_at_unix_ns",
    "raw_response_observed_at_monotonic_ns",
    "usage",
    "provider_gate_call",
}
ULTRA_THREAD_LEDGER_KEYS = {
    "thread_id",
    "parent_thread_id",
    "agent_path",
    "provisional",
    "spawn_call_id",
    "spawn_parent_turn_id",
    "spawn_parent_response_id",
    "spawn_fork_turns",
    "spawn_fork_semantics",
    "spawn_binding_status",
    "turn_seen",
    "active_turn_id",
    "turn_status",
    "thread_status",
    "response_count",
    "input_tokens",
    "cached_input_tokens",
    "cache_write_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
    "total_tokens",
    "cumulative_baseline",
    "expected_cumulative_baseline",
    "last_cumulative",
    "cumulative_observation_count",
    "expected_cumulative_projection",
    "full_cumulative_projection",
    "cumulative_projection_exempt_response_id",
    "cumulative_projection_exempt_response_usage",
    "observed_cumulative_baseline",
    "cumulative_baseline_matches_expected",
    "cumulative_projection_match",
    "cumulative_projection_status",
    "accounting_complete",
}
ULTRA_PROVIDER_GATE_SUMMARY_KEYS = {
    "enabled",
    "response_token_bound",
    "artifact_path",
    "record_sha256",
    "final_attached",
    "exact_for_usage",
    "live",
    "terminal",
}
ULTRA_ADAPTER_TEARDOWN_KEYS = {
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
ULTRA_TOKEN_LIMIT_ENFORCEMENT_MODE = (
    "first_authenticated_provider_gate_crossing_commit_at_or_above_limit"
)
PROVIDER_GATE_SCHEMA_VERSION = 6
PROVIDER_GATE_PROTOCOL = "highambench-provider-token-gate-v6"
PROVIDER_GATE_IMPLEMENTATION_NAME = "provider_token_gate.py"
PROVIDER_GATE_IMPLEMENTATION_VERSION = "6"
PROVIDER_GATE_CROSSING_RELEASE_POLICY = (
    "ordinary_empty_output_or_compaction_single_item_before_minimal_completion"
)
PROVIDER_GATE_ORDINARY_CROSSING_RELEASE = "sanitized_crossing_completion"
PROVIDER_GATE_COMPACTION_CROSSING_RELEASE = (
    "sanitized_compaction_crossing_completion"
)
PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT = {
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
}
PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_KEYS = set(
    PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT
)
PROVIDER_GATE_SSE_AUTHENTICATION_KEYS = {
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
PROVIDER_GATE_SSE_CONTENT_TYPE_BASES = {
    "declared_text_event_stream",
    "authenticated_stream_request_header_absent",
}
PROVIDER_GATE_SSE_CONTENT_ENCODING_BASES = {
    "declared_identity",
    "implicit_identity_header_absent",
}
_PROVIDER_GATE_SSE_CONTENT_TYPE_RE = re.compile(
    r'\A[ \t]*text/event-stream(?:[ \t]*;[ \t]*charset[ \t]*=[ \t]*'
    r'(?:utf-8|"utf-8"))?[ \t]*\Z',
    re.IGNORECASE,
)
PROVIDER_RESPONSE_TOKEN_BOUND = 272_000
PROVIDER_TRANSPORT_SCHEMA_VERSION = 1
PROVIDER_TRANSPORT_KIND = "python-stdlib-http-client-explicit-tls-v1"
PROVIDER_CA_BUNDLE_PATH = "/etc/ssl/certs/ca-certificates.crt"
PROVIDER_OPENSSL_CONFIG_PATH = "/usr/lib/ssl/openssl.cnf"
PROVIDER_RESOLV_CONF_PATH = "/etc/resolv.conf"
PROVIDER_NSSWITCH_PATH = "/etc/nsswitch.conf"
PROVIDER_HOSTS_PATH = "/etc/hosts"
PROVIDER_GAI_CONF_PATH = "/etc/gai.conf"
PROVIDER_CERTIFICATE_SOURCE_MODE = "explicit_hashed_pem_cadata_only"
PROVIDER_PROXY_MODE = "direct_http_client_no_environment_proxy"
PROVIDER_CONNECTION_FACTORY_MODE = "explicit_tls"
PROVIDER_RESOLVER_POLICY = (
    "host_getaddrinfo_dynamic_addresses_authenticated_by_tls_hostname"
)
PROVIDER_RESOLVER_VARIABILITY_CLASSIFICATION = (
    "availability_only_under_authenticated_tls_hostname"
)
PROVIDER_TLS_ALPN_PROTOCOLS = ["http/1.1"]
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
PROVIDER_GATE_CANONICAL_ENCODING = "compact_sorted_key_utf8_json_newline"
PROVIDER_GATE_SEALED_MODE = "0444"
FROZEN_CODEX_BINARY_SHA256 = (
    "d13cfcda217421fb20d0aa6aa80819a62483a72e4a7fd52743675ca20d86377c"
)
FROZEN_BUNDLED_MODEL_CATALOG_SHA256 = (
    "0dea49fbbe38900bef0a46c85e79a7ccef9b79d0f4ae5b3c7e898e34ca3dab9b"
)
FROZEN_BUNDLED_MODEL_ENTRY_SHA256 = (
    "1b7c2944189a61833cc1d0122ce1cfcb5b70f6cd78797abe2296fb5791338858"
)
PROVIDER_GATE_ARTIFACT_SUFFIX = ".provider-token-gate.json"
PROVIDER_GATE_LIVE_SUFFIX = ".provider-token-gate.live.json"
PROVIDER_GATE_PHASES = {
    "CONCURRENT",
    "DRAINING",
    "EXCLUSIVE",
    "CLOSED",
    "POISONED",
}
PROVIDER_GATE_ADMISSION_MODES = {"CONCURRENT", "EXCLUSIVE"}
PROVIDER_GATE_CLOSE_REASONS = {
    "token_limit",
    "accepted_submission",
    "natural_end",
    "system_error",
    "poison",
}
PROVIDER_GATE_CALL_KEYS = {
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
    "upstream_content_type",
    "upstream_content_type_occurrences",
    "upstream_content_encoding",
    "upstream_content_encoding_occurrences",
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
PROVIDER_GATE_REQUEST_METADATA_KEYS = {
    "installation_id",
    "session_id",
    "thread_id",
    "turn_id",
    "request_kind",
    "window_id",
}
PROVIDER_GATE_CREDENTIAL_HEADER_NAMES = {
    "authorization",
    "cookie",
    "openai-organization",
    "openai-project",
    "chatgpt-account-id",
    "x-openai-attestation",
    "x-codex-attestation",
}
PROVIDER_GATE_USAGE_KEYS = {
    "input_tokens",
    "cached_input_tokens",
    "cache_write_input_tokens",
    "output_tokens",
    "reasoning_output_tokens",
    "total_tokens",
}
PROVIDER_GATE_CROSSBIND_KEYS = {
    "thread_id",
    "turn_id",
    "event_sequence",
    "normalized_usage",
    "bind_unix_ns",
    "bind_monotonic_ns",
}
PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_KEYS = {
    "schema_version",
    "response_id",
    "output_item_count",
    "action_capable_item_count",
    "items",
}
PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_ITEM_KEYS = {
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
PROVIDER_GATE_APPSERVER_DELIVERY_KEYS = {
    "kind",
    "successor_call_id",
    "successor_response_id",
    "bind_unix_ns",
    "bind_monotonic_ns",
}
PROVIDER_GATE_CROSSING_KEYS = {
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
PROVIDER_GATE_DENIAL_KEYS = {
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
PROVIDER_GATE_TRANSITION_KEYS = {
    "sequence",
    "from_phase",
    "to_phase",
    "reason",
    "call_id",
    "unix_ns",
    "monotonic_ns",
}
PROVIDER_GATE_TOP_LEVEL_KEYS = {
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
    "record_sha256",
}
PROVIDER_GATE_IMPLEMENTATION_KEYS = {"name", "version", "source_sha256"}
PROVIDER_GATE_CONFIGURATION_KEYS = {
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
PROVIDER_GATE_BINDING_KEYS = {
    "root_thread_id",
    "prompt_release_sha256",
    "prompt_release_protocol",
    "prompt_sha256",
    "run_id",
    "model",
    "reasoning_effort",
}
PROVIDER_GATE_LIFECYCLE_KEYS = {
    "started_unix_ns",
    "started_monotonic_ns",
    "stopped_unix_ns",
    "stopped_monotonic_ns",
    "finalized_unix_ns",
    "finalized_monotonic_ns",
}
PROVIDER_GATE_STATE_KEYS = {
    "phase",
    "completed_tokens",
    "close_reason",
    "crossing",
    "crossing_closed",
    "poison_reasons",
    "open_request_ids",
    "all_complete",
    "no_post_close_upstream",
    "poisoned",
    "sequence",
    "active_handler_count",
    "handlers_quiescent",
}
PROVIDER_GATE_INVARIANT_KEYS = {
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
PROVIDER_TRANSPORT_PROVENANCE_KEYS = {
    "schema_version",
    "kind",
    "python",
    "openssl",
    "tls",
    "resolver",
    "environment",
    "connection_factory_mode",
}
PROVIDER_TRANSPORT_DEPENDENCY_KEYS = {
    "logical_path",
    "resolved_path",
    "symlink_target",
    "sha256",
    "bytes",
    "mode",
}
PROVIDER_TRANSPORT_PYTHON_KEYS = {
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
PROVIDER_TRANSPORT_OPENSSL_KEYS = {
    "version",
    "version_number",
    "libssl",
    "libcrypto",
    "config",
}
PROVIDER_TRANSPORT_TLS_KEYS = {
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
PROVIDER_TRANSPORT_RESOLVER_KEYS = {
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
PROVIDER_TRANSPORT_ENVIRONMENT_KEYS = {
    "required_absent",
    "observed_absent",
    "proxy_mode",
}
FAILURE_PRECEDENCE = (
    "TIME_LIMIT",
    "TOKEN_LIMIT",
    "NO_SUBMISSION",
    "RULE_VIOLATION",
    "SYNTAX_OR_ELAB",
    "PROOF_ERROR",
    "SYSTEM_ERROR",
)
SIGNPOSTED_PROMPT_PROTOCOL_VERSION = "signposted-library-v1"
SIGNPOSTED_PROMPT_COMPOSITION_ORDER = [
    "common_prompt",
    "condition_L_supplement_if_condition_L",
    "task_context",
    "fixed_target",
]
EFFECTIVE_PROMPT_COMPOSITION = (
    "utf8_rstrip_each_section_join_two_newlines_final_newline_v1"
)
IN_MODIFY = 0x00000002
IN_CLOSE_WRITE = 0x00000008
IN_MOVED_TO = 0x00000080
IN_CREATE = 0x00000100
IN_DELETE = 0x00000200
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


class SubmissionViolationMonitor:
    """Remember any model-side appearance of the runner-owned submission path."""

    def __init__(self, submission: Path) -> None:
        library = ctypes.CDLL(None, use_errno=True)
        init = library.inotify_init1
        init.argtypes = [ctypes.c_int]
        init.restype = ctypes.c_int
        add_watch = library.inotify_add_watch
        add_watch.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_uint32]
        add_watch.restype = ctypes.c_int
        descriptor = init(os.O_NONBLOCK | os.O_CLOEXEC)
        if descriptor < 0:
            raise BenchmarkToolError("cannot create trusted submission monitor")
        mask = IN_CREATE | IN_MOVED_TO | IN_CLOSE_WRITE | IN_ATTRIB | IN_Q_OVERFLOW
        watch = add_watch(descriptor, os.fsencode(submission.parent), mask)
        if watch < 0:
            os.close(descriptor)
            raise BenchmarkToolError("cannot watch the submission directory")
        self.descriptor = descriptor
        self.watch = watch
        self.basename = os.fsencode(submission.name)
        self.detected = False
        self.integrity_error = False
        self.closed = False

    def poll(self, submission: Path, *, runner_owned: bool = False) -> bool:
        while True:
            try:
                payload = os.read(self.descriptor, 65536)
            except BlockingIOError:
                break
            except InterruptedError:
                continue
            except OSError:
                self.integrity_error = True
                break
            if not payload:
                break
            offset = 0
            while offset + INOTIFY_EVENT.size <= len(payload):
                watch, mask, _cookie, name_length = INOTIFY_EVENT.unpack_from(
                    payload, offset
                )
                name_start = offset + INOTIFY_EVENT.size
                name = payload[name_start : name_start + name_length].rstrip(b"\0")
                offset = name_start + name_length
                if mask & (IN_Q_OVERFLOW | IN_IGNORED):
                    self.integrity_error = True
                if (
                    not runner_owned
                    and watch == self.watch
                    and name == self.basename
                    and mask & (IN_CREATE | IN_MOVED_TO | IN_CLOSE_WRITE | IN_ATTRIB)
                ):
                    self.detected = True
        if not runner_owned:
            try:
                submission.lstat()
            except FileNotFoundError:
                pass
            except OSError:
                self.integrity_error = True
            else:
                self.detected = True
        return self.detected or self.integrity_error

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


def _command_option_value(
    command: Sequence[str], option: str, *, required: bool
) -> str | None:
    positions = [index for index, item in enumerate(command) if item == option]
    if not positions:
        if required:
            raise BenchmarkToolError(f"agent command lacks required {option}")
        return None
    if len(positions) != 1 or positions[0] + 1 >= len(command):
        raise BenchmarkToolError(f"agent command must contain exactly one {option} value")
    return command[positions[0] + 1]


def authenticate_bundled_model_catalog(
    agent_command: Sequence[str],
    *,
    model: str,
    reasoning_effort: str,
    freeze_check: Mapping[str, Any],
) -> dict[str, Any]:
    """Derive the response bound from the authenticated pinned Codex binary."""

    raw_codex = _command_option_value(agent_command, "--codex", required=True)
    assert raw_codex is not None
    codex = Path(raw_codex).resolve()
    try:
        metadata = codex.lstat()
    except OSError as error:
        raise BenchmarkToolError(f"cannot inspect authenticated Codex binary: {error}") from error
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
        raise BenchmarkToolError("Codex --codex path must be a regular non-symlink file")
    binary_sha256 = sha256_file(codex)
    frozen_agent = freeze_check.get("agent")
    if not isinstance(frozen_agent, Mapping):
        raise BenchmarkToolError("frozen-run verification has no agent identity")
    if (
        frozen_agent.get("binary_sha256") != binary_sha256
        or frozen_agent.get("model") != model
        or frozen_agent.get("reasoning_effort") != reasoning_effort
    ):
        raise BenchmarkToolError("Codex binary/model/effort disagrees with the frozen run")
    orchestration = frozen_agent.get("ultra_orchestration")
    if (
        not isinstance(orchestration, Mapping)
        or orchestration.get("enabled") is not True
        or orchestration.get("multi_agent_version") != "v2"
        or orchestration.get("root_model") != model
        or orchestration.get("child_model") != model
        or orchestration.get("root_reasoning_effort") != reasoning_effort
        or orchestration.get("child_reasoning_effort") != reasoning_effort
    ):
        raise BenchmarkToolError("frozen Ultra V2 model/effort locks are incomplete")
    try:
        completed = subprocess.run(
            [str(codex), "debug", "models", "--bundled"],
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30.0,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise BenchmarkToolError(f"cannot read bundled Codex model catalog: {error}") from error
    if completed.returncode != 0:
        raise BenchmarkToolError(
            "authenticated Codex binary rejected `debug models --bundled`"
        )
    try:
        stdout = completed.stdout.decode("utf-8")
        catalog = json.loads(stdout)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise BenchmarkToolError(f"bundled Codex model catalog is not strict JSON: {error}") from error
    if not isinstance(catalog, Mapping) or set(catalog) != {"models"}:
        raise BenchmarkToolError("bundled Codex model catalog has an unknown schema")
    models = catalog.get("models")
    if not isinstance(models, list) or not models:
        raise BenchmarkToolError("bundled Codex model catalog has no models")
    matches = [
        entry
        for entry in models
        if isinstance(entry, Mapping) and entry.get("slug") == model
    ]
    if len(matches) != 1:
        raise BenchmarkToolError("bundled Codex catalog must have exactly one model match")
    entry = dict(matches[0])
    effort_entries = entry.get("supported_reasoning_levels")
    effort_names = (
        [
            item.get("effort")
            for item in effort_entries
            if isinstance(item, Mapping)
        ]
        if isinstance(effort_entries, list)
        else []
    )
    if (
        entry.get("context_window") != PROVIDER_RESPONSE_TOKEN_BOUND
        or isinstance(entry.get("context_window"), bool)
        or entry.get("max_context_window") != PROVIDER_RESPONSE_TOKEN_BOUND
        or isinstance(entry.get("max_context_window"), bool)
        or entry.get("effective_context_window_percent") != 95
        or isinstance(entry.get("effective_context_window_percent"), bool)
        or entry.get("tool_mode") != "code_mode_only"
        or entry.get("multi_agent_version") != "v2"
        or effort_names.count(reasoning_effort) != 1
    ):
        raise BenchmarkToolError("bundled Codex model entry lacks the frozen Ultra contract")

    def canonical_digest(value: Any) -> tuple[str, int]:
        encoded = (
            json.dumps(
                value,
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            )
            + "\n"
        ).encode("utf-8")
        return hashlib.sha256(encoded).hexdigest(), len(encoded)

    catalog_sha256, catalog_bytes = canonical_digest(dict(catalog))
    entry_sha256, entry_bytes = canonical_digest(entry)
    if binary_sha256 == FROZEN_CODEX_BINARY_SHA256 and (
        catalog_sha256 != FROZEN_BUNDLED_MODEL_CATALOG_SHA256
        or entry_sha256 != FROZEN_BUNDLED_MODEL_ENTRY_SHA256
    ):
        raise BenchmarkToolError("pinned Codex bundled model catalog digest changed")
    return {
        "source": "authenticated_codex_debug_models_bundled",
        "codex_path": str(codex),
        "codex_binary_sha256": binary_sha256,
        "catalog_sha256": catalog_sha256,
        "catalog_canonical_bytes": catalog_bytes,
        "model_count": len(models),
        "matching_model_count": 1,
        "entry_sha256": entry_sha256,
        "entry_canonical_bytes": entry_bytes,
        "slug": model,
        "context_window": entry["context_window"],
        "max_context_window": entry["max_context_window"],
        "effective_context_window_percent": entry[
            "effective_context_window_percent"
        ],
        "tool_mode": entry["tool_mode"],
        "multi_agent_version": entry["multi_agent_version"],
        "reasoning_effort": reasoning_effort,
        "reasoning_effort_supported": True,
        "response_bound": entry["context_window"],
    }


def _sanitized_provider_transport_environment() -> dict[str, str]:
    """Return the exact adapter environment with transport overrides removed."""

    environment = os.environ.copy()
    for name in PROVIDER_TRANSPORT_ENV_REQUIRED_ABSENT:
        environment.pop(name, None)
    if any(name in environment for name in PROVIDER_TRANSPORT_ENV_REQUIRED_ABSENT):
        raise BenchmarkToolError(
            "provider transport override survived environment sanitization"
        )
    return environment


def _provider_transport_read_all(descriptor: int) -> bytes:
    chunks: list[bytes] = []
    while True:
        chunk = os.read(descriptor, 1024 * 1024)
        if not chunk:
            return b"".join(chunks)
        chunks.append(chunk)


def _provider_transport_dependency(
    logical_path: os.PathLike[str] | str,
    *,
    nofollow: bool = False,
) -> tuple[dict[str, Any], bytes]:
    """Hash one dependency through the same regular-file fd being described."""

    logical = os.fspath(logical_path)
    if not os.path.isabs(logical):
        raise BenchmarkToolError(
            f"provider transport dependency path is not absolute: {logical}"
        )
    try:
        link_metadata = os.lstat(logical)
        symlink_target = (
            os.readlink(logical) if stat.S_ISLNK(link_metadata.st_mode) else None
        )
        flags = os.O_RDONLY | os.O_CLOEXEC
        if nofollow:
            if not hasattr(os, "O_NOFOLLOW"):
                raise BenchmarkToolError(
                    "provider transport O_NOFOLLOW is unavailable"
                )
            flags |= os.O_NOFOLLOW
        descriptor = os.open(logical, flags)
    except (OSError, ValueError) as error:
        raise BenchmarkToolError(
            f"provider transport dependency cannot be opened: {logical}: {error}"
        ) from error
    try:
        metadata = os.fstat(descriptor)
        if not stat.S_ISREG(metadata.st_mode):
            raise BenchmarkToolError(
                f"provider transport dependency is not regular: {logical}"
            )
        try:
            resolved = os.readlink(f"/proc/self/fd/{descriptor}")
        except OSError as error:
            raise BenchmarkToolError(
                f"provider transport dependency fd cannot be resolved: {logical}"
            ) from error
        if resolved.endswith(" (deleted)") or not os.path.isabs(resolved):
            raise BenchmarkToolError(
                f"provider transport dependency fd is unstable: {logical}"
            )
        payload = _provider_transport_read_all(descriptor)
        if len(payload) != metadata.st_size:
            raise BenchmarkToolError(
                f"provider transport dependency changed while read: {logical}"
            )
    finally:
        os.close(descriptor)
    return (
        {
            "logical_path": logical,
            "resolved_path": os.path.realpath(resolved),
            "symlink_target": symlink_target,
            "sha256": hashlib.sha256(payload).hexdigest(),
            "bytes": len(payload),
            "mode": f"{stat.S_IMODE(metadata.st_mode):04o}",
        },
        payload,
    )


def _provider_transport_descriptor(
    logical_path: os.PathLike[str] | str,
) -> dict[str, Any]:
    descriptor, _payload = _provider_transport_dependency(logical_path)
    return descriptor


def _provider_transport_module_descriptor(
    module: Any, label: str
) -> dict[str, Any]:
    path = getattr(module, "__file__", None)
    if not isinstance(path, str) or not path:
        raise BenchmarkToolError(
            f"provider transport module {label} is not file-backed"
        )
    return _provider_transport_descriptor(path)


def _provider_transport_loaded_library_path(basename_prefix: str) -> str:
    try:
        maps = Path("/proc/self/maps").read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise BenchmarkToolError(
            "provider transport loaded libraries cannot be enumerated"
        ) from error
    candidates: set[str] = set()
    for line in maps.splitlines():
        fields = line.split(maxsplit=5)
        if len(fields) == 6:
            path = fields[5]
            if path.startswith("/") and Path(path).name.startswith(basename_prefix):
                candidates.add(os.path.realpath(path))
    if len(candidates) != 1:
        raise BenchmarkToolError(
            "provider transport loaded library is ambiguous or absent: "
            + basename_prefix
        )
    return next(iter(candidates))


def _provider_transport_system_library_path(filename: str) -> str:
    multiarch = sysconfig.get_config_var("MULTIARCH")
    if not isinstance(multiarch, str) or not multiarch:
        raise BenchmarkToolError("provider transport Python MULTIARCH is unavailable")
    candidates = (
        Path("/usr/lib") / multiarch / filename,
        Path("/lib") / multiarch / filename,
    )
    for candidate in candidates:
        if candidate.is_file():
            return os.fspath(candidate)
    raise BenchmarkToolError(
        f"provider transport resolver library is absent: {filename}"
    )


def _build_provider_transport_provenance() -> dict[str, Any]:
    """Independently construct the gate's exact stdlib/TLS trust record."""

    present = [
        name for name in PROVIDER_TRANSPORT_ENV_REQUIRED_ABSENT if name in os.environ
    ]
    if present:
        raise BenchmarkToolError(
            "provider transport override environment is present: "
            + ",".join(present)
        )
    ca_descriptor, ca_payload = _provider_transport_dependency(
        PROVIDER_CA_BUNDLE_PATH,
        nofollow=True,
    )
    try:
        ca_pem = ca_payload.decode("ascii", errors="strict")
    except UnicodeDecodeError as error:
        raise BenchmarkToolError(
            "provider transport CA bundle is not strict ASCII PEM"
        ) from error
    if (
        not ca_pem
        or "-----BEGIN CERTIFICATE-----" not in ca_pem
        or "\x00" in ca_pem
    ):
        raise BenchmarkToolError("provider transport CA bundle is not nonempty PEM")

    context = ssl.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    context.verify_mode = ssl.CERT_REQUIRED
    context.check_hostname = True
    context.minimum_version = ssl.TLSVersion.TLSv1_2
    context.maximum_version = ssl.TLSVersion.MAXIMUM_SUPPORTED
    context.set_alpn_protocols(PROVIDER_TLS_ALPN_PROTOCOLS)
    try:
        context.load_verify_locations(cadata=ca_pem)
    except ssl.SSLError as error:
        raise BenchmarkToolError(
            "provider transport explicit CA bundle could not be loaded"
        ) from error
    if context.keylog_filename is not None:
        raise BenchmarkToolError("provider transport TLS key logging is enabled")
    ca_count = context.cert_store_stats().get("x509_ca")
    if isinstance(ca_count, bool) or not isinstance(ca_count, int) or ca_count < 1:
        raise BenchmarkToolError(
            "provider transport explicit CA bundle loaded no authorities"
        )
    socket_origin = getattr(getattr(_socket, "__spec__", None), "origin", None)
    if socket_origin != "built-in" or getattr(_socket, "__file__", None) is not None:
        raise BenchmarkToolError("provider transport _socket is not built-in")
    cipher_names = [cipher.get("name") for cipher in context.get_ciphers()]
    if not cipher_names or not all(
        isinstance(name, str) and name for name in cipher_names
    ):
        raise BenchmarkToolError("provider transport cipher inventory is malformed")
    cipher_payload = (
        json.dumps(
            cipher_names,
            separators=(",", ":"),
            ensure_ascii=False,
        )
        + "\n"
    ).encode("utf-8")

    return {
        "schema_version": PROVIDER_TRANSPORT_SCHEMA_VERSION,
        "kind": PROVIDER_TRANSPORT_KIND,
        "connection_factory_mode": PROVIDER_CONNECTION_FACTORY_MODE,
        "python": {
            "executable": sys.executable,
            "version": sys.version.split()[0],
            "implementation": sys.implementation.name,
            "binary": _provider_transport_descriptor(sys.executable),
            "ssl_module": _provider_transport_module_descriptor(ssl, "ssl"),
            "http_client_module": _provider_transport_module_descriptor(
                http.client, "http.client"
            ),
            "socket_module": _provider_transport_module_descriptor(socket, "socket"),
            "http_server_module": _provider_transport_module_descriptor(
                http_server, "http.server"
            ),
            "json_module": _provider_transport_module_descriptor(json, "json"),
            "json_encoder_module": _provider_transport_module_descriptor(
                json_encoder, "json.encoder"
            ),
            "json_decoder_module": _provider_transport_module_descriptor(
                json_decoder, "json.decoder"
            ),
            "json_extension": _provider_transport_module_descriptor(_json, "_json"),
            "hashlib_module": _provider_transport_module_descriptor(
                hashlib, "hashlib"
            ),
            "hashlib_extension": _provider_transport_module_descriptor(
                _hashlib, "_hashlib"
            ),
            "ssl_extension": _provider_transport_module_descriptor(_ssl, "_ssl"),
            "socket_implementation": socket_origin,
        },
        "openssl": {
            "version": ssl.OPENSSL_VERSION,
            "version_number": ssl.OPENSSL_VERSION_NUMBER,
            "libssl": _provider_transport_descriptor(
                _provider_transport_loaded_library_path("libssl.so")
            ),
            "libcrypto": _provider_transport_descriptor(
                _provider_transport_loaded_library_path("libcrypto.so")
            ),
            "config": _provider_transport_descriptor(PROVIDER_OPENSSL_CONFIG_PATH),
        },
        "tls": {
            "protocol": context.protocol.name,
            "protocol_value": int(context.protocol),
            "server_hostname": "chatgpt.com",
            "server_port": 443,
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
            "cipher_names_sha256": hashlib.sha256(cipher_payload).hexdigest(),
        },
        "resolver": {
            "policy": PROVIDER_RESOLVER_POLICY,
            "hostname": "chatgpt.com",
            "resolv_conf": _provider_transport_descriptor(
                PROVIDER_RESOLV_CONF_PATH
            ),
            "nsswitch_conf": _provider_transport_descriptor(
                PROVIDER_NSSWITCH_PATH
            ),
            "hosts_file": _provider_transport_descriptor(PROVIDER_HOSTS_PATH),
            "gai_conf": _provider_transport_descriptor(PROVIDER_GAI_CONF_PATH),
            "libc": _provider_transport_descriptor(
                _provider_transport_loaded_library_path("libc.so")
            ),
            "libnss_dns": _provider_transport_descriptor(
                _provider_transport_system_library_path("libnss_dns.so.2")
            ),
            "libnss_files": _provider_transport_descriptor(
                _provider_transport_system_library_path("libnss_files.so.2")
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


def authenticate_provider_transport_provenance(
    agent_command: Sequence[str],
) -> dict[str, Any]:
    """Recompute provenance in the exact sanitized adapter interpreter."""

    if not agent_command:
        raise BenchmarkToolError("agent command has no adapter interpreter")
    interpreter = Path(agent_command[0])
    if not interpreter.is_absolute():
        raise BenchmarkToolError("adapter interpreter path must be absolute")
    try:
        metadata = interpreter.lstat()
    except OSError as error:
        raise BenchmarkToolError(
            f"cannot inspect adapter interpreter: {error}"
        ) from error
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
        raise BenchmarkToolError(
            "adapter interpreter must be a regular non-symlink file"
        )
    probe_source = (
        "import json,runner;"
        "value=runner._build_provider_transport_provenance();"
        "print(json.dumps(value,sort_keys=True,separators=(',',':'),"
        "ensure_ascii=False))"
    )
    try:
        completed = subprocess.run(
            [os.fspath(interpreter), "-c", probe_source],
            cwd=Path(__file__).resolve().parent,
            env=_sanitized_provider_transport_environment(),
            stdin=subprocess.DEVNULL,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            check=False,
            timeout=30.0,
        )
    except (OSError, subprocess.TimeoutExpired) as error:
        raise BenchmarkToolError(
            f"cannot derive provider transport provenance: {error}"
        ) from error
    if completed.returncode != 0 or completed.stderr != b"":
        stderr = completed.stderr.decode("utf-8", errors="replace").strip()
        raise BenchmarkToolError(
            "provider transport provenance probe failed"
            + (f": {stderr}" if stderr else "")
        )
    try:
        text = completed.stdout.decode("utf-8", errors="strict")
        value = json.loads(text)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise BenchmarkToolError(
            f"provider transport provenance probe is not strict JSON: {error}"
        ) from error
    canonical = (
        json.dumps(
            value,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        )
        + "\n"
    )
    if text != canonical:
        raise BenchmarkToolError(
            "provider transport provenance probe is not canonical JSON"
        )
    provenance = _validate_provider_transport_provenance(
        value,
        field="probe",
    )
    python_record = provenance["python"]
    if (
        python_record["executable"] != os.fspath(interpreter)
        or python_record["binary"]["logical_path"] != os.fspath(interpreter)
    ):
        raise BenchmarkToolError(
            "provider transport probe used another adapter interpreter"
        )
    return provenance


def _prompt_source_descriptor(
    path: Path,
    *,
    relative: str,
    expected: Mapping[str, Any],
    label: str,
) -> dict[str, Any]:
    if path.is_symlink() or not path.is_file():
        raise BenchmarkToolError(f"{label} must be a regular non-symlink file: {path}")
    digest = sha256_file(path)
    byte_count = path.stat().st_size
    if (
        expected.get("path") != relative
        or expected.get("sha256") != digest
        or type(expected.get("bytes")) is not int
        or expected.get("bytes") != byte_count
    ):
        raise BenchmarkToolError(f"{label} does not match authenticated prompt metadata")
    return {"path": relative, "sha256": digest, "bytes": byte_count}


def _controlled_prompt_source(
    task_destination: Path,
    manifest: Mapping[str, Any],
    command_path: str,
    *,
    label: str,
) -> tuple[dict[str, Any], str]:
    path = Path(command_path).resolve()
    try:
        relative = path.relative_to(task_destination.resolve()).as_posix()
    except ValueError as error:
        raise BenchmarkToolError(
            f"agent {label} path is outside the authenticated staged task"
        ) from error
    entries = manifest.get("files")
    entry = next(
        (
            item
            for item in entries
            if isinstance(item, Mapping) and item.get("path") == relative
        ),
        None,
    ) if isinstance(entries, list) else None
    if not isinstance(entry, Mapping):
        raise BenchmarkToolError(f"agent {label} is not in the controlled manifest")
    descriptor = _prompt_source_descriptor(
        path,
        relative=relative,
        expected=entry,
        label=label,
    )
    try:
        text = path.read_text(encoding="utf-8")
    except (OSError, UnicodeError) as error:
        raise BenchmarkToolError(f"cannot read authenticated {label}: {error}") from error
    return descriptor, text


def build_prompt_provenance(
    *,
    condition: str,
    freeze_check: Mapping[str, Any],
    agent_command: Sequence[str],
    task_root: Path,
    task_destination: Path,
    controlled_manifest: Mapping[str, Any],
    canonical_target: Path,
    include_effective_text: bool = False,
) -> dict[str, Any] | None:
    """Authenticate and hash the exact prompt payload before releasing it.

    Legacy raw-access snapshots did not carry ``prompt_protocol`` and retain
    their old record shape.  A signposted snapshot fails closed unless the
    staged common/context/target files, L-only supplement, and adapter argv all
    agree with the embedded frozen-run verification.
    """

    raw_protocol = freeze_check.get("prompt_protocol")
    if raw_protocol is None:
        return None
    if not isinstance(raw_protocol, Mapping):
        raise BenchmarkToolError("freeze_check.prompt_protocol must be an object")
    protocol = raw_protocol
    if (
        protocol.get("version") != SIGNPOSTED_PROMPT_PROTOCOL_VERSION
        or protocol.get("composition_order") != SIGNPOSTED_PROMPT_COMPOSITION_ORDER
        or protocol.get("N_receives_condition_supplement") is not False
        or protocol.get("relevant_theorem_or_module_hints_supplied") is not False
    ):
        raise BenchmarkToolError("freeze_check contains an invalid signposted prompt protocol")

    command_condition = _command_option_value(
        agent_command, "--condition", required=True
    )
    if command_condition != condition:
        raise BenchmarkToolError("agent command condition disagrees with the run")

    prompt_path = _command_option_value(agent_command, "--prompt-file", required=True)
    context_path = _command_option_value(agent_command, "--context-file", required=True)
    target_path = _command_option_value(agent_command, "--target-file", required=True)
    assert prompt_path is not None and context_path is not None and target_path is not None
    if Path(target_path).resolve() != canonical_target.resolve():
        raise BenchmarkToolError("agent prompt target is not the canonical staged target")

    common_descriptor, common_text = _controlled_prompt_source(
        task_destination,
        controlled_manifest,
        prompt_path,
        label="common prompt",
    )
    raw_common = protocol.get("common_prompt")
    if not isinstance(raw_common, Mapping):
        raise BenchmarkToolError("prompt protocol has no common-prompt descriptor")
    if common_descriptor != dict(raw_common):
        raise BenchmarkToolError("staged common prompt disagrees with the frozen protocol")
    context_descriptor, context_text = _controlled_prompt_source(
        task_destination,
        controlled_manifest,
        context_path,
        label="task context",
    )
    target_descriptor, target_text = _controlled_prompt_source(
        task_destination,
        controlled_manifest,
        target_path,
        label="fixed target",
    )

    supplements = protocol.get("condition_supplements")
    if not isinstance(supplements, Mapping) or set(supplements) != {"L"}:
        raise BenchmarkToolError("prompt protocol must contain exactly one L supplement")
    raw_l_descriptor = supplements.get("L")
    if not isinstance(raw_l_descriptor, Mapping):
        raise BenchmarkToolError("prompt protocol has no condition-L supplement descriptor")

    supplement_descriptor: dict[str, Any] | None = None
    supplement_text: str | None = None
    condition_file = _command_option_value(
        agent_command, "--condition-prompt-file", required=condition == "L"
    )
    condition_digest = _command_option_value(
        agent_command, "--condition-prompt-sha256", required=condition == "L"
    )
    if condition == "N":
        if condition_file is not None or condition_digest is not None:
            raise BenchmarkToolError("condition N received condition-L prompt material")
    elif condition == "L":
        assert condition_file is not None and condition_digest is not None
        relative = raw_l_descriptor.get("path")
        if not isinstance(relative, str) or not relative:
            raise BenchmarkToolError("condition-L prompt path is invalid")
        source = resolve_below(task_root.resolve(), relative)
        if Path(condition_file).resolve() != source or condition_digest != raw_l_descriptor.get(
            "sha256"
        ):
            raise BenchmarkToolError(
                "condition-L agent command disagrees with the frozen supplement"
            )
        supplement_descriptor = _prompt_source_descriptor(
            source,
            relative=relative,
            expected=raw_l_descriptor,
            label="condition-L prompt supplement",
        )
        try:
            supplement_text = source.read_text(encoding="utf-8")
        except (OSError, UnicodeError) as error:
            raise BenchmarkToolError(
                f"cannot read authenticated condition-L prompt supplement: {error}"
            ) from error
    else:
        raise BenchmarkToolError(f"unsupported benchmark condition: {condition!r}")

    sections = [common_text.rstrip()]
    if supplement_text is not None:
        sections.append(supplement_text.rstrip())
    sections.extend(
        (
            "## Task context\n\n" + context_text.rstrip(),
            "## Fixed Lean target\n\n```lean\n" + target_text.rstrip() + "\n```",
        )
    )
    effective = "\n\n".join(sections) + "\n"
    effective_bytes = effective.encode("utf-8")
    result: dict[str, Any] = {
        "protocol_version": SIGNPOSTED_PROMPT_PROTOCOL_VERSION,
        "condition": condition,
        "composition_order": list(SIGNPOSTED_PROMPT_COMPOSITION_ORDER),
        "common_prompt": common_descriptor,
        "condition_supplement": supplement_descriptor,
        "task_context": context_descriptor,
        "fixed_target": target_descriptor,
        "effective_prompt": {
            "sha256": hashlib.sha256(effective_bytes).hexdigest(),
            "bytes": len(effective_bytes),
            "encoding": "utf-8",
            "composition": EFFECTIVE_PROMPT_COMPOSITION,
        },
        "authentication": {
            "computed_before_prompt_release": True,
            "frozen_protocol_match": True,
            "controlled_task_sources_match": True,
            "agent_command_match": True,
        },
    }
    if include_effective_text:
        # Internal-only handoff to the READY/GO verifier.  run_one removes this
        # key before the provenance is serialized into the benchmark record.
        result["_effective_prompt_text"] = effective
    return result


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


def _positive_int(value: Any, field: str) -> int:
    result = _nonnegative_int(value, field)
    if result == 0:
        raise BenchmarkToolError(f"usage field {field!r} must be positive")
    return result


def _validate_submission_wire(
    value: Mapping[str, Any], *, candidate_path: str, label: str
) -> None:
    """Revalidate the authenticated model-to-dynamic-tool wire binding."""

    wire_format = value.get("submission_transport")
    outer_raw_item_id = value.get("outer_raw_item_id")
    outer_call_id = value.get("outer_exec_call_id")
    outer_input = value.get("outer_exec_program")
    outer_input_bytes = value.get("outer_exec_program_bytes")
    outer_input_sha256 = value.get("outer_exec_program_sha256")
    if wire_format != NESTED_SUBMISSION_WIRE_FORMAT:
        raise BenchmarkToolError(f"{label} has an unknown submission wire format")
    if not isinstance(outer_call_id, str) or not outer_call_id:
        raise BenchmarkToolError(f"{label} lacks the outer exec call id")
    if not isinstance(outer_raw_item_id, str) or not outer_raw_item_id:
        raise BenchmarkToolError(f"{label} lacks the outer raw item id")
    if value.get("outer_raw_item_type") != "custom_tool_call":
        raise BenchmarkToolError(f"{label} has the wrong outer raw item type")
    if value.get("outer_exec_name") != "exec":
        raise BenchmarkToolError(f"{label} has the wrong outer exec name")
    inner_call_id = value.get("call_id")
    if not isinstance(inner_call_id, str) or not inner_call_id:
        raise BenchmarkToolError(f"{label} lacks the inner dynamic call id")
    if len({outer_raw_item_id, outer_call_id, inner_call_id}) != 3:
        raise BenchmarkToolError(f"{label} conflates outer and inner identities")
    if value.get("inner_dynamic_call_id") != inner_call_id:
        raise BenchmarkToolError(f"{label} does not bind its inner dynamic call id")
    if value.get("inner_dynamic_tool_name") != "submit_proof":
        raise BenchmarkToolError(f"{label} has the wrong inner dynamic tool")
    if value.get("inner_dynamic_arguments") != {"candidate_path": candidate_path}:
        raise BenchmarkToolError(f"{label} has the wrong inner dynamic arguments")
    outer_observed_ns = _positive_int(
        value.get("outer_raw_item_observed_at_monotonic_ns"),
        f"{label}.outer_raw_item_observed_at_monotonic_ns",
    )
    inner_started_ns = _positive_int(
        value.get("inner_dynamic_item_started_at_monotonic_ns"),
        f"{label}.inner_dynamic_item_started_at_monotonic_ns",
    )
    if (
        value.get("outer_raw_item_observed_before_inner_dynamic_call") is not True
        or outer_observed_ns > inner_started_ns
    ):
        raise BenchmarkToolError(f"{label} has invalid outer/inner event order")
    if not is_canonical_nested_submit_exec_input(
        outer_input, candidate_path=candidate_path
    ):
        raise BenchmarkToolError(f"{label} has non-canonical nested exec source")
    assert isinstance(outer_input, str)
    expected_digest = hashlib.sha256(outer_input.encode("utf-8")).hexdigest()
    if (
        outer_input_bytes != NESTED_SUBMISSION_EXEC_SOURCE_BYTES
        or len(outer_input.encode("utf-8")) != NESTED_SUBMISSION_EXEC_SOURCE_BYTES
        or outer_input_sha256 != expected_digest
        or outer_input_sha256 != NESTED_SUBMISSION_EXEC_SOURCE_SHA256
    ):
        raise BenchmarkToolError(f"{label} nested exec source digest mismatch")
    expected_yield = nested_submission_exec_yield_record()
    if any(value.get(field) != expected for field, expected in expected_yield.items()):
        raise BenchmarkToolError(f"{label} nested exec yield envelope mismatch")


def _validate_submission_event_order(
    value: Mapping[str, Any], *, label: str, derive_from_timestamps: bool
) -> None:
    """Require one truthful order for the two observed submission events."""

    dynamic_before = value.get(
        "dynamic_call_observed_before_raw_response_completed"
    )
    response_before = value.get(
        "raw_response_completed_before_dynamic_call_observed"
    )
    order = value.get("submission_event_order")
    if (dynamic_before, response_before) == (True, False):
        expected_order = SUBMISSION_EVENT_ORDER_INNER_THEN_RESPONSE
    elif (dynamic_before, response_before) == (False, True):
        expected_order = SUBMISSION_EVENT_ORDER_RESPONSE_THEN_INNER
    else:
        raise BenchmarkToolError(
            f"{label} does not attest exactly one submission event order"
        )
    if order != expected_order:
        raise BenchmarkToolError(f"{label} submission event order is inconsistent")
    if not derive_from_timestamps:
        return
    captured_ns = _positive_int(
        value.get("captured_at_monotonic_ns"),
        f"{label}.captured_at_monotonic_ns",
    )
    response_ns = _positive_int(
        value.get("raw_response_observed_at_monotonic_ns"),
        f"{label}.raw_response_observed_at_monotonic_ns",
    )
    inner_started_ns = _positive_int(
        value.get("inner_dynamic_item_started_at_monotonic_ns"),
        f"{label}.inner_dynamic_item_started_at_monotonic_ns",
    )
    if captured_ns == response_ns:
        raise BenchmarkToolError(f"{label} submission event order is ambiguous")
    derived_dynamic_before = captured_ns < response_ns
    if dynamic_before is not derived_dynamic_before:
        raise BenchmarkToolError(
            f"{label} submission event order contradicts its timestamps"
        )
    if dynamic_before is True:
        valid_sequence = inner_started_ns <= captured_ns < response_ns
    else:
        valid_sequence = response_ns < inner_started_ns <= captured_ns
    if not valid_sequence:
        raise BenchmarkToolError(
            f"{label} dynamic-start/inner-call/response order is inconsistent"
        )


def read_token_usage(path: Path | None) -> dict[str, Any] | None:
    """Read trusted, live cumulative provider usage.

    The required meaning of ``input_tokens`` is total input tokens including
    cached input.  ``cached_input_tokens`` is retained for audit and is not
    added a second time.  Source, cumulative-scope, cached-input, sequence, and
    trusted adapter timestamp metadata are mandatory.  Lists of cumulative
    snapshots are rejected because summing them would double-count earlier
    totals and selecting one would weaken the atomic latest-update contract.
    """

    if path is None or not path.is_file():
        return None
    try:
        value = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        raise BenchmarkToolError(f"cannot read token usage {path}: {error}") from error
    if isinstance(value, dict) and isinstance(value.get("calls"), list):
        raise BenchmarkToolError(
            "live cumulative usage JSON must be one atomic top-level object, not calls"
        )
    if not isinstance(value, dict):
        raise BenchmarkToolError("live cumulative usage JSON must be an object")
    if value.get("measurement_source") == ULTRA_USAGE_MEASUREMENT_SOURCE:
        return _read_ultra_token_usage(value)
    metadata = {
        "measurement_source": value.get("measurement_source"),
        "live_cumulative": value.get("live_cumulative"),
        "input_includes_cached": value.get("input_includes_cached"),
        "notification_sequence": _positive_int(
            value.get("notification_sequence"), "notification_sequence"
        ),
        "observed_at_unix_ns": _positive_int(
            value.get("observed_at_unix_ns"), "observed_at_unix_ns"
        ),
    }
    if metadata["measurement_source"] != TOKEN_USAGE_MEASUREMENT_SOURCE:
        raise BenchmarkToolError(
            "usage measurement_source must identify the trusted Codex app-server "
            "token-usage notification"
        )
    if metadata["live_cumulative"] is not True:
        raise BenchmarkToolError("usage live_cumulative must be true")
    if metadata["input_includes_cached"] is not True:
        raise BenchmarkToolError("usage input_includes_cached must be true")
    input_tokens = _nonnegative_int(value.get("input_tokens"), "input_tokens")
    output_tokens = _nonnegative_int(value.get("output_tokens"), "output_tokens")
    cached_input_tokens = _nonnegative_int(
        value.get("cached_input_tokens", 0), "cached_input_tokens"
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
        "call_count": 1,
        **metadata,
    }


_ULTRA_FORK_POLICY_DYNAMIC_KEYS = {"call_evidence", "complete"}
_ULTRA_FORK_POLICY_CALL_KEYS = {
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


def _read_ultra_fork_policy(
    value: Mapping[str, Any],
    *,
    raw_spawn_ids: set[str],
    activity_spawn_ids: set[str],
    collab_spawn_ids: set[str],
    resolved_spawn_ids: set[str],
    failed_spawn_ids: set[str],
    response_ids: set[str],
    thread_ids: set[str],
    child_spawn_ids: set[str],
    projected_threads: Mapping[str, Mapping[str, Any]],
) -> dict[str, Any]:
    """Independently authenticate the frozen spawn policy and its call ledger.

    The adapter observes hook lifecycle notifications, but this runner does not
    trust its summary booleans or identifier sets.  It rechecks the fixed hook
    fingerprint, every raw-call/hook identity, the allow/block decision, and
    the absence of any activity for a policy-blocked call.
    """

    raw_policy = value.get("fork_policy")
    if not isinstance(raw_policy, Mapping):
        raise BenchmarkToolError("Ultra usage lacks the frozen fork policy")
    policy = dict(raw_policy)
    expected_static = ultra_fork_policy_static_record("/u501/m2fetrat")
    expected_keys = set(expected_static) | _ULTRA_FORK_POLICY_DYNAMIC_KEYS
    if set(policy) != expected_keys:
        raise BenchmarkToolError("Ultra fork policy has a missing or extra field")
    if any(
        type(policy.get(field)) is not type(expected)
        or policy.get(field) != expected
        for field, expected in expected_static.items()
    ):
        raise BenchmarkToolError("Ultra fork policy fingerprint is not frozen")
    usage_hint = policy["usage_hint"]
    if (
        not isinstance(usage_hint, str)
        or hashlib.sha256(usage_hint.encode("utf-8")).hexdigest()
        != policy["usage_hint_sha256"]
    ):
        raise BenchmarkToolError("Ultra fork-policy usage-hint hash is inconsistent")
    for field in ("helper_sha256", "hooks_json_sha256", "usage_hint_sha256"):
        if not isinstance(policy[field], str) or re.fullmatch(
            r"[0-9a-f]{64}", policy[field]
        ) is None:
            raise BenchmarkToolError(f"Ultra fork policy has an invalid {field}")

    raw_evidence = policy.get("call_evidence")
    if not isinstance(raw_evidence, list):
        raise BenchmarkToolError("Ultra fork policy call_evidence must be a list")
    evidence_by_id: dict[str, dict[str, Any]] = {}
    observed_ids: set[str] = set()
    allowed_ids: set[str] = set()
    blocked_ids: set[str] = set()
    invalid_ids: set[str] = set()
    complete_ids: set[str] = set()
    normalized_evidence: list[dict[str, Any]] = []
    expected_source_path = str(policy["source_path"])

    for index, raw in enumerate(raw_evidence):
        if not isinstance(raw, Mapping) or set(raw) != _ULTRA_FORK_POLICY_CALL_KEYS:
            raise BenchmarkToolError(
                f"Ultra fork-policy call evidence {index} has the wrong schema"
            )
        evidence = dict(raw)
        call_id = evidence.get("call_id")
        if (
            not isinstance(call_id, str)
            or re.fullmatch(r"call_[A-Za-z0-9_-]{1,120}", call_id) is None
            or call_id in evidence_by_id
        ):
            raise BenchmarkToolError("Ultra fork policy has an invalid call identity")
        evidence_by_id[call_id] = evidence
        for field in ("parent_thread_id", "parent_turn_id", "parent_response_id"):
            if not isinstance(evidence.get(field), str) or not evidence[field]:
                raise BenchmarkToolError(
                    f"Ultra fork-policy call {call_id} lacks {field}"
                )
        if evidence["parent_thread_id"] not in thread_ids:
            raise BenchmarkToolError(
                f"Ultra fork-policy call {call_id} has an unknown parent thread"
            )
        if evidence["parent_response_id"] not in response_ids:
            raise BenchmarkToolError(
                f"Ultra fork-policy call {call_id} has an unknown parent response"
            )

        fork_turns = evidence.get("fork_turns")
        fork_semantics = evidence.get("fork_semantics")
        expected_semantics = {
            "all": "full_history_parent_pre_response",
            "none": "no_history_zero",
        }.get(fork_turns)
        positive_fork = bool(
            isinstance(fork_turns, str)
            and re.fullmatch(r"[1-9][0-9]*", fork_turns) is not None
        )
        if positive_fork:
            expected_semantics = "unsupported_positive_turn_suffix"
        if fork_turns is None:
            fork_shape_valid = fork_semantics in (
                "invalid_arguments",
                "invalid_fork_turns",
            )
        else:
            fork_shape_valid = bool(
                expected_semantics is not None
                and fork_semantics == expected_semantics
            )
        expects_allow = fork_turns in ("all", "none") and fork_shape_valid

        started_count = _nonnegative_int(
            evidence.get("hook_started_count"),
            f"fork_policy.call_evidence[{index}].hook_started_count",
        )
        completed_count = _nonnegative_int(
            evidence.get("hook_completed_count"),
            f"fork_policy.call_evidence[{index}].hook_completed_count",
        )
        started_observed = evidence.get("hook_started_observed")
        completed_observed = evidence.get("hook_completed_observed")
        child_activity = evidence.get("child_activity_observed")
        if any(
            item not in (True, False)
            for item in (started_observed, completed_observed, child_activity)
        ):
            raise BenchmarkToolError(
                f"Ultra fork-policy call {call_id} lacks lifecycle booleans"
            )
        if started_observed is not (started_count > 0) or completed_observed is not (
            completed_count > 0
        ):
            raise BenchmarkToolError(
                f"Ultra fork-policy call {call_id} has inconsistent hook counts"
            )
        derived_child_activity = call_id in (activity_spawn_ids | collab_spawn_ids)
        if child_activity is not derived_child_activity:
            raise BenchmarkToolError(
                f"Ultra fork-policy call {call_id} has inconsistent child activity"
            )

        hook_fields = (
            evidence.get("hook_run_id"),
            evidence.get("hook_source_path"),
            evidence.get("hook_thread_id"),
            evidence.get("hook_turn_id"),
        )
        has_hook_identity = all(isinstance(item, str) and item for item in hook_fields)
        no_hook_identity = all(item is None for item in hook_fields)
        expected_run_id = (
            f"pre-tool-use:{policy['display_order']}:{expected_source_path}:{call_id}"
        )
        exact_hook_identity = bool(
            has_hook_identity
            and evidence["hook_run_id"] == expected_run_id
            and evidence["hook_source_path"] == expected_source_path
            and evidence["hook_thread_id"] == evidence["parent_thread_id"]
            and evidence["hook_turn_id"] == evidence["parent_turn_id"]
        )
        hook_status = evidence.get("hook_status")
        decision = evidence.get("decision")
        feedback = evidence.get("feedback")
        resolution_status = evidence.get("resolution_status")
        if not isinstance(resolution_status, str) or not resolution_status:
            raise BenchmarkToolError(
                f"Ultra fork-policy call {call_id} lacks a resolution status"
            )
        lifecycle_shape_valid = bool(
            (started_count, completed_count) in ((0, 0), (1, 0), (1, 1))
            and (no_hook_identity if started_count == 0 else has_hook_identity)
            and (completed_count == 0 or started_count == 1)
        )
        if started_count or completed_count:
            observed_ids.add(call_id)

        expected_feedback = ULTRA_FORK_POLICY_BLOCK_REASON_TEMPLATE.format(
            call_id=call_id
        )
        allow_terminal = bool(
            started_count == 1
            and completed_count == 1
            and exact_hook_identity
            and hook_status == ULTRA_FORK_POLICY_ALLOW_STATUS
            and decision == ULTRA_FORK_POLICY_ALLOW_DECISION
            and feedback is None
            and expects_allow
            and fork_shape_valid
            and resolution_status
            in (
                ULTRA_FORK_POLICY_ALLOWED_RESOLUTION_STATUS,
                "resolved_child",
                "failed_without_child",
            )
        )
        block_terminal = bool(
            started_count == 1
            and completed_count == 1
            and exact_hook_identity
            and hook_status == ULTRA_FORK_POLICY_BLOCK_STATUS
            and decision == ULTRA_FORK_POLICY_BLOCK_DECISION
            and feedback == expected_feedback
            and not expects_allow
            and fork_shape_valid
            and resolution_status == ULTRA_FORK_POLICY_BLOCKED_RESOLUTION_STATUS
            and not child_activity
        )
        awaiting = bool(
            completed_count == 0
            and fork_shape_valid
            and hook_status is None
            and decision is None
            and feedback is None
            and resolution_status == ULTRA_FORK_POLICY_AWAITING_HOOK_STATUS
        )
        explicitly_invalid = resolution_status == ULTRA_FORK_POLICY_INVALID_RESOLUTION_STATUS
        if allow_terminal:
            allowed_ids.add(call_id)
            complete_ids.add(call_id)
        elif block_terminal:
            blocked_ids.add(call_id)
            complete_ids.add(call_id)
        elif not (awaiting and lifecycle_shape_valid) or explicitly_invalid:
            invalid_ids.add(call_id)
        normalized_evidence.append(evidence)

    if list(evidence_by_id) != sorted(evidence_by_id):
        raise BenchmarkToolError("Ultra fork-policy call evidence is not sorted")
    if set(evidence_by_id) != raw_spawn_ids:
        raise BenchmarkToolError("Ultra fork-policy evidence does not cover raw spawn calls")

    def reported_ids(field: str) -> set[str]:
        raw_ids = value.get(field)
        if (
            not isinstance(raw_ids, list)
            or any(not isinstance(item, str) or not item for item in raw_ids)
            or raw_ids != sorted(set(raw_ids))
        ):
            raise BenchmarkToolError(f"Ultra usage {field} is not a sorted identifier set")
        return set(raw_ids)

    reported_observed = reported_ids("hook_observed_spawn_call_ids")
    reported_allowed = reported_ids("hook_allowed_spawn_call_ids")
    reported_blocked = reported_ids("hook_blocked_spawn_call_ids")
    reported_invalid = reported_ids("hook_invalid_spawn_call_ids")
    reported_policy_blocked = reported_ids("policy_blocked_spawn_call_ids")
    if (
        reported_observed != observed_ids
        or reported_allowed != allowed_ids
        or reported_blocked != blocked_ids
        or reported_invalid != invalid_ids
        or reported_policy_blocked != blocked_ids
    ):
        raise BenchmarkToolError("Ultra fork-policy identifier projection is inconsistent")
    if blocked_ids & (activity_spawn_ids | collab_spawn_ids | resolved_spawn_ids):
        raise BenchmarkToolError("Ultra policy-blocked spawn produced child activity")
    if child_spawn_ids - allowed_ids:
        raise BenchmarkToolError("Ultra child is not bound to a hook-allowed spawn")
    zero_baseline = {
        "input_tokens": 0,
        "cached_input_tokens": 0,
        "cache_write_input_tokens": 0,
        "output_tokens": 0,
        "reasoning_output_tokens": 0,
        "total_tokens": 0,
    }
    for thread_id, thread in projected_threads.items():
        if (
            thread.get("parent_thread_id") is None
            or thread.get("spawn_binding_status") != "resolved"
        ):
            continue
        call_id = thread.get("spawn_call_id")
        evidence = evidence_by_id.get(call_id) if isinstance(call_id, str) else None
        if evidence is None or call_id not in allowed_ids:
            raise BenchmarkToolError(
                f"Ultra child {thread_id} lacks hook-allowed spawn evidence"
            )
        if (
            evidence["parent_thread_id"] != thread.get("parent_thread_id")
            or evidence["parent_turn_id"] != thread.get("spawn_parent_turn_id")
            or evidence["parent_response_id"]
            != thread.get("spawn_parent_response_id")
            or evidence["fork_turns"] != thread.get("spawn_fork_turns")
            or evidence["fork_semantics"] != thread.get("spawn_fork_semantics")
        ):
            raise BenchmarkToolError(
                f"Ultra child {thread_id} disagrees with spawn-policy evidence"
            )
        if thread.get("spawn_fork_turns") == "none":
            if thread.get("expected_cumulative_baseline") != zero_baseline:
                raise BenchmarkToolError(
                    f"Ultra no-history child {thread_id} lacks a zero baseline"
                )
        elif thread.get("spawn_fork_turns") != "all":
            raise BenchmarkToolError(
                f"Ultra child {thread_id} used a disallowed fork projection"
            )
    if not blocked_ids <= failed_spawn_ids:
        raise BenchmarkToolError("Ultra policy-blocked spawn is not terminal failed")

    derived_complete = bool(
        complete_ids == raw_spawn_ids
        and not invalid_ids
        and not (blocked_ids & (activity_spawn_ids | collab_spawn_ids))
    )
    if policy.get("complete") not in (True, False) or value.get(
        "fork_policy_complete"
    ) not in (True, False):
        raise BenchmarkToolError("Ultra usage lacks fork-policy completeness booleans")
    if (
        policy["complete"] is not derived_complete
        or value["fork_policy_complete"] is not derived_complete
    ):
        raise BenchmarkToolError("Ultra fork-policy completeness is inconsistent")
    return {
        **expected_static,
        "call_evidence": normalized_evidence,
        "complete": derived_complete,
        "hook_observed_spawn_call_ids": sorted(observed_ids),
        "hook_allowed_spawn_call_ids": sorted(allowed_ids),
        "hook_blocked_spawn_call_ids": sorted(blocked_ids),
        "hook_invalid_spawn_call_ids": sorted(invalid_ids),
        "policy_blocked_spawn_call_ids": sorted(blocked_ids),
    }


def _rooted_collaboration_route_matches(
    *,
    thread_id: Any,
    author: Any,
    recipient: Any,
    projected_threads: Mapping[str, Mapping[str, Any]],
    root_thread_id: str,
) -> bool:
    """Independently authenticate one parent/child collaboration route."""

    if not all(
        isinstance(item, str) and item
        for item in (thread_id, author, recipient)
    ):
        return False
    target = projected_threads.get(str(thread_id))
    if not isinstance(target, Mapping):
        return False
    target_path = (
        "/root"
        if thread_id == root_thread_id
        else target.get("agent_path")
    )
    if recipient != target_path:
        return False
    author_matches = [
        candidate_thread_id
        for candidate_thread_id, thread in projected_threads.items()
        if (
            candidate_thread_id == root_thread_id
            and author == "/root"
        )
        or (
            thread.get("agent_path") == author
            and thread.get("provisional") is False
            and thread.get("spawn_binding_status") == "resolved"
        )
    ]
    if len(author_matches) != 1:
        return False
    author_thread_id = author_matches[0]
    author_thread = projected_threads[author_thread_id]
    return bool(
        target.get("parent_thread_id") == author_thread_id
        or author_thread.get("parent_thread_id") == thread_id
    )


def _read_ultra_token_usage(value: Mapping[str, Any]) -> dict[str, Any]:
    """Validate one atomic exact-response aggregate over an Ultra thread tree."""

    if value.get("notification") != ULTRA_USAGE_NOTIFICATION:
        raise BenchmarkToolError("Ultra usage has the wrong notification source")
    if value.get("usage_scope") != ULTRA_USAGE_SCOPE:
        raise BenchmarkToolError("Ultra usage has the wrong tree scope")
    if value.get("live_cumulative") is not True:
        raise BenchmarkToolError("Ultra usage live_cumulative must be true")
    if value.get("input_includes_cached") is not True:
        raise BenchmarkToolError("Ultra usage input_includes_cached must be true")
    root_thread_id = value.get("root_thread_id")
    if not isinstance(root_thread_id, str) or not root_thread_id:
        raise BenchmarkToolError("Ultra usage has no root thread id")
    root_turn_id = value.get("root_turn_id")
    if root_turn_id is not None and (
        not isinstance(root_turn_id, str) or not root_turn_id
    ):
        raise BenchmarkToolError("Ultra usage has an invalid root turn id")
    thread_count = _positive_int(value.get("thread_count"), "thread_count")
    response_count = _nonnegative_int(value.get("response_count"), "response_count")
    notification_sequence = _nonnegative_int(
        value.get("notification_sequence"), "notification_sequence"
    )
    if notification_sequence != response_count:
        raise BenchmarkToolError(
            "Ultra usage response count and notification sequence disagree"
        )
    observed_at_unix_ns = _positive_int(
        value.get("observed_at_unix_ns"), "observed_at_unix_ns"
    )
    field_names = (
        "input_tokens",
        "cached_input_tokens",
        "cache_write_input_tokens",
        "output_tokens",
        "reasoning_output_tokens",
        "total_tokens",
    )
    totals = {
        field: _nonnegative_int(value.get(field), field) for field in field_names
    }
    if totals["cached_input_tokens"] > totals["input_tokens"]:
        raise BenchmarkToolError("Ultra cached input exceeds total input")
    if totals["cache_write_input_tokens"] > totals["input_tokens"]:
        raise BenchmarkToolError("Ultra cache-write input exceeds total input")
    if totals["reasoning_output_tokens"] > totals["output_tokens"]:
        raise BenchmarkToolError("Ultra reasoning output exceeds total output")
    if totals["total_tokens"] != totals["input_tokens"] + totals["output_tokens"]:
        raise BenchmarkToolError("Ultra total tokens do not equal input plus output")
    threads = value.get("threads")
    if not isinstance(threads, list) or len(threads) != thread_count:
        raise BenchmarkToolError("Ultra usage thread_count disagrees with threads")

    def breakdown(raw: Any, field: str, *, nullable: bool = False) -> dict[str, int] | None:
        if raw is None and nullable:
            return None
        if not isinstance(raw, Mapping):
            raise BenchmarkToolError(f"Ultra usage {field} must be an object")
        result = {
            name: _nonnegative_int(raw.get(name), f"{field}.{name}")
            for name in field_names
        }
        if result["cached_input_tokens"] > result["input_tokens"]:
            raise BenchmarkToolError(f"Ultra usage {field} has excess cached input")
        if result["cache_write_input_tokens"] > result["input_tokens"]:
            raise BenchmarkToolError(f"Ultra usage {field} has excess cache-write input")
        if result["reasoning_output_tokens"] > result["output_tokens"]:
            raise BenchmarkToolError(f"Ultra usage {field} has excess reasoning output")
        if result["total_tokens"] != result["input_tokens"] + result["output_tokens"]:
            raise BenchmarkToolError(f"Ultra usage {field} has an invalid total")
        return result

    zero = {field: 0 for field in field_names}
    seen_threads: set[str] = set()
    summed = {field: 0 for field in field_names}
    summed_responses = 0
    projected_threads: dict[str, dict[str, Any]] = {}
    active_turns: dict[str, str] = {}
    provisional_thread_ids: set[str] = set()
    for index, raw_thread in enumerate(threads):
        if (
            not isinstance(raw_thread, Mapping)
            or set(raw_thread) != ULTRA_THREAD_LEDGER_KEYS
        ):
            raise BenchmarkToolError(
                f"Ultra usage thread {index} has the wrong schema"
            )
        thread_id = raw_thread.get("thread_id")
        if not isinstance(thread_id, str) or not thread_id or thread_id in seen_threads:
            raise BenchmarkToolError("Ultra usage has an invalid or duplicate thread id")
        seen_threads.add(thread_id)
        parent = raw_thread.get("parent_thread_id")
        if parent is not None and (not isinstance(parent, str) or not parent):
            raise BenchmarkToolError("Ultra usage has an invalid parent thread id")
        provisional = raw_thread.get("provisional")
        if type(provisional) is not bool:
            raise BenchmarkToolError("Ultra usage thread lacks provisional status")
        if provisional:
            provisional_thread_ids.add(thread_id)
        agent_path = raw_thread.get("agent_path")
        if agent_path is not None and (
            not isinstance(agent_path, str) or not agent_path
        ):
            raise BenchmarkToolError("Ultra usage thread has an invalid agent path")
        turn_seen = raw_thread.get("turn_seen")
        active_turn_id = raw_thread.get("active_turn_id")
        turn_status = raw_thread.get("turn_status")
        thread_status = raw_thread.get("thread_status")
        if type(turn_seen) is not bool:
            raise BenchmarkToolError("Ultra usage thread lacks exact turn-seen evidence")
        if active_turn_id is not None and (
            not isinstance(active_turn_id, str) or not active_turn_id
        ):
            raise BenchmarkToolError("Ultra usage thread has an invalid active turn")
        if turn_status not in (None, "inProgress", "completed", "failed", "interrupted"):
            raise BenchmarkToolError("Ultra usage thread has an invalid turn status")
        if thread_status is not None and (
            not isinstance(thread_status, str) or not thread_status
        ):
            raise BenchmarkToolError("Ultra usage thread has an invalid thread status")
        if active_turn_id is not None:
            if turn_seen is not True or turn_status != "inProgress":
                raise BenchmarkToolError(
                    "Ultra usage active turn contradicts its lifecycle state"
                )
            active_turns[thread_id] = active_turn_id
        elif turn_seen is False and turn_status is not None:
            raise BenchmarkToolError(
                "Ultra usage unseen turn has a terminal lifecycle state"
            )
        response_total = _nonnegative_int(
            raw_thread.get("response_count"), f"threads[{index}].response_count"
        )
        if response_total and turn_seen is not True:
            raise BenchmarkToolError("Ultra responding thread was never observed running")
        summed_responses += response_total
        raw_sum: dict[str, int] = {}
        for field in field_names:
            raw_sum[field] = _nonnegative_int(
                raw_thread.get(field), f"threads[{index}].{field}"
            )
            summed[field] += raw_sum[field]
        expected_baseline = breakdown(
            raw_thread.get("expected_cumulative_baseline"),
            f"threads[{index}].expected_cumulative_baseline",
            nullable=True,
        )
        compatibility_baseline = breakdown(
            raw_thread.get("cumulative_baseline"),
            f"threads[{index}].cumulative_baseline",
            nullable=True,
        )
        if compatibility_baseline != expected_baseline:
            raise BenchmarkToolError("Ultra cumulative-baseline alias disagrees")
        full_projection = breakdown(
            raw_thread.get("full_cumulative_projection"),
            f"threads[{index}].full_cumulative_projection",
            nullable=True,
        )
        expected_projection = breakdown(
            raw_thread.get("expected_cumulative_projection"),
            f"threads[{index}].expected_cumulative_projection",
            nullable=True,
        )
        last_cumulative = breakdown(
            raw_thread.get("last_cumulative"),
            f"threads[{index}].last_cumulative",
            nullable=True,
        )
        observed_baseline = breakdown(
            raw_thread.get("observed_cumulative_baseline"),
            f"threads[{index}].observed_cumulative_baseline",
            nullable=True,
        )
        exempt_usage = breakdown(
            raw_thread.get("cumulative_projection_exempt_response_usage"),
            f"threads[{index}].cumulative_projection_exempt_response_usage",
            nullable=True,
        )
        exempt_response_id = raw_thread.get(
            "cumulative_projection_exempt_response_id"
        )
        if exempt_response_id is not None and (
            not isinstance(exempt_response_id, str) or not exempt_response_id
        ):
            raise BenchmarkToolError("Ultra projection has an invalid exempt response")
        observation_count = _nonnegative_int(
            raw_thread.get("cumulative_observation_count"),
            f"threads[{index}].cumulative_observation_count",
        )
        if (observation_count == 0) != (last_cumulative is None):
            raise BenchmarkToolError("Ultra cumulative observation count is inconsistent")
        if expected_baseline is not None:
            derived_full = {
                field: expected_baseline[field] + raw_sum[field]
                for field in field_names
            }
            if full_projection != derived_full:
                raise BenchmarkToolError("Ultra full cumulative projection is inconsistent")
        elif full_projection is not None or expected_projection is not None:
            raise BenchmarkToolError("Ultra unresolved baseline has a token projection")
        if exempt_response_id is None:
            if exempt_usage is not None or expected_projection != full_projection:
                raise BenchmarkToolError("Ultra non-exempt projection is inconsistent")
        else:
            if thread_id != root_thread_id or exempt_usage is None:
                raise BenchmarkToolError("Ultra only the root may exempt one response")
            if expected_projection is None or full_projection is None:
                raise BenchmarkToolError("Ultra exempt projection is unresolved")
            if any(
                expected_projection[field] + exempt_usage[field]
                != full_projection[field]
                for field in field_names
            ):
                raise BenchmarkToolError("Ultra exempt response projection is inconsistent")
        projection_match = raw_thread.get("cumulative_projection_match")
        baseline_match = raw_thread.get("cumulative_baseline_matches_expected")
        thread_accounting = raw_thread.get("accounting_complete")
        if any(
            value not in (True, False)
            for value in (projection_match, baseline_match, thread_accounting)
        ):
            raise BenchmarkToolError("Ultra thread lacks accounting booleans")
        projection_status = raw_thread.get("cumulative_projection_status")
        if not isinstance(projection_status, str) or not projection_status:
            raise BenchmarkToolError("Ultra thread lacks projection status")
        if expected_baseline is None:
            derived_baseline = None
            derived_baseline_match = False
            derived_match = False
            derived_status = "unresolved_expected_baseline"
        elif last_cumulative is None:
            derived_baseline = None
            derived_match = bool(
                exempt_response_id is not None
                and expected_projection == zero
                and expected_baseline == zero
            )
            derived_baseline_match = derived_match
            derived_status = (
                "zero_pre_response_without_cumulative_notification"
                if derived_match
                else "missing_cumulative"
            )
        else:
            use_full = bool(
                exempt_response_id is not None and last_cumulative == full_projection
            )
            comparison_projection = (
                full_projection if use_full else expected_projection
            )
            comparison_raw = dict(raw_sum)
            if exempt_response_id is not None and not use_full:
                assert exempt_usage is not None
                comparison_raw = {
                    field: raw_sum[field] - exempt_usage[field]
                    for field in field_names
                }
                if any(value < 0 for value in comparison_raw.values()):
                    raise BenchmarkToolError("Ultra exempt usage exceeds root raw sum")
            differences = {
                field: last_cumulative[field] - comparison_raw[field]
                for field in field_names
            }
            derived_baseline = (
                differences
                if (
                    all(value >= 0 for value in differences.values())
                    and differences["cached_input_tokens"]
                    <= differences["input_tokens"]
                    and differences["cache_write_input_tokens"]
                    <= differences["input_tokens"]
                    and differences["reasoning_output_tokens"]
                    <= differences["output_tokens"]
                    and differences["total_tokens"]
                    == differences["input_tokens"]
                    + differences["output_tokens"]
                )
                else None
            )
            derived_baseline_match = (
                derived_baseline is not None
                and expected_baseline is not None
                and derived_baseline == expected_baseline
            )
            derived_match = bool(
                comparison_projection is not None
                and last_cumulative == comparison_projection
                and derived_baseline_match
            )
            if exempt_response_id is not None and use_full:
                derived_status = "matched_full_including_exempt_response"
            elif exempt_response_id is not None and (
                last_cumulative == expected_projection
            ):
                derived_status = "matched_pre_exempt_response"
            elif exempt_response_id is None and (
                last_cumulative == expected_projection
            ):
                derived_status = "matched_full_projection"
            else:
                derived_status = "cumulative_projection_mismatch"
        if observed_baseline != derived_baseline:
            raise BenchmarkToolError("Ultra observed cumulative baseline is inconsistent")
        if baseline_match is not derived_baseline_match or projection_match is not derived_match:
            raise BenchmarkToolError("Ultra cumulative projection booleans are inconsistent")
        if projection_status != derived_status:
            raise BenchmarkToolError("Ultra cumulative projection status is inconsistent")
        binding_status = raw_thread.get("spawn_binding_status")
        spawn_call_id = raw_thread.get("spawn_call_id")
        spawn_parent_turn_id = raw_thread.get("spawn_parent_turn_id")
        spawn_parent_response_id = raw_thread.get("spawn_parent_response_id")
        spawn_fork_turns = raw_thread.get("spawn_fork_turns")
        spawn_fork_semantics = raw_thread.get("spawn_fork_semantics")
        if thread_id == root_thread_id:
            if (
                binding_status != "root_zero"
                or any(
                    item is not None
                    for item in (
                        spawn_call_id,
                        spawn_parent_turn_id,
                        spawn_parent_response_id,
                        spawn_fork_turns,
                        spawn_fork_semantics,
                    )
                )
                or expected_baseline != zero
            ):
                raise BenchmarkToolError("Ultra root baseline is not the frozen zero baseline")
            binding_complete = True
        else:
            if not isinstance(binding_status, str) or not binding_status:
                raise BenchmarkToolError("Ultra child lacks spawn-binding status")
            binding_complete = binding_status == "resolved"
            if binding_complete:
                if not all(
                    isinstance(item, str) and item
                    for item in (
                        spawn_call_id,
                        spawn_parent_turn_id,
                        spawn_parent_response_id,
                    )
                ):
                    raise BenchmarkToolError("Ultra resolved child lacks spawn identity")
                expected_semantics = {
                    "none": "no_history_zero",
                    "all": "full_history_parent_pre_response",
                }.get(spawn_fork_turns)
                if expected_semantics is None or spawn_fork_semantics != expected_semantics:
                    raise BenchmarkToolError("Ultra resolved child has unsupported fork semantics")
                if expected_baseline is None:
                    raise BenchmarkToolError("Ultra resolved child lacks expected baseline")
        if thread_accounting is not bool(binding_complete and derived_match):
            raise BenchmarkToolError("Ultra thread accounting completeness is inconsistent")
        projected_threads[thread_id] = {
            "thread_id": thread_id,
            "parent_thread_id": parent,
            "agent_path": agent_path,
            "provisional": provisional,
            "turn_seen": turn_seen,
            "active_turn_id": active_turn_id,
            "turn_status": turn_status,
            "thread_status": thread_status,
            "response_count": response_total,
            **raw_sum,
            "spawn_call_id": spawn_call_id,
            "spawn_parent_turn_id": spawn_parent_turn_id,
            "spawn_parent_response_id": spawn_parent_response_id,
            "spawn_fork_turns": spawn_fork_turns,
            "spawn_fork_semantics": spawn_fork_semantics,
            "spawn_binding_status": binding_status,
            "expected_cumulative_baseline": expected_baseline,
            "expected_cumulative_projection": expected_projection,
            "full_cumulative_projection": full_projection,
            "last_cumulative": last_cumulative,
            "cumulative_observation_count": observation_count,
            "observed_cumulative_baseline": observed_baseline,
            "cumulative_baseline_matches_expected": derived_baseline_match,
            "cumulative_projection_status": projection_status,
            "cumulative_projection_match": derived_match,
            "cumulative_projection_exempt_response_id": exempt_response_id,
            "cumulative_projection_exempt_response_usage": exempt_usage,
            "accounting_complete": bool(thread_accounting),
        }
    if root_thread_id not in seen_threads:
        raise BenchmarkToolError("Ultra usage root is absent from the thread ledger")
    if projected_threads[root_thread_id]["parent_thread_id"] is not None:
        raise BenchmarkToolError("Ultra usage root has a parent")
    if (
        projected_threads[root_thread_id]["agent_path"] != "root"
        or projected_threads[root_thread_id]["provisional"] is not False
    ):
        raise BenchmarkToolError("Ultra usage root lacks its frozen root identity")
    if root_turn_id is None:
        if projected_threads[root_thread_id]["turn_seen"] is True:
            raise BenchmarkToolError("Ultra usage observed a root turn without its identity")
    elif projected_threads[root_thread_id]["turn_seen"] is not True:
        raise BenchmarkToolError("Ultra usage root turn identity was never observed")
    for thread_id, projected in projected_threads.items():
        if thread_id == root_thread_id:
            continue
        parent = projected["parent_thread_id"]
        if parent not in seen_threads or parent == thread_id:
            raise BenchmarkToolError("Ultra child has an invalid parent edge")
        spawn_response = projected["spawn_parent_response_id"]
        if spawn_response is not None and spawn_response not in value.get(
            "response_ids", []
        ):
            raise BenchmarkToolError("Ultra child spawn response is absent from ledger")
        ancestry: set[str] = set()
        current: str | None = thread_id
        while current is not None:
            if current in ancestry:
                raise BenchmarkToolError("Ultra thread projection contains a cycle")
            ancestry.add(current)
            parent_value = projected_threads[current]["parent_thread_id"]
            current = parent_value if isinstance(parent_value, str) else None
    if summed_responses != response_count:
        raise BenchmarkToolError("Ultra usage per-thread response counts disagree")
    if summed != totals:
        raise BenchmarkToolError("Ultra usage per-thread token sums disagree")
    response_ids = value.get("response_ids")
    if (
        not isinstance(response_ids, list)
        or len(response_ids) != response_count
        or any(not isinstance(item, str) or not item for item in response_ids)
        or len(set(response_ids)) != len(response_ids)
    ):
        raise BenchmarkToolError("Ultra usage response-id ledger is inconsistent")

    raw_response_ledger = value.get("response_ledger")
    if not isinstance(raw_response_ledger, list) or len(raw_response_ledger) != response_count:
        raise BenchmarkToolError("Ultra usage response ledger has the wrong length")
    response_ledger: list[dict[str, Any]] = []
    ledger_ids: set[str] = set()
    ledger_sequences: set[int] = set()
    ledger_totals = {field: 0 for field in field_names}
    ledger_by_thread = {
        thread_id: {
            "response_count": 0,
            **{field: 0 for field in field_names},
        }
        for thread_id in seen_threads
    }
    for index, raw_response in enumerate(raw_response_ledger):
        if not isinstance(raw_response, Mapping) or set(raw_response) != ULTRA_RESPONSE_LEDGER_KEYS:
            raise BenchmarkToolError(
                f"Ultra response ledger entry {index} has the wrong schema"
            )
        response_id = raw_response.get("response_id")
        thread_id = raw_response.get("thread_id")
        turn_id = raw_response.get("turn_id")
        if (
            not isinstance(response_id, str)
            or not response_id
            or response_id in ledger_ids
            or not isinstance(thread_id, str)
            or not thread_id
            or not isinstance(turn_id, str)
            or not turn_id
        ):
            raise BenchmarkToolError("Ultra response ledger has an invalid identity")
        sequence = _positive_int(
            raw_response.get("raw_response_notification_sequence"),
            f"response_ledger[{index}].raw_response_notification_sequence",
        )
        if sequence != index + 1 or sequence in ledger_sequences:
            raise BenchmarkToolError("Ultra response ledger reused an event sequence")
        observed_unix_ns = _positive_int(
            raw_response.get("raw_response_observed_at_unix_ns"),
            f"response_ledger[{index}].raw_response_observed_at_unix_ns",
        )
        observed_monotonic_ns = _positive_int(
            raw_response.get("raw_response_observed_at_monotonic_ns"),
            f"response_ledger[{index}].raw_response_observed_at_monotonic_ns",
        )
        normalized_usage = _provider_gate_usage(
            raw_response.get("usage"), f"response_ledger[{index}].usage"
        )
        if thread_id not in ledger_by_thread:
            raise BenchmarkToolError("Ultra response ledger cites an unknown thread")
        for field in field_names:
            ledger_totals[field] += normalized_usage[field]
            ledger_by_thread[thread_id][field] += normalized_usage[field]
        ledger_by_thread[thread_id]["response_count"] += 1
        embedded_call = raw_response.get("provider_gate_call")
        if embedded_call is not None and not isinstance(embedded_call, Mapping):
            raise BenchmarkToolError("Ultra response ledger has malformed gate evidence")
        ledger_ids.add(response_id)
        ledger_sequences.add(sequence)
        response_ledger.append(
            {
                "response_id": response_id,
                "thread_id": thread_id,
                "turn_id": turn_id,
                "raw_response_notification_sequence": sequence,
                "raw_response_observed_at_unix_ns": observed_unix_ns,
                "raw_response_observed_at_monotonic_ns": observed_monotonic_ns,
                "usage": normalized_usage,
                "provider_gate_call": dict(embedded_call) if embedded_call is not None else None,
            }
        )
    if (
        ledger_ids != set(response_ids)
        or response_ids
        != [response["response_id"] for response in response_ledger]
        or ledger_sequences != set(range(1, response_count + 1))
        or ledger_totals != totals
    ):
        raise BenchmarkToolError("Ultra response ledger does not reproduce its aggregate")
    for thread_id, projected in projected_threads.items():
        ledger_projection = ledger_by_thread[thread_id]
        if ledger_projection != {
            "response_count": projected["response_count"],
            **{field: projected[field] for field in field_names},
        }:
            raise BenchmarkToolError(
                "Ultra response ledger does not reproduce its per-thread aggregate"
            )

    root_responses = [
        response for response in response_ledger if response["thread_id"] == root_thread_id
    ]
    if root_turn_id is None:
        if root_responses:
            raise BenchmarkToolError("Ultra root response lacks a root turn identity")
    else:
        distinct_root_responses = [
            response
            for response in root_responses
            if response["turn_id"] != root_turn_id
        ]
        if distinct_root_responses:
            # The pinned adapter authorizes exactly one second root turn, and only
            # for the explicit provider-token-gate compaction canary after the
            # prompt turn has completed.  Preserve that shape independently in
            # the scorer so an arbitrary second root response cannot be relabeled
            # as a compaction crossing.
            if (
                thread_count != 1
                or response_count != 2
                or len(root_responses) != 2
                or root_responses[0]["turn_id"] != root_turn_id
                or len(distinct_root_responses) != 1
                or distinct_root_responses[0] is not root_responses[1]
                or active_turns.get(root_thread_id)
                != distinct_root_responses[0]["turn_id"]
            ):
                raise BenchmarkToolError(
                    "Ultra second root turn is not the exact compaction-canary shape"
                )
            prompt_gate_call = root_responses[0].get("provider_gate_call")
            compaction_gate_call = root_responses[1].get("provider_gate_call")
            prompt_metadata = (
                prompt_gate_call.get("request_metadata")
                if isinstance(prompt_gate_call, Mapping)
                else None
            )
            compaction_metadata = (
                compaction_gate_call.get("request_metadata")
                if isinstance(compaction_gate_call, Mapping)
                else None
            )
            if (
                not isinstance(prompt_gate_call, Mapping)
                or prompt_gate_call.get("crossed_cap") is not False
                or prompt_gate_call.get("release_kind") != "byte_identity"
                or not isinstance(prompt_metadata, Mapping)
                or prompt_metadata.get("request_kind") != "turn"
                or not isinstance(compaction_gate_call, Mapping)
                or compaction_gate_call.get("crossed_cap") is not True
                or compaction_gate_call.get("release_kind")
                != PROVIDER_GATE_COMPACTION_CROSSING_RELEASE
                or not isinstance(compaction_metadata, Mapping)
                or compaction_metadata.get("request_kind") != "compaction"
            ):
                raise BenchmarkToolError(
                    "Ultra second root turn lacks exact provider compaction evidence"
                )

    raw_gate_summary = value.get("provider_token_gate")
    provider_gate_summary: dict[str, Any] | None = None
    if raw_gate_summary is not None:
        if not isinstance(raw_gate_summary, Mapping) or set(raw_gate_summary) != ULTRA_PROVIDER_GATE_SUMMARY_KEYS:
            raise BenchmarkToolError("Ultra usage provider-gate summary has the wrong schema")
        provider_gate_summary = dict(raw_gate_summary)
        if (
            provider_gate_summary["enabled"] is not True
            or provider_gate_summary["response_token_bound"]
            != PROVIDER_RESPONSE_TOKEN_BOUND
            or isinstance(provider_gate_summary["response_token_bound"], bool)
            or provider_gate_summary["final_attached"] not in (True, False)
            or provider_gate_summary["exact_for_usage"] not in (True, False)
            or not isinstance(provider_gate_summary["live"], Mapping)
        ):
            raise BenchmarkToolError("Ultra usage provider-gate summary is malformed")
        if provider_gate_summary["final_attached"]:
            artifact_path = provider_gate_summary["artifact_path"]
            if not isinstance(artifact_path, str) or not Path(artifact_path).is_absolute():
                raise BenchmarkToolError("Ultra usage gate artifact path is not absolute")
            _provider_gate_sha256(
                provider_gate_summary["record_sha256"],
                "usage.provider_token_gate.record_sha256",
            )
            if (
                provider_gate_summary["exact_for_usage"] is not True
                or not isinstance(provider_gate_summary["terminal"], Mapping)
            ):
                raise BenchmarkToolError("Ultra final usage lacks exact gate attachment")

    raw_reconciliation = value.get("provider_usage_reconciliation")
    provider_usage_reconciliation: dict[str, Any] | None = None
    if raw_reconciliation is not None:
        if (
            not isinstance(raw_reconciliation, Mapping)
            or set(raw_reconciliation) != set(PROVIDER_USAGE_RECONCILIATION_KEYS)
            or raw_reconciliation.get("schema_version")
            != PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION
        ):
            raise BenchmarkToolError(
                "Ultra provider usage reconciliation has the wrong schema"
            )
        provider_count = _nonnegative_int(
            raw_reconciliation.get("provider_response_count"),
            "provider_usage_reconciliation.provider_response_count",
        )
        appserver_count = _nonnegative_int(
            raw_reconciliation.get("appserver_response_count"),
            "provider_usage_reconciliation.appserver_response_count",
        )
        suppressed_count = _nonnegative_int(
            raw_reconciliation.get(
                "suppressed_collaboration_wait_response_count"
            ),
            "provider_usage_reconciliation.suppressed_collaboration_wait_response_count",
        )
        superseded_count = _nonnegative_int(
            raw_reconciliation.get(
                "superseded_by_collaboration_message_response_count"
            ),
            "provider_usage_reconciliation.superseded_by_collaboration_message_response_count",
        )
        discarded_count = _nonnegative_int(
            raw_reconciliation.get(
                "discarded_after_explicit_child_interrupt_response_count"
            ),
            "provider_usage_reconciliation.discarded_after_explicit_child_interrupt_response_count",
        )
        provider_usage = breakdown(
            raw_reconciliation.get("provider_usage"),
            "provider_usage_reconciliation.provider_usage",
        )
        appserver_usage = breakdown(
            raw_reconciliation.get("appserver_usage"),
            "provider_usage_reconciliation.appserver_usage",
        )
        suppressed_usage = breakdown(
            raw_reconciliation.get("suppressed_collaboration_wait_usage"),
            "provider_usage_reconciliation.suppressed_collaboration_wait_usage",
        )
        superseded_usage = breakdown(
            raw_reconciliation.get(
                "superseded_by_collaboration_message_usage"
            ),
            "provider_usage_reconciliation.superseded_by_collaboration_message_usage",
        )
        discarded_usage = breakdown(
            raw_reconciliation.get(
                "discarded_after_explicit_child_interrupt_usage"
            ),
            "provider_usage_reconciliation.discarded_after_explicit_child_interrupt_usage",
        )
        assert provider_usage is not None
        assert appserver_usage is not None
        assert suppressed_usage is not None
        assert superseded_usage is not None
        assert discarded_usage is not None

        def reconciliation_ids(field: str, expected_count: int) -> list[str]:
            raw_ids = raw_reconciliation.get(field)
            if (
                not isinstance(raw_ids, list)
                or len(raw_ids) != expected_count
                or any(not isinstance(item, str) or not item for item in raw_ids)
                or len(set(raw_ids)) != len(raw_ids)
            ):
                raise BenchmarkToolError(
                    f"Ultra provider usage reconciliation has invalid {field}"
                )
            return list(raw_ids)

        provider_ids = reconciliation_ids("provider_response_ids", provider_count)
        appserver_ids = reconciliation_ids("appserver_response_ids", appserver_count)
        suppressed_ids = reconciliation_ids(
            "suppressed_collaboration_wait_response_ids", suppressed_count
        )
        superseded_ids = reconciliation_ids(
            "superseded_by_collaboration_message_response_ids",
            superseded_count,
        )
        discarded_ids = reconciliation_ids(
            "discarded_after_explicit_child_interrupt_response_ids",
            discarded_count,
        )
        raw_evidence = raw_reconciliation.get(
            "suppressed_collaboration_wait_evidence"
        )
        if not isinstance(raw_evidence, list) or len(raw_evidence) != suppressed_count:
            raise BenchmarkToolError(
                "Ultra suppressed-wait evidence has the wrong length"
            )
        evidence: list[dict[str, Any]] = []
        evidence_response_ids: list[str] = []
        evidence_message_ids: set[str] = set()
        for index, raw_item in enumerate(raw_evidence):
            if (
                not isinstance(raw_item, Mapping)
                or set(raw_item) != set(SUPPRESSED_COLLABORATION_WAIT_EVIDENCE_KEYS)
            ):
                raise BenchmarkToolError(
                    f"Ultra suppressed-wait evidence {index} has the wrong schema"
                )
            item = dict(raw_item)
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
            ):
                if not isinstance(item.get(field), str) or not item[field]:
                    raise BenchmarkToolError(
                        f"Ultra suppressed-wait evidence {index} lacks {field}"
                    )
            if (
                re.fullmatch(r"[0-9a-f]{64}", item["agent_message_sha256"])
                is None
                or item["agent_message_recipient"] != "/root"
            ):
                raise BenchmarkToolError(
                    "Ultra suppressed-wait evidence has invalid child-message identity"
                )
            for field in (
                "agent_message_observed_at_unix_ns",
                "agent_message_observed_at_monotonic_ns",
            ):
                _positive_int(item.get(field), f"suppressed evidence {index}.{field}")
            if item["agent_message_item_id"] in evidence_message_ids:
                raise BenchmarkToolError(
                    "Ultra suppressed waits reuse one child-result message"
                )
            evidence_message_ids.add(item["agent_message_item_id"])
            evidence_response_ids.append(item["response_id"])
            evidence.append(item)
        raw_superseded_evidence = raw_reconciliation.get(
            "superseded_by_collaboration_message_evidence"
        )
        if (
            not isinstance(raw_superseded_evidence, list)
            or len(raw_superseded_evidence) != superseded_count
        ):
            raise BenchmarkToolError(
                "Ultra superseded-response evidence has the wrong length"
            )
        superseded_evidence: list[dict[str, Any]] = []
        superseded_evidence_response_ids: list[str] = []
        for index, raw_item in enumerate(raw_superseded_evidence):
            if (
                not isinstance(raw_item, Mapping)
                or set(raw_item)
                != set(SUPERSEDED_BY_COLLABORATION_MESSAGE_EVIDENCE_KEYS)
            ):
                raise BenchmarkToolError(
                    f"Ultra superseded-response evidence {index} has the wrong schema"
                )
            item = dict(raw_item)
            for field in (
                "response_id",
                "provider_call_id",
                "thread_id",
                "turn_id",
                "successor_response_id",
                "successor_call_id",
            ):
                if not isinstance(item.get(field), str) or not item[field]:
                    raise BenchmarkToolError(
                        f"Ultra superseded-response evidence {index} lacks {field}"
                    )
            messages = item.get("collaboration_messages")
            if not isinstance(messages, list) or not messages:
                raise BenchmarkToolError(
                    "Ultra superseded-response evidence has no child messages"
                )
            normalized_messages: list[dict[str, Any]] = []
            for message_index, raw_message in enumerate(messages):
                if (
                    not isinstance(raw_message, Mapping)
                    or set(raw_message) != set(COLLABORATION_MESSAGE_EVIDENCE_KEYS)
                ):
                    raise BenchmarkToolError(
                        "Ultra superseded-response child-message evidence has the wrong schema"
                    )
                message = dict(raw_message)
                if (
                    not isinstance(message.get("item_id"), str)
                    or not message["item_id"]
                    or message["item_id"] in evidence_message_ids
                    or not isinstance(message.get("item_sha256"), str)
                    or re.fullmatch(r"[0-9a-f]{64}", message["item_sha256"])
                    is None
                    or not _rooted_collaboration_route_matches(
                        thread_id=item.get("thread_id"),
                        author=message.get("author"),
                        recipient=message.get("recipient"),
                        projected_threads=projected_threads,
                        root_thread_id=root_thread_id,
                    )
                ):
                    raise BenchmarkToolError(
                        "Ultra superseded-response child-message identity is invalid"
                    )
                _positive_int(
                    message.get("observed_at_unix_ns"),
                    f"superseded evidence {index}.messages[{message_index}].observed_at_unix_ns",
                )
                _positive_int(
                    message.get("observed_at_monotonic_ns"),
                    f"superseded evidence {index}.messages[{message_index}].observed_at_monotonic_ns",
                )
                evidence_message_ids.add(message["item_id"])
                normalized_messages.append(message)
            if normalized_messages != sorted(
                normalized_messages,
                key=lambda message: (
                    message["observed_at_unix_ns"],
                    message["item_id"],
                    message["observed_at_monotonic_ns"],
                ),
            ):
                raise BenchmarkToolError(
                    "Ultra superseded-response child messages are out of order"
                )
            item["collaboration_messages"] = normalized_messages
            superseded_evidence_response_ids.append(item["response_id"])
            superseded_evidence.append(item)
        raw_discarded_evidence = raw_reconciliation.get(
            "discarded_after_explicit_child_interrupt_evidence"
        )
        if (
            not isinstance(raw_discarded_evidence, list)
            or len(raw_discarded_evidence) != discarded_count
        ):
            raise BenchmarkToolError(
                "Ultra explicit-child-interrupt evidence has the wrong length"
            )
        discarded_evidence: list[dict[str, Any]] = []
        discarded_evidence_response_ids: list[str] = []
        for index, raw_item in enumerate(raw_discarded_evidence):
            if (
                not isinstance(raw_item, Mapping)
                or set(raw_item)
                != set(DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_EVIDENCE_KEYS)
            ):
                raise BenchmarkToolError(
                    f"Ultra explicit-child-interrupt evidence {index} has the wrong schema"
                )
            item = dict(raw_item)
            for field in (
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
            ):
                if not isinstance(item.get(field), str) or not item[field]:
                    raise BenchmarkToolError(
                        f"Ultra explicit-child-interrupt evidence {index} lacks {field}"
                    )
            for field in (
                "interrupt_function_arguments_sha256",
                "interrupt_activity_item_sha256",
                "interrupt_output_item_sha256",
            ):
                if (
                    not isinstance(item.get(field), str)
                    or re.fullmatch(r"[0-9a-f]{64}", item[field]) is None
                ):
                    raise BenchmarkToolError(
                        f"Ultra explicit-child-interrupt evidence {index} has invalid {field}"
                    )
            for prefix in (
                "interrupt_function",
                "interrupt_activity",
                "interrupt_output",
                "interrupted_turn",
            ):
                _positive_int(
                    item.get(f"{prefix}_observed_at_unix_ns"),
                    f"explicit-child-interrupt evidence {index}.{prefix}_observed_at_unix_ns",
                )
                _positive_int(
                    item.get(f"{prefix}_observed_at_monotonic_ns"),
                    f"explicit-child-interrupt evidence {index}.{prefix}_observed_at_monotonic_ns",
                )
            child = projected_threads.get(item["thread_id"])
            parent = projected_threads.get(item["interrupt_parent_thread_id"])
            if (
                not isinstance(child, Mapping)
                or not isinstance(parent, Mapping)
                or child.get("parent_thread_id")
                != item["interrupt_parent_thread_id"]
                or child.get("agent_path") != item["interrupted_agent_path"]
                or not item["interrupted_agent_path"].startswith("/root/")
                or item["interrupting_response_id"] not in appserver_ids
                or item["response_id"] in appserver_ids
            ):
                raise BenchmarkToolError(
                    "Ultra explicit-child-interrupt evidence has an invalid direct-child route"
                )
            discarded_evidence_response_ids.append(item["response_id"])
            discarded_evidence.append(item)
        if (
            appserver_count != response_count
            or appserver_ids != list(response_ids)
            or appserver_usage != totals
            or provider_count
            != appserver_count + suppressed_count + superseded_count + discarded_count
            or evidence_response_ids != suppressed_ids
            or superseded_evidence_response_ids != superseded_ids
            or discarded_evidence_response_ids != discarded_ids
            or set(provider_ids)
            != set(appserver_ids)
            | set(suppressed_ids)
            | set(superseded_ids)
            | set(discarded_ids)
            or set(appserver_ids) & set(suppressed_ids)
            or set(appserver_ids) & set(superseded_ids)
            or set(suppressed_ids) & set(superseded_ids)
            or set(appserver_ids) & set(discarded_ids)
            or set(suppressed_ids) & set(discarded_ids)
            or set(superseded_ids) & set(discarded_ids)
            or any(
                provider_usage[field]
                != appserver_usage[field]
                + suppressed_usage[field]
                + superseded_usage[field]
                + discarded_usage[field]
                for field in field_names
            )
        ):
            raise BenchmarkToolError(
                "Ultra provider/app-server usage partition is inconsistent"
            )
        provider_usage_reconciliation = {
            **dict(raw_reconciliation),
            "provider_usage": provider_usage,
            "appserver_usage": appserver_usage,
            "suppressed_collaboration_wait_usage": suppressed_usage,
            "provider_response_ids": provider_ids,
            "appserver_response_ids": appserver_ids,
            "suppressed_collaboration_wait_response_ids": suppressed_ids,
            "suppressed_collaboration_wait_evidence": evidence,
            "superseded_by_collaboration_message_usage": superseded_usage,
            "superseded_by_collaboration_message_response_ids": superseded_ids,
            "superseded_by_collaboration_message_evidence": superseded_evidence,
            "discarded_after_explicit_child_interrupt_usage": discarded_usage,
            "discarded_after_explicit_child_interrupt_response_ids": discarded_ids,
            "discarded_after_explicit_child_interrupt_evidence": discarded_evidence,
        }
    if (
        provider_gate_summary is not None
        and provider_gate_summary.get("final_attached") is True
        and provider_gate_summary.get("exact_for_usage") is True
        and provider_usage_reconciliation is None
    ):
        raise BenchmarkToolError("Ultra exact provider usage lacks reconciliation")

    raw_teardown = value.get("adapter_teardown")
    adapter_teardown: dict[str, Any] | None = None
    if raw_teardown is not None:
        if not isinstance(raw_teardown, Mapping) or set(raw_teardown) != ULTRA_ADAPTER_TEARDOWN_KEYS:
            raise BenchmarkToolError("Ultra app-server teardown has the wrong schema")
        adapter_teardown = dict(raw_teardown)
        if (
            adapter_teardown["process_group_isolated"] is not True
            or adapter_teardown["stdin_closed"] is not True
            or adapter_teardown["completed"] is not True
            or adapter_teardown["immediate"] not in (True, False)
            or not isinstance(adapter_teardown["returncode"], int)
            or isinstance(adapter_teardown["returncode"], bool)
            or adapter_teardown["signal"] not in (None, "SIGTERM", "SIGKILL")
        ):
            raise BenchmarkToolError("Ultra app-server teardown is incomplete")
        for clock in ("unix", "monotonic"):
            started = _positive_int(
                adapter_teardown[f"started_at_{clock}_ns"],
                f"adapter_teardown.started_at_{clock}_ns",
            )
            completed = _positive_int(
                adapter_teardown[f"completed_at_{clock}_ns"],
                f"adapter_teardown.completed_at_{clock}_ns",
            )
            if completed < started:
                raise BenchmarkToolError("Ultra app-server teardown timestamps regress")
    if (
        value.get("accounting_projection_schema_version")
        != ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION
    ):
        raise BenchmarkToolError("Ultra usage lacks the frozen accounting projection schema")

    def identifier_list(field: str) -> list[str]:
        raw = value.get(field)
        if (
            not isinstance(raw, list)
            or any(not isinstance(item, str) or not item for item in raw)
            or raw != sorted(set(raw))
        ):
            raise BenchmarkToolError(f"Ultra usage {field} is not a sorted identifier set")
        return list(raw)

    if value.get("spawn_binding_source") != (
        "raw_function_call.call_id=subAgentActivity.id"
    ):
        raise BenchmarkToolError("Ultra usage has the wrong spawn-binding source")
    raw_spawn_ids = set(identifier_list("raw_spawn_call_ids"))
    activity_spawn_ids = set(identifier_list("activity_spawn_call_ids"))
    collab_spawn_ids = set(identifier_list("collab_spawn_call_ids"))
    resolved_spawn_ids = set(identifier_list("resolved_spawn_call_ids"))
    failed_spawn_ids = set(identifier_list("failed_spawn_call_ids"))
    unresolved_spawn_ids = set(identifier_list("unresolved_spawn_call_ids"))
    unsupported_spawn_ids = set(identifier_list("unsupported_spawn_call_ids"))
    inference_child_ids = set(identifier_list("inference_child_thread_ids"))
    if resolved_spawn_ids & failed_spawn_ids:
        raise BenchmarkToolError("Ultra spawn call cannot both resolve and fail")
    expected_terminal_spawn_ids = resolved_spawn_ids | failed_spawn_ids
    expected_unresolved_spawn_ids = (
        raw_spawn_ids | activity_spawn_ids | collab_spawn_ids
    ) - expected_terminal_spawn_ids
    if unresolved_spawn_ids != expected_unresolved_spawn_ids:
        raise BenchmarkToolError("Ultra unresolved spawn-call projection is inconsistent")
    if not unsupported_spawn_ids <= unresolved_spawn_ids:
        raise BenchmarkToolError("Ultra unsupported spawn calls are not unresolved")
    child_thread_ids = seen_threads - {root_thread_id}
    if inference_child_ids != child_thread_ids:
        raise BenchmarkToolError("Ultra inference-child projection disagrees with threads")
    child_spawn_ids = {
        str(projected_threads[thread_id]["spawn_call_id"])
        for thread_id in child_thread_ids
        if projected_threads[thread_id]["spawn_call_id"] is not None
    }
    fork_policy = _read_ultra_fork_policy(
        value,
        raw_spawn_ids=raw_spawn_ids,
        activity_spawn_ids=activity_spawn_ids,
        collab_spawn_ids=collab_spawn_ids,
        resolved_spawn_ids=resolved_spawn_ids,
        failed_spawn_ids=failed_spawn_ids,
        response_ids=set(response_ids),
        thread_ids=seen_threads,
        child_spawn_ids=child_spawn_ids,
        projected_threads=projected_threads,
    )
    derived_spawn_complete = bool(
        raw_spawn_ids == expected_terminal_spawn_ids
        and activity_spawn_ids == resolved_spawn_ids
        and collab_spawn_ids <= expected_terminal_spawn_ids
        and not unsupported_spawn_ids
        and not unresolved_spawn_ids
        and child_spawn_ids == resolved_spawn_ids
        and len(child_spawn_ids) == len(child_thread_ids)
        and fork_policy["complete"]
    )
    spawn_linkage_complete = value.get("spawn_linkage_complete")
    descendant_accounting_complete = value.get(
        "descendant_accounting_complete"
    )
    cumulative_projection_complete = value.get(
        "cumulative_projection_complete"
    )
    accounting_complete = value.get("accounting_complete")
    if any(
        item not in (True, False)
        for item in (
            spawn_linkage_complete,
            descendant_accounting_complete,
            cumulative_projection_complete,
            accounting_complete,
        )
    ):
        raise BenchmarkToolError("Ultra usage lacks accounting-completeness booleans")
    derived_descendant_complete = all(
        projected_threads[thread_id]["accounting_complete"]
        for thread_id in child_thread_ids
    )
    derived_cumulative_complete = all(
        thread["cumulative_projection_match"]
        for thread in projected_threads.values()
    )
    derived_accounting_complete = bool(
        derived_spawn_complete
        and derived_cumulative_complete
        and all(
            thread["accounting_complete"] for thread in projected_threads.values()
        )
    )
    if (
        spawn_linkage_complete is not derived_spawn_complete
        or descendant_accounting_complete is not derived_descendant_complete
        or cumulative_projection_complete is not derived_cumulative_complete
        or accounting_complete is not derived_accounting_complete
    ):
        raise BenchmarkToolError("Ultra accounting-completeness projection is inconsistent")
    drain_complete = value.get("drain_complete")
    measurement_exact = value.get("measurement_exact")
    if drain_complete not in (True, False) or measurement_exact not in (True, False):
        raise BenchmarkToolError("Ultra usage lacks drain/exactness booleans")
    active_thread_ids = value.get("active_thread_ids")
    unresolved_thread_ids = value.get("unresolved_thread_ids")
    invalid_reasons = value.get("invalid_reasons")
    interrupt_requested = value.get("interrupt_requested")
    if interrupt_requested not in (True, False):
        raise BenchmarkToolError("Ultra usage lacks an interrupt-requested boolean")
    pending_interrupt_response_count = _nonnegative_int(
        value.get("pending_interrupt_response_count"),
        "pending_interrupt_response_count",
    )
    if not all(
        isinstance(items, list) and all(isinstance(item, str) for item in items)
        for items in (active_thread_ids, unresolved_thread_ids, invalid_reasons)
    ):
        raise BenchmarkToolError("Ultra usage has malformed lifecycle evidence")
    if (
        active_thread_ids != sorted(active_turns)
        or unresolved_thread_ids != sorted(provisional_thread_ids)
        or len(invalid_reasons) != len(set(invalid_reasons))
    ):
        raise BenchmarkToolError("Ultra usage lifecycle identifier sets are inconsistent")
    boundary_raw = value.get("submission_boundary")
    boundary: dict[str, Any] | None = None
    boundary_exact = False
    if boundary_raw is not None:
        if not isinstance(boundary_raw, Mapping):
            raise BenchmarkToolError("Ultra submission boundary must be an object")
        boundary = dict(boundary_raw)
        required_strings = (
            "request_sha256",
            "ack_sha256",
            "challenge_sha256",
            "call_sha256",
            "attempt_nonce",
            "run_id",
            "validator_contract_sha256",
            "call_id",
            "thread_id",
            "turn_id",
            "response_id",
            "candidate_path",
            "candidate_sha256",
        )
        if any(
            not isinstance(boundary.get(field), str) or not boundary[field]
            for field in required_strings
        ):
            raise BenchmarkToolError("Ultra submission boundary lacks an identity")
        _validate_submission_wire(
            boundary,
            candidate_path=str(boundary["candidate_path"]),
            label="Ultra submission boundary",
        )
        if not all(
            re.fullmatch(r"[0-9a-f]{64}", str(boundary[field]))
            for field in (
                "request_sha256",
                "ack_sha256",
                "challenge_sha256",
                "call_sha256",
                "validator_contract_sha256",
                "candidate_sha256",
            )
        ):
            raise BenchmarkToolError("Ultra submission boundary has an invalid digest")
        _positive_int(boundary.get("sequence"), "submission_boundary.sequence")
        _nonnegative_int(
            boundary.get("candidate_size_bytes"),
            "submission_boundary.candidate_size_bytes",
        )
        _positive_int(
            boundary.get("raw_response_notification_sequence"),
            "submission_boundary.raw_response_notification_sequence",
        )
        for field in (
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
            "inner_dynamic_call_left_blocked",
        ):
            if boundary.get(field) is not True:
                raise BenchmarkToolError(
                    f"Ultra submission boundary lacks {field} evidence"
                )
        if (
            boundary.get("inner_dynamic_tool_response_sent") is not False
            or boundary.get("outer_exec_output_emitted") is not False
            or boundary.get("later_model_response_possible") is not False
            or boundary.get("current_response_cumulative_required") is not False
        ):
            raise BenchmarkToolError("Ultra submission boundary permits post-proof work")
        _validate_submission_event_order(
            boundary,
            label="Ultra submission boundary",
            derive_from_timestamps=False,
        )
        if projected_threads[root_thread_id][
            "cumulative_projection_exempt_response_id"
        ] != boundary.get("response_id") or any(
            projected_threads[thread_id][
                "cumulative_projection_exempt_response_id"
            ]
            is not None
            for thread_id in seen_threads
            if thread_id != root_thread_id
        ):
            raise BenchmarkToolError(
                "Ultra cumulative exception is not the accepted root response"
            )
        boundary_exact = (
            boundary.get("schema_version") == SUBMISSION_BARRIER_SCHEMA_VERSION
            and boundary.get("authenticated") is True
            and boundary.get("status") == "accepted"
            and boundary.get("exact") is True
            and boundary.get("thread_id") == root_thread_id
            and boundary.get("response_id") in response_ids
            and boundary.get("raw_response_notification_sequence")
            <= notification_sequence
            and value.get("stop_reason") == "first_valid_proof"
            and drain_complete is False
            and active_thread_ids == [root_thread_id]
            and not unresolved_thread_ids
            and not invalid_reasons
            and accounting_complete is True
            and spawn_linkage_complete is True
            and descendant_accounting_complete is True
            and cumulative_projection_complete is True
            and interrupt_requested is False
            and pending_interrupt_response_count == 0
            and value.get("first_crossing") is None
        )
        if not boundary_exact:
            raise BenchmarkToolError(
                "Ultra accepted boundary contradicts rooted-tree lifecycle evidence"
            )
    elif any(
        projected["cumulative_projection_exempt_response_id"] is not None
        for projected in projected_threads.values()
    ):
        raise BenchmarkToolError("Ultra natural usage has an exempt response")
    raw_first_crossing = value.get("first_crossing")
    first_crossing: dict[str, Any] | None = None
    crossing_exact = False
    if raw_first_crossing is not None:
        if not isinstance(raw_first_crossing, Mapping) or set(raw_first_crossing) != {
            "response_id",
            "notification_sequence",
            "observed_at_unix_ns",
            "tokens",
            "active_thread_ids",
        }:
            raise BenchmarkToolError("Ultra first crossing has the wrong schema")
        first_crossing = dict(raw_first_crossing)
        crossing_response_id = first_crossing.get("response_id")
        crossing_sequence = _positive_int(
            first_crossing.get("notification_sequence"),
            "first_crossing.notification_sequence",
        )
        _positive_int(
            first_crossing.get("observed_at_unix_ns"),
            "first_crossing.observed_at_unix_ns",
        )
        crossing_tokens = _nonnegative_int(
            first_crossing.get("tokens"), "first_crossing.tokens"
        )
        crossing_usage = (
            provider_usage_reconciliation["provider_usage"]
            if provider_usage_reconciliation is not None
            else totals
        )
        crossing_active = first_crossing.get("active_thread_ids")
        if (
            not isinstance(crossing_response_id, str)
            or crossing_response_id not in response_ids
            or crossing_sequence > notification_sequence
            or crossing_tokens != crossing_usage["total_tokens"]
            or not isinstance(crossing_active, list)
            or any(not isinstance(item, str) or not item for item in crossing_active)
            or crossing_active != sorted(set(crossing_active))
        ):
            raise BenchmarkToolError("Ultra first crossing is inconsistent")
        terminal = (
            provider_gate_summary.get("terminal")
            if isinstance(provider_gate_summary, Mapping)
            else None
        )
        gate_crossing = terminal.get("crossing") if isinstance(terminal, Mapping) else None
        crossing_ledger = [
            response
            for response in response_ledger
            if response.get("response_id") == crossing_response_id
        ]
        crossing_gate_call = (
            crossing_ledger[0].get("provider_gate_call")
            if len(crossing_ledger) == 1
            else None
        )
        crossing_crossbind = (
            crossing_gate_call.get("appserver_crossbind")
            if isinstance(crossing_gate_call, Mapping)
            else None
        )
        gate_crossing_request_kind = (
            gate_crossing.get("request_kind")
            if isinstance(gate_crossing, Mapping)
            else None
        )
        call_request_metadata = (
            crossing_gate_call.get("request_metadata")
            if isinstance(crossing_gate_call, Mapping)
            else None
        )
        call_crossing_request_kind = (
            call_request_metadata.get("request_kind")
            if isinstance(call_request_metadata, Mapping)
            else None
        )
        expected_crossing_release = (
            _provider_gate_crossing_release_kind(gate_crossing_request_kind)
            if isinstance(gate_crossing_request_kind, str)
            and gate_crossing_request_kind
            else None
        )
        crossing_exact = bool(
            value.get("stop_reason") == "token_limit"
            and drain_complete is False
            and not invalid_reasons
            and interrupt_requested is False
            and pending_interrupt_response_count == 0
            and provider_gate_summary is not None
            and provider_gate_summary.get("final_attached") is True
            and provider_gate_summary.get("exact_for_usage") is True
            and isinstance(terminal, Mapping)
            and terminal.get("phase") == "CLOSED"
            and terminal.get("close_reason") == "token_limit"
            and terminal.get("crossing_closed") is True
            and terminal.get("open_request_ids") == []
            and terminal.get("all_complete") is True
            and terminal.get("no_post_close_upstream") is True
            and terminal.get("poisoned") is False
            and terminal.get("poison_reasons") == []
            and terminal.get("active_handler_count") == 0
            and not isinstance(terminal.get("active_handler_count"), bool)
            and terminal.get("handlers_quiescent") is True
            and isinstance(gate_crossing, Mapping)
            and gate_crossing.get("response_id") == crossing_response_id
            and gate_crossing.get("completed_tokens") == crossing_tokens
            and gate_crossing.get("sole_inflight") is True
            and gate_crossing.get("release_kind") == expected_crossing_release
            and len(crossing_ledger) == 1
            and isinstance(crossing_gate_call, Mapping)
            and crossing_gate_call.get("response_id") == crossing_response_id
            and crossing_gate_call.get("normalized_usage")
            == crossing_ledger[0].get("usage")
            and crossing_gate_call.get("committed_total") == crossing_tokens
            and crossing_gate_call.get("crossed_cap") is True
            and call_crossing_request_kind == gate_crossing_request_kind
            and crossing_gate_call.get("release_kind")
            == expected_crossing_release
            and crossing_gate_call.get("client_release_complete") is True
            and isinstance(crossing_gate_call.get("appserver_delivery"), Mapping)
            and crossing_gate_call["appserver_delivery"].get("kind")
            == "direct_raw_response"
            and isinstance(crossing_crossbind, Mapping)
            and crossing_crossbind.get("thread_id")
            == crossing_ledger[0].get("thread_id")
            and crossing_crossbind.get("turn_id")
            == crossing_ledger[0].get("turn_id")
            and crossing_crossbind.get("event_sequence")
            == crossing_ledger[0].get("raw_response_notification_sequence")
            and crossing_crossbind.get("normalized_usage")
            == crossing_ledger[0].get("usage")
            and adapter_teardown is not None
            and adapter_teardown.get("immediate") is True
        )
    if measurement_exact:
        natural_exact = (
            drain_complete
            and not active_thread_ids
            and not unresolved_thread_ids
            and not invalid_reasons
            and accounting_complete is True
            and spawn_linkage_complete is True
            and descendant_accounting_complete is True
            and cumulative_projection_complete is True
            and interrupt_requested is False
            and pending_interrupt_response_count == 0
        )
        if not natural_exact and not boundary_exact and not crossing_exact:
            raise BenchmarkToolError("Ultra exactness contradicts lifecycle evidence")
    if boundary_exact and measurement_exact is not True:
        raise BenchmarkToolError("Ultra accepted boundary is not marked exact")
    if provider_usage_reconciliation is not None:
        scoring_totals = provider_usage_reconciliation["provider_usage"]
        scoring_response_count = provider_usage_reconciliation[
            "provider_response_count"
        ]
        scoring_response_ids = provider_usage_reconciliation[
            "provider_response_ids"
        ]
        suppressed_response_count = provider_usage_reconciliation[
            "suppressed_collaboration_wait_response_count"
        ]
        suppressed_response_ids = provider_usage_reconciliation[
            "suppressed_collaboration_wait_response_ids"
        ]
        suppressed_usage = provider_usage_reconciliation[
            "suppressed_collaboration_wait_usage"
        ]
        suppressed_evidence = provider_usage_reconciliation[
            "suppressed_collaboration_wait_evidence"
        ]
        superseded_response_count = provider_usage_reconciliation[
            "superseded_by_collaboration_message_response_count"
        ]
        superseded_response_ids = provider_usage_reconciliation[
            "superseded_by_collaboration_message_response_ids"
        ]
        superseded_usage = provider_usage_reconciliation[
            "superseded_by_collaboration_message_usage"
        ]
        superseded_evidence = provider_usage_reconciliation[
            "superseded_by_collaboration_message_evidence"
        ]
        discarded_response_count = provider_usage_reconciliation[
            "discarded_after_explicit_child_interrupt_response_count"
        ]
        discarded_response_ids = provider_usage_reconciliation[
            "discarded_after_explicit_child_interrupt_response_ids"
        ]
        discarded_usage = provider_usage_reconciliation[
            "discarded_after_explicit_child_interrupt_usage"
        ]
        discarded_evidence = provider_usage_reconciliation[
            "discarded_after_explicit_child_interrupt_evidence"
        ]
    else:
        scoring_totals = totals
        scoring_response_count = response_count
        scoring_response_ids = list(response_ids)
        suppressed_response_count = 0
        suppressed_response_ids = []
        suppressed_usage = {field: 0 for field in field_names}
        suppressed_evidence = []
        superseded_response_count = 0
        superseded_response_ids = []
        superseded_usage = {field: 0 for field in field_names}
        superseded_evidence = []
        discarded_response_count = 0
        discarded_response_ids = []
        discarded_usage = {field: 0 for field in field_names}
        discarded_evidence = []
    return {
        "input_tokens": scoring_totals["input_tokens"],
        "output_tokens": scoring_totals["output_tokens"],
        "cached_input_tokens": scoring_totals["cached_input_tokens"],
        "cache_write_input_tokens": scoring_totals["cache_write_input_tokens"],
        "reasoning_output_tokens": scoring_totals["reasoning_output_tokens"],
        "model_tokens": scoring_totals["total_tokens"],
        "call_count": scoring_response_count,
        "response_count": scoring_response_count,
        "response_ids": list(scoring_response_ids),
        "provider_response_count": scoring_response_count,
        "provider_response_ids": list(scoring_response_ids),
        "provider_usage": dict(scoring_totals),
        "appserver_response_count": response_count,
        "appserver_response_ids": list(response_ids),
        "appserver_response_ledger": response_ledger,
        "appserver_usage": dict(totals),
        "suppressed_collaboration_wait_response_count": (
            suppressed_response_count
        ),
        "suppressed_collaboration_wait_response_ids": list(
            suppressed_response_ids
        ),
        "suppressed_collaboration_wait_usage": dict(suppressed_usage),
        "suppressed_collaboration_wait_evidence": list(suppressed_evidence),
        "superseded_by_collaboration_message_response_count": (
            superseded_response_count
        ),
        "superseded_by_collaboration_message_response_ids": list(
            superseded_response_ids
        ),
        "superseded_by_collaboration_message_usage": dict(superseded_usage),
        "superseded_by_collaboration_message_evidence": list(
            superseded_evidence
        ),
        "discarded_after_explicit_child_interrupt_response_count": (
            discarded_response_count
        ),
        "discarded_after_explicit_child_interrupt_response_ids": list(
            discarded_response_ids
        ),
        "discarded_after_explicit_child_interrupt_usage": dict(discarded_usage),
        "discarded_after_explicit_child_interrupt_evidence": list(
            discarded_evidence
        ),
        "provider_usage_reconciliation": provider_usage_reconciliation,
        "thread_count": thread_count,
        "response_id_deduplicated": True,
        "measurement_source": ULTRA_USAGE_MEASUREMENT_SOURCE,
        "notification": ULTRA_USAGE_NOTIFICATION,
        "usage_scope": ULTRA_USAGE_SCOPE,
        "live_cumulative": True,
        "input_includes_cached": True,
        "notification_sequence": notification_sequence,
        "observed_at_unix_ns": observed_at_unix_ns,
        "root_thread_id": root_thread_id,
        "root_turn_id": root_turn_id,
        "drain_complete": drain_complete,
        "tree_quiescent": drain_complete and not active_thread_ids and not unresolved_thread_ids,
        "measurement_exact": measurement_exact,
        "accounting_projection_schema_version": (
            ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION
        ),
        "fork_policy": {
            field: fork_policy[field]
            for field in fork_policy
            if field
            not in {
                "hook_observed_spawn_call_ids",
                "hook_allowed_spawn_call_ids",
                "hook_blocked_spawn_call_ids",
                "hook_invalid_spawn_call_ids",
                "policy_blocked_spawn_call_ids",
            }
        },
        "hook_observed_spawn_call_ids": fork_policy[
            "hook_observed_spawn_call_ids"
        ],
        "hook_allowed_spawn_call_ids": fork_policy[
            "hook_allowed_spawn_call_ids"
        ],
        "hook_blocked_spawn_call_ids": fork_policy[
            "hook_blocked_spawn_call_ids"
        ],
        "hook_invalid_spawn_call_ids": fork_policy[
            "hook_invalid_spawn_call_ids"
        ],
        "policy_blocked_spawn_call_ids": fork_policy[
            "policy_blocked_spawn_call_ids"
        ],
        "fork_policy_complete": fork_policy["complete"],
        "spawn_linkage_complete": spawn_linkage_complete,
        "descendant_accounting_complete": descendant_accounting_complete,
        "cumulative_projection_complete": cumulative_projection_complete,
        "accounting_complete": accounting_complete,
        "spawn_binding_source": (
            "raw_function_call.call_id=subAgentActivity.id"
        ),
        "raw_spawn_call_ids": sorted(raw_spawn_ids),
        "activity_spawn_call_ids": sorted(activity_spawn_ids),
        "collab_spawn_call_ids": sorted(collab_spawn_ids),
        "resolved_spawn_call_ids": sorted(resolved_spawn_ids),
        "failed_spawn_call_ids": sorted(failed_spawn_ids),
        "unresolved_spawn_call_ids": sorted(unresolved_spawn_ids),
        "unsupported_spawn_call_ids": sorted(unsupported_spawn_ids),
        "inference_child_thread_ids": sorted(inference_child_ids),
        "thread_accounting": [
            dict(projected_threads[thread_id]) for thread_id in sorted(projected_threads)
        ],
        "submission_boundary_exact": boundary_exact,
        "submission_boundary": boundary,
        "first_crossing": dict(first_crossing) if first_crossing is not None else None,
        "stop_reason": value.get("stop_reason"),
        "interrupt_requested": interrupt_requested,
        "pending_interrupt_response_count": pending_interrupt_response_count,
        "active_thread_ids": list(active_thread_ids),
        "unresolved_thread_ids": list(unresolved_thread_ids),
        "invalid_reasons": list(invalid_reasons),
        "provider_token_gate": provider_gate_summary,
        "adapter_teardown": adapter_teardown,
    }


def _submission_stamp(path: Path) -> tuple[int, int] | None:
    try:
        stat = path.stat()
    except FileNotFoundError:
        return None
    return stat.st_mtime_ns, stat.st_size


def _workspace_byte_inventory(root: Path) -> dict[str, tuple[str, str | None]]:
    """Hash one workspace tree without following candidate-created symlinks."""

    root = root.resolve()
    if not root.is_dir():
        raise BenchmarkToolError(f"workspace snapshot source is not a directory: {root}")
    inventory: dict[str, tuple[str, str | None]] = {}
    for current, raw_directories, raw_files in os.walk(root, followlinks=False):
        directory = Path(current)
        directories = sorted(raw_directories)
        files = sorted(raw_files)
        traversed: list[str] = []
        for name in directories:
            path = directory / name
            relative = path.relative_to(root).as_posix()
            metadata = path.lstat()
            if stat.S_ISLNK(metadata.st_mode):
                inventory[relative] = ("symlink", os.readlink(path))
            elif stat.S_ISDIR(metadata.st_mode):
                inventory[relative] = ("directory", None)
                traversed.append(name)
            else:
                raise BenchmarkToolError(
                    f"unsupported workspace entry at submission boundary: {relative}"
                )
        raw_directories[:] = traversed
        for name in files:
            path = directory / name
            relative = path.relative_to(root).as_posix()
            metadata = path.lstat()
            if stat.S_ISLNK(metadata.st_mode):
                inventory[relative] = ("symlink", os.readlink(path))
            elif stat.S_ISREG(metadata.st_mode):
                inventory[relative] = ("file", sha256_file(path))
            else:
                raise BenchmarkToolError(
                    f"unsupported workspace entry at submission boundary: {relative}"
                )
    return inventory


def freeze_stopped_workspace(
    source: Path, destination: Path
) -> dict[str, tuple[str, str | None]]:
    """Copy and byte-verify a stopped agent workspace for hidden validation."""

    if destination.exists():
        raise BenchmarkToolError(f"workspace snapshot already exists: {destination}")
    before = _workspace_byte_inventory(source)
    try:
        shutil.copytree(source, destination, symlinks=True)
        after = _workspace_byte_inventory(source)
        frozen = _workspace_byte_inventory(destination)
    except Exception:
        shutil.rmtree(destination, ignore_errors=True)
        raise
    if before != after or before != frozen:
        shutil.rmtree(destination, ignore_errors=True)
        raise BenchmarkToolError(
            "workspace changed while the final Ultra submission snapshot was frozen"
        )
    return frozen


def _read_regular_bytes(path: Path, label: str) -> bytes:
    try:
        metadata = path.lstat()
    except OSError as error:
        raise BenchmarkToolError(f"cannot read {label}: {error}") from error
    if stat.S_ISLNK(metadata.st_mode) or not stat.S_ISREG(metadata.st_mode):
        raise BenchmarkToolError(f"{label} must be a regular non-symlink file")
    try:
        return path.read_bytes()
    except OSError as error:
        raise BenchmarkToolError(f"cannot read {label}: {error}") from error


def _safe_candidate_relative(value: Any) -> str:
    if not isinstance(value, str) or not value or len(value) > 512:
        raise BenchmarkToolError("submission request candidate_path is invalid")
    if "\x00" in value or "\\" in value:
        raise BenchmarkToolError("submission request candidate_path is unsafe")
    candidate = PurePosixPath(value)
    if (
        candidate.is_absolute()
        or value != candidate.as_posix()
        or any(part in ("", ".", "..") for part in candidate.parts)
        or candidate.as_posix() != "Candidate.lean"
    ):
        raise BenchmarkToolError("submission request candidate_path escapes its contract")
    return candidate.as_posix()


def _validator_contract(
    args: argparse.Namespace,
    *,
    compile_command: Sequence[str],
    audit_command: Sequence[str] | None,
) -> dict[str, Any]:
    return {
        "condition": args.condition,
        "submission_relative": args.submission_relative,
        "canonical_relative": args.canonical_relative,
        "target_theorem": args.target_theorem,
        "compile_command": list(compile_command),
        "audit_command": list(audit_command) if audit_command is not None else None,
        "controlled_manifest_sha256": sha256_file(args.controlled_manifest),
        "reject_workspace_local_module_imports": bool(
            args.reject_workspace_local_module_imports
        ),
    }


def _validator_contract_sha256(
    args: argparse.Namespace,
    *,
    compile_command: Sequence[str],
    audit_command: Sequence[str] | None,
) -> str:
    contract = _validator_contract(
        args,
        compile_command=compile_command,
        audit_command=audit_command,
    )
    return hashlib.sha256(
        json.dumps(
            contract, sort_keys=True, separators=(",", ":"), ensure_ascii=False
        ).encode("utf-8")
    ).hexdigest()


def _make_submission_challenge(
    args: argparse.Namespace,
    *,
    run_id: str,
    compile_command: Sequence[str],
    audit_command: Sequence[str] | None,
) -> dict[str, Any]:
    validator_contract_sha256 = _validator_contract_sha256(
        args,
        compile_command=compile_command,
        audit_command=audit_command,
    )
    return authenticated_record(
        {
            "schema_version": SUBMISSION_BARRIER_SCHEMA_VERSION,
            "kind": "highambench_submission_challenge",
            "run_id": run_id,
            "attempt_nonce": uuid.uuid4().hex,
            "validator_contract_sha256": validator_contract_sha256,
            **nested_submission_exec_yield_record(),
            "published_at_unix_ns": time.time_ns(),
            "published_at_monotonic_ns": time.monotonic_ns(),
        },
        "challenge_sha256",
    )


def _authenticate_validation_result(
    result: Mapping[str, Any],
    *,
    run_id: str,
    task_id: str,
    candidate_sha256: str,
    target_theorem: str,
    controlled_manifest_sha256: str,
    validator_contract_sha256: str,
    submission_request_sha256: str | None,
    submission_sequence: int | None,
) -> dict[str, Any]:
    """Bind one accepted or rejected validation to the exact candidate bytes."""

    if not re.fullmatch(r"[0-9a-f]{64}", candidate_sha256):
        raise BenchmarkToolError("validation authentication has an invalid candidate hash")
    for label, digest in (
        ("controlled manifest", controlled_manifest_sha256),
        ("validator contract", validator_contract_sha256),
    ):
        if not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise BenchmarkToolError(
                f"validation authentication has an invalid {label} hash"
            )
    if submission_request_sha256 is None:
        if submission_sequence is not None:
            raise BenchmarkToolError(
                "non-Ultra validation authentication has a submission sequence"
            )
    elif (
        not re.fullmatch(r"[0-9a-f]{64}", submission_request_sha256)
        or not isinstance(submission_sequence, int)
        or isinstance(submission_sequence, bool)
        or submission_sequence <= 0
    ):
        raise BenchmarkToolError(
            "Ultra validation authentication has an invalid request binding"
        )
    authenticated = dict(result)
    authenticated.pop("record_sha256", None)
    authenticated["authentication"] = {
        "schema_version": 1,
        "run_id": run_id,
        "task_id": task_id,
        "candidate_sha256": candidate_sha256,
        "target_theorem": target_theorem,
        "controlled_manifest_sha256": controlled_manifest_sha256,
        "validator_contract_sha256": validator_contract_sha256,
        "submission_request_sha256": submission_request_sha256,
        "submission_sequence": submission_sequence,
    }
    payload = json.dumps(
        authenticated, sort_keys=True, separators=(",", ":"), ensure_ascii=False
    ).encode("utf-8")
    authenticated["record_sha256"] = hashlib.sha256(payload).hexdigest()
    return authenticated


def _read_submission_call(
    usage_path: Path,
    *,
    expected_sequence: int,
    prompt_released_monotonic_ns: int,
) -> tuple[dict[str, Any], float]:
    paths = submission_barrier_paths(usage_path, expected_sequence)
    try:
        challenge = verify_authenticated_record(
            json.loads(_read_regular_bytes(paths["challenge"], "submission challenge")),
            "challenge_sha256",
        )
        call = verify_authenticated_record(
            json.loads(_read_regular_bytes(paths["call"], "submission call")),
            "call_sha256",
        )
    except (RuntimeError, json.JSONDecodeError) as error:
        raise BenchmarkToolError(str(error)) from error
    if (
        challenge.get("schema_version") != SUBMISSION_BARRIER_SCHEMA_VERSION
        or challenge.get("kind") != "highambench_submission_challenge"
        or any(
            challenge.get(field) != expected
            for field, expected in nested_submission_exec_yield_record().items()
        )
        or call.get("schema_version") != SUBMISSION_BARRIER_SCHEMA_VERSION
        or call.get("kind") != "highambench_submission_call"
        or call.get("sequence") != expected_sequence
        or call.get("challenge_sha256") != challenge.get("challenge_sha256")
    ):
        raise BenchmarkToolError("submission call schema/challenge mismatch")
    for field in (
        "attempt_nonce",
        "run_id",
        "validator_contract_sha256",
        *nested_submission_exec_yield_record(),
    ):
        if call.get(field) != challenge.get(field):
            raise BenchmarkToolError(f"submission call {field} mismatch")
    candidate_path = _safe_candidate_relative(call.get("candidate_path"))
    if candidate_path != "Candidate.lean":
        raise BenchmarkToolError("submission call candidate mismatch")
    _validate_submission_wire(
        call,
        candidate_path=candidate_path,
        label="submission call",
    )
    captured = _positive_int(
        call.get("captured_at_monotonic_ns"), "captured_at_monotonic_ns"
    )
    elapsed = (captured - prompt_released_monotonic_ns) / 1_000_000_000
    if elapsed < 0:
        raise BenchmarkToolError("submission call predates prompt release")
    return call, elapsed


def _read_submission_request(
    usage_path: Path,
    *,
    expected_sequence: int,
    prompt_released_monotonic_ns: int,
    usage: Mapping[str, Any] | None,
) -> tuple[dict[str, Any], bytes, Path]:
    paths = submission_barrier_paths(usage_path, expected_sequence)
    request_path = paths["request"]
    try:
        challenge = verify_authenticated_record(
            json.loads(_read_regular_bytes(paths["challenge"], "submission challenge")),
            "challenge_sha256",
        )
        call = verify_authenticated_record(
            json.loads(_read_regular_bytes(paths["call"], "submission call")),
            "call_sha256",
        )
    except (RuntimeError, json.JSONDecodeError) as error:
        raise BenchmarkToolError(str(error)) from error
    try:
        raw = json.loads(_read_regular_bytes(request_path, "submission request"))
    except json.JSONDecodeError as error:
        raise BenchmarkToolError(f"submission request is malformed JSON: {error}") from error
    try:
        request = verify_authenticated_record(raw, "request_sha256")
    except RuntimeError as error:
        raise BenchmarkToolError(str(error)) from error
    if (
        request.get("schema_version") != SUBMISSION_BARRIER_SCHEMA_VERSION
        or request.get("kind") != "highambench_submission_request"
        or request.get("sequence") != expected_sequence
    ):
        raise BenchmarkToolError("submission request schema or sequence mismatch")
    if (
        challenge.get("schema_version") != SUBMISSION_BARRIER_SCHEMA_VERSION
        or challenge.get("kind") != "highambench_submission_challenge"
        or any(
            challenge.get(field) != expected
            for field, expected in nested_submission_exec_yield_record().items()
        )
        or call.get("schema_version") != SUBMISSION_BARRIER_SCHEMA_VERSION
        or call.get("kind") != "highambench_submission_call"
        or call.get("sequence") != expected_sequence
        or request.get("challenge_sha256") != challenge.get("challenge_sha256")
        or call.get("challenge_sha256") != challenge.get("challenge_sha256")
        or request.get("call_sha256") != call.get("call_sha256")
    ):
        raise BenchmarkToolError("submission request does not bind its challenge/call")
    for field in (
        "attempt_nonce",
        "run_id",
        "validator_contract_sha256",
        *nested_submission_exec_yield_record(),
    ):
        if request.get(field) != challenge.get(field) or call.get(field) != challenge.get(field):
            raise BenchmarkToolError(f"submission barrier {field} binding mismatch")
    for field in ("call_id", "thread_id", "turn_id", "response_id"):
        if not isinstance(request.get(field), str) or not request[field]:
            raise BenchmarkToolError(f"submission request lacks {field}")
    jsonrpc_id = request.get("jsonrpc_request_id")
    if not isinstance(jsonrpc_id, (str, int)) or isinstance(jsonrpc_id, bool):
        raise BenchmarkToolError("submission request has an invalid JSON-RPC id")
    candidate_path = _safe_candidate_relative(request.get("candidate_path"))
    _validate_submission_wire(
        request,
        candidate_path=candidate_path,
        label="submission request",
    )
    if request.get("snapshot_name") != paths["snapshot"].name:
        raise BenchmarkToolError("submission request names the wrong protected snapshot")
    for field in (
        "jsonrpc_request_id",
        "call_id",
        "inner_dynamic_call_id",
        "inner_dynamic_tool_name",
        "inner_dynamic_arguments",
        "submission_transport",
        "outer_raw_item_id",
        "outer_raw_item_type",
        "outer_exec_name",
        "outer_exec_call_id",
        "outer_exec_program",
        "outer_exec_program_bytes",
        "outer_exec_program_sha256",
        *nested_submission_exec_yield_record(),
        "outer_raw_item_observed_at_monotonic_ns",
        "inner_dynamic_item_started_at_monotonic_ns",
        "outer_raw_item_observed_before_inner_dynamic_call",
        "thread_id",
        "turn_id",
        "candidate_path",
        "candidate_sha256",
        "candidate_size_bytes",
        "snapshot_name",
        "captured_at_unix_ns",
        "captured_at_monotonic_ns",
    ):
        if request.get(field) != call.get(field):
            raise BenchmarkToolError(f"submission request/call {field} mismatch")
    candidate_sha = request.get("candidate_sha256")
    if not isinstance(candidate_sha, str) or not re.fullmatch(r"[0-9a-f]{64}", candidate_sha):
        raise BenchmarkToolError("submission request candidate digest is invalid")
    candidate_size = _nonnegative_int(
        request.get("candidate_size_bytes"), "candidate_size_bytes"
    )
    published_ns = _positive_int(
        request.get("request_published_at_monotonic_ns"),
        "request_published_at_monotonic_ns",
    )
    if published_ns < prompt_released_monotonic_ns or published_ns > time.monotonic_ns():
        raise BenchmarkToolError("submission request has a stale monotonic timestamp")
    for flag in (
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
    ):
        if request.get(flag) is not True:
            raise BenchmarkToolError(f"submission request lacks {flag} evidence")
    _validate_submission_event_order(
        request,
        label="submission request",
        derive_from_timestamps=True,
    )
    captured_ns = _positive_int(
        request.get("captured_at_monotonic_ns"),
        "captured_at_monotonic_ns",
    )
    response_ns = _positive_int(
        request.get("raw_response_observed_at_monotonic_ns"),
        "raw_response_observed_at_monotonic_ns",
    )
    if min(captured_ns, response_ns) < prompt_released_monotonic_ns or max(
        captured_ns, response_ns
    ) > published_ns:
        raise BenchmarkToolError("submission events fall outside the released boundary")
    snapshot = _read_regular_bytes(paths["snapshot"], "submission snapshot")
    if len(snapshot) != candidate_size or hashlib.sha256(snapshot).hexdigest() != candidate_sha:
        raise BenchmarkToolError("submission snapshot does not match its request")
    boundary_usage = request.get("boundary_usage")
    if not isinstance(boundary_usage, Mapping) or usage is None:
        raise BenchmarkToolError("submission request lacks a live exact usage boundary")
    expected_usage = {
        "input_tokens": usage["input_tokens"],
        "cached_input_tokens": usage["cached_input_tokens"],
        "cache_write_input_tokens": usage.get("cache_write_input_tokens", 0),
        "output_tokens": usage["output_tokens"],
        "reasoning_output_tokens": usage.get("reasoning_output_tokens", 0),
        "total_tokens": usage["model_tokens"],
        "response_count": usage["response_count"],
        "thread_count": usage["thread_count"],
        "notification_sequence": usage["notification_sequence"],
        "response_ids": usage["response_ids"],
        "appserver_response_count": usage["appserver_response_count"],
        "appserver_response_ids": usage["appserver_response_ids"],
    }
    if dict(boundary_usage) != expected_usage:
        raise BenchmarkToolError("submission request usage ledger does not match live usage")
    if (
        request.get("thread_id") != usage["root_thread_id"]
        or request.get("response_id") not in usage["appserver_response_ids"]
        or request.get("raw_response_notification_sequence")
        != usage["notification_sequence"]
    ):
        raise BenchmarkToolError("submission request does not bind the proof response")
    request["candidate_path"] = candidate_path
    return request, snapshot, paths["snapshot"]


def _write_submission_ack(
    usage_path: Path,
    request: Mapping[str, Any],
    *,
    decision: str,
    note: str,
    validator_elapsed_seconds: float,
) -> dict[str, Any]:
    if decision not in ("accept", "reject"):
        raise BenchmarkToolError("invalid submission ack decision")
    encoded_note = note.encode("utf-8", errors="replace")[:MAX_REJECTION_NOTE_BYTES]
    bounded_note = encoded_note.decode("utf-8", errors="ignore")
    ack = authenticated_record(
        {
            "schema_version": SUBMISSION_BARRIER_SCHEMA_VERSION,
            "kind": "highambench_submission_ack",
            "sequence": request["sequence"],
            "request_sha256": request["request_sha256"],
            "candidate_sha256": request["candidate_sha256"],
            "decision": decision,
            "note": bounded_note,
            "validator_accepted_at_unix_ns": (
                time.time_ns() if decision == "accept" else None
            ),
            "validator_accepted_elapsed_seconds": (
                validator_elapsed_seconds if decision == "accept" else None
            ),
            "published_at_unix_ns": time.time_ns(),
            "published_at_monotonic_ns": time.monotonic_ns(),
        },
        "ack_sha256",
    )
    ack_path = submission_barrier_paths(usage_path)["ack"]
    if ack_path.exists() or ack_path.is_symlink():
        raise BenchmarkToolError("stale or duplicate submission ack exists")
    temporary = Path(str(ack_path) + ".tmp")
    if temporary.exists() or temporary.is_symlink():
        raise BenchmarkToolError("stale submission ack temporary exists")
    payload = (json.dumps(ack, sort_keys=True) + "\n").encode("utf-8")
    descriptor = os.open(
        temporary, os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC, 0o600
    )
    try:
        offset = 0
        while offset < len(payload):
            offset += os.write(descriptor, payload[offset:])
        os.fsync(descriptor)
    finally:
        os.close(descriptor)
    os.replace(temporary, ack_path)
    return ack


def _materialize_barrier_workspace(
    source: Path,
    destination: Path,
    request: Mapping[str, Any],
    snapshot: bytes,
    submission_relative: str,
) -> tuple[Path, dict[str, tuple[str, str | None]]]:
    freeze_stopped_workspace(source, destination)
    submission = resolve_below(destination, submission_relative)
    try:
        submission.lstat()
    except FileNotFoundError:
        pass
    else:
        raise BenchmarkToolError("Submission.lean appeared before runner acceptance")
    submission.parent.mkdir(parents=True, exist_ok=True)
    submission.write_bytes(snapshot)
    return submission, _workspace_byte_inventory(destination)


def _bind_final_submission_boundary(
    usage: Mapping[str, Any],
    request: Mapping[str, Any],
    ack: Mapping[str, Any],
) -> None:
    boundary = usage.get("submission_boundary")
    if usage.get("submission_boundary_exact") is not True or not isinstance(
        boundary, Mapping
    ):
        raise BenchmarkToolError("adapter did not publish an exact accepted boundary")
    bindings = {
        "sequence": request["sequence"],
        "challenge_sha256": request["challenge_sha256"],
        "call_sha256": request["call_sha256"],
        "attempt_nonce": request["attempt_nonce"],
        "run_id": request["run_id"],
        "validator_contract_sha256": request["validator_contract_sha256"],
        "request_sha256": request["request_sha256"],
        "ack_sha256": ack["ack_sha256"],
        "jsonrpc_request_id": request["jsonrpc_request_id"],
        "call_id": request["call_id"],
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
        "outer_raw_item_observed_before_inner_dynamic_call": request[
            "outer_raw_item_observed_before_inner_dynamic_call"
        ],
        "inner_dynamic_call_id": request["inner_dynamic_call_id"],
        "inner_dynamic_tool_name": request["inner_dynamic_tool_name"],
        "inner_dynamic_arguments": request["inner_dynamic_arguments"],
        "thread_id": request["thread_id"],
        "turn_id": request["turn_id"],
        "response_id": request["response_id"],
        "raw_response_notification_sequence": request[
            "raw_response_notification_sequence"
        ],
        "submission_event_order": request["submission_event_order"],
        "dynamic_call_observed_before_raw_response_completed": request[
            "dynamic_call_observed_before_raw_response_completed"
        ],
        "raw_response_completed_before_dynamic_call_observed": request[
            "raw_response_completed_before_dynamic_call_observed"
        ],
        "candidate_path": request["candidate_path"],
        "candidate_sha256": request["candidate_sha256"],
        "candidate_size_bytes": request["candidate_size_bytes"],
    }
    if any(boundary.get(key) != value for key, value in bindings.items()):
        raise BenchmarkToolError("final submission boundary does not bind its request/ack")
    boundary_usage = request["boundary_usage"]
    final_usage = {
        "input_tokens": usage["input_tokens"],
        "cached_input_tokens": usage["cached_input_tokens"],
        "cache_write_input_tokens": usage.get("cache_write_input_tokens", 0),
        "output_tokens": usage["output_tokens"],
        "reasoning_output_tokens": usage.get("reasoning_output_tokens", 0),
        "total_tokens": usage["model_tokens"],
        "response_count": usage["response_count"],
        "thread_count": usage["thread_count"],
        "notification_sequence": usage["notification_sequence"],
        "response_ids": usage["response_ids"],
        "appserver_response_count": usage["appserver_response_count"],
        "appserver_response_ids": usage["appserver_response_ids"],
    }
    if final_usage != dict(boundary_usage):
        raise BenchmarkToolError("final token ledger changed after proof submission")


def _seal_accepted_barrier_artifacts(
    usage_path: Path,
    request: Mapping[str, Any],
    ack: Mapping[str, Any],
) -> dict[str, Any]:
    """Rebind, make read-only, and retain the accepted audit evidence."""

    paths = submission_barrier_paths(usage_path, int(request["sequence"]))
    json_artifacts = (
        ("challenge", "challenge_sha256", request["challenge_sha256"]),
        ("call", "call_sha256", request["call_sha256"]),
        ("request", "request_sha256", request["request_sha256"]),
        ("ack", "ack_sha256", ack["ack_sha256"]),
    )
    result: dict[str, Any] = {}
    for name, hash_field, expected_hash in json_artifacts:
        try:
            record = verify_authenticated_record(
                json.loads(_read_regular_bytes(paths[name], f"accepted {name}")),
                hash_field,
            )
        except (RuntimeError, json.JSONDecodeError) as error:
            raise BenchmarkToolError(f"accepted {name} artifact is invalid: {error}") from error
        if record.get(hash_field) != expected_hash:
            raise BenchmarkToolError(f"accepted {name} artifact hash binding mismatch")
        result[name] = {
            "path": str(paths[name]),
            "record_sha256": expected_hash,
            "file_sha256": sha256_file(paths[name]),
        }
    snapshot = _read_regular_bytes(paths["snapshot"], "accepted snapshot")
    if (
        len(snapshot) != request["candidate_size_bytes"]
        or hashlib.sha256(snapshot).hexdigest() != request["candidate_sha256"]
    ):
        raise BenchmarkToolError("accepted snapshot artifact hash binding mismatch")
    result["snapshot"] = {
        "path": str(paths["snapshot"]),
        "file_sha256": request["candidate_sha256"],
        "size_bytes": request["candidate_size_bytes"],
    }
    for name in ("challenge", "call", "request", "ack", "snapshot"):
        os.chmod(paths[name], 0o444, follow_symlinks=False)
    return result


def _limit_observation(usage: Mapping[str, Any]) -> int:
    crossing = usage.get("first_crossing")
    if isinstance(crossing, Mapping):
        tokens = crossing.get("tokens")
        if isinstance(tokens, int) and not isinstance(tokens, bool) and tokens >= 0:
            return tokens
    return int(usage["model_tokens"])


def trusted_usage_output(args: argparse.Namespace, logs_dir: Path) -> Path:
    """Resolve the adapter-owned usage file below the trusted logs directory."""

    raw = getattr(args, "usage_output", None)
    if not isinstance(raw, Path):
        raise BenchmarkToolError("--usage-output is required")
    if not raw.is_absolute():
        raise BenchmarkToolError("--usage-output must be an absolute path")
    resolved = raw.resolve()
    try:
        relative = resolved.relative_to(logs_dir)
    except ValueError as error:
        raise BenchmarkToolError(
            "--usage-output must resolve below --logs-dir"
        ) from error
    if relative == Path("."):
        raise BenchmarkToolError("--usage-output must name a file below --logs-dir")
    return resolved


def provider_gate_paths(usage_output: Path) -> dict[str, Path]:
    """Derive the live and final gate artifacts from one trusted usage path."""

    try:
        paths = {
            "live": core_provider_gate_live_path(usage_output).resolve(),
            "final": core_provider_gate_artifact_path(usage_output).resolve(),
        }
    except RuntimeError as error:
        raise BenchmarkToolError(f"cannot derive provider-gate artifacts: {error}") from error
    if (
        not paths["live"].name.endswith(PROVIDER_GATE_LIVE_SUFFIX)
        or not paths["final"].name.endswith(PROVIDER_GATE_ARTIFACT_SUFFIX)
        or paths["live"].parent != usage_output.parent.resolve()
        or paths["final"].parent != usage_output.parent.resolve()
    ):
        raise BenchmarkToolError("provider-gate path API changed")
    return paths


def _provider_gate_file_status(path: Path | None) -> dict[str, Any] | None:
    if path is None:
        return None
    result: dict[str, Any] = {
        "path": str(path),
        "absolute": path.is_absolute(),
        "exists": False,
        "regular_non_symlink": False,
        "mode": None,
        "size_bytes": None,
        "file_sha256": None,
    }
    try:
        metadata = path.lstat()
    except FileNotFoundError:
        return result
    except OSError as error:
        result["inspection_error"] = str(error)
        return result
    result["exists"] = True
    result["mode"] = f"{stat.S_IMODE(metadata.st_mode):04o}"
    result["size_bytes"] = metadata.st_size
    regular = stat.S_ISREG(metadata.st_mode) and not stat.S_ISLNK(metadata.st_mode)
    result["regular_non_symlink"] = regular
    if regular:
        try:
            result["file_sha256"] = sha256_file(path)
        except OSError as error:
            result["inspection_error"] = str(error)
    return result


def provider_gate_run_record(
    *,
    required: bool,
    status: str,
    paths: Mapping[str, Path] | None,
    source_sha256: str | None,
    catalog: Mapping[str, Any] | None,
    transport_provenance: Mapping[str, Any] | None,
    live_crossing: Mapping[str, Any] | None,
    final: Mapping[str, Any] | None,
    error: str | None,
) -> dict[str, Any]:
    """Preserve both provisional and sealed evidence without conflating them."""

    live_path = paths.get("live") if paths is not None else None
    final_path = paths.get("final") if paths is not None else None
    return {
        "required": required,
        "status": status,
        "protocol": PROVIDER_GATE_PROTOCOL if required else None,
        "cleanup_grace_seconds": (
            PROVIDER_GATE_CLEANUP_GRACE_SECONDS if required else None
        ),
        "implementation_source_sha256": source_sha256,
        "model_catalog": (
            {
                "catalog_sha256": catalog.get("catalog_sha256"),
                "entry_sha256": catalog.get("entry_sha256"),
                "response_bound": catalog.get("response_bound"),
            }
            if catalog is not None
            else None
        ),
        "transport_provenance": (
            dict(transport_provenance)
            if transport_provenance is not None
            else None
        ),
        "live": {
            "scoreable": False,
            "file": _provider_gate_file_status(live_path),
            "authenticated_crossing": (
                dict(live_crossing) if live_crossing is not None else None
            ),
        },
        "final": {
            "scoreable": bool(final is not None and final.get("authenticated") is True),
            "file": _provider_gate_file_status(final_path),
            "authentication": dict(final) if final is not None else None,
        },
        "error": error,
    }


def _provider_gate_sha256(value: Any, field: str) -> str:
    if (
        not isinstance(value, str)
        or re.fullmatch(r"[0-9a-f]{64}", value) is None
    ):
        raise BenchmarkToolError(f"provider gate {field} is not a SHA-256 digest")
    return value


def _validate_provider_transport_dependency(
    value: Any,
    *,
    field: str,
) -> dict[str, Any]:
    dependency = _provider_gate_exact_keys(
        value,
        PROVIDER_TRANSPORT_DEPENDENCY_KEYS,
        f"transport.{field}",
    )
    logical = dependency["logical_path"]
    resolved = dependency["resolved_path"]
    symlink_target = dependency["symlink_target"]
    if not isinstance(logical, str) or not os.path.isabs(logical):
        raise BenchmarkToolError(
            f"provider gate transport.{field}.logical_path is not absolute"
        )
    if (
        not isinstance(resolved, str)
        or not os.path.isabs(resolved)
        or resolved.endswith(" (deleted)")
    ):
        raise BenchmarkToolError(
            f"provider gate transport.{field}.resolved_path is unstable"
        )
    if symlink_target is not None and (
        not isinstance(symlink_target, str) or not symlink_target
    ):
        raise BenchmarkToolError(
            f"provider gate transport.{field}.symlink_target is malformed"
        )
    _provider_gate_sha256(
        dependency["sha256"], f"transport.{field}.sha256"
    )
    _positive_int(dependency["bytes"], f"transport.{field}.bytes")
    mode = dependency["mode"]
    if (
        not isinstance(mode, str)
        or re.fullmatch(r"0[0-7]{3}", mode) is None
    ):
        raise BenchmarkToolError(
            f"provider gate transport.{field}.mode is not four-digit octal"
        )
    return dependency


def _validate_provider_transport_provenance(
    value: Any,
    *,
    field: str,
    expected: Mapping[str, Any] | None = None,
) -> dict[str, Any]:
    """Validate the frozen production transport contract independently."""

    runner_and_core_keysets = (
        (
            PROVIDER_TRANSPORT_PROVENANCE_KEYS,
            CORE_PROVIDER_TRANSPORT_PROVENANCE_KEYS,
        ),
        (
            PROVIDER_TRANSPORT_DEPENDENCY_KEYS,
            CORE_PROVIDER_TRANSPORT_DEPENDENCY_KEYS,
        ),
        (PROVIDER_TRANSPORT_PYTHON_KEYS, CORE_PROVIDER_TRANSPORT_PYTHON_KEYS),
        (PROVIDER_TRANSPORT_OPENSSL_KEYS, CORE_PROVIDER_TRANSPORT_OPENSSL_KEYS),
        (PROVIDER_TRANSPORT_TLS_KEYS, CORE_PROVIDER_TRANSPORT_TLS_KEYS),
        (PROVIDER_TRANSPORT_RESOLVER_KEYS, CORE_PROVIDER_TRANSPORT_RESOLVER_KEYS),
        (
            PROVIDER_TRANSPORT_ENVIRONMENT_KEYS,
            CORE_PROVIDER_TRANSPORT_ENVIRONMENT_KEYS,
        ),
    )
    if any(set(runner) != set(core) for runner, core in runner_and_core_keysets):
        raise BenchmarkToolError("runner/provider transport static schemas disagree")
    provenance = _provider_gate_exact_keys(
        value,
        PROVIDER_TRANSPORT_PROVENANCE_KEYS,
        f"transport provenance {field}",
    )
    if (
        type(provenance["schema_version"]) is not int
        or provenance["schema_version"] != PROVIDER_TRANSPORT_SCHEMA_VERSION
        or provenance["kind"] != PROVIDER_TRANSPORT_KIND
        or provenance["connection_factory_mode"]
        != PROVIDER_CONNECTION_FACTORY_MODE
    ):
        raise BenchmarkToolError(
            f"provider gate {field} is not the production transport protocol"
        )

    python_record = _provider_gate_exact_keys(
        provenance["python"],
        PROVIDER_TRANSPORT_PYTHON_KEYS,
        f"transport provenance {field}.python",
    )
    executable = python_record["executable"]
    python_version = python_record["version"]
    if (
        executable != "/usr/bin/python3.10"
        or not isinstance(python_version, str)
        or re.fullmatch(r"3\.10\.\d+", python_version) is None
    ):
        raise BenchmarkToolError(
            f"provider gate {field} used another Python interpreter"
        )
    if (
        python_record["implementation"] != "cpython"
        or python_record["socket_implementation"] != "built-in"
    ):
        raise BenchmarkToolError(
            f"provider gate {field} has the wrong Python implementation"
        )
    python_dependencies: dict[str, dict[str, Any]] = {}
    for name in (
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
        python_dependencies[name] = _validate_provider_transport_dependency(
            python_record[name],
            field=f"{field}.python.{name}",
        )
    if python_dependencies["binary"]["logical_path"] != executable:
        raise BenchmarkToolError(
            f"provider gate {field} Python binary descriptor is unbound"
        )

    openssl = _provider_gate_exact_keys(
        provenance["openssl"],
        PROVIDER_TRANSPORT_OPENSSL_KEYS,
        f"transport provenance {field}.openssl",
    )
    if not isinstance(openssl["version"], str) or not openssl["version"]:
        raise BenchmarkToolError(
            f"provider gate {field} OpenSSL version is malformed"
        )
    _positive_int(
        openssl["version_number"],
        f"transport provenance {field}.openssl.version_number",
    )
    openssl_dependencies = {
        name: _validate_provider_transport_dependency(
            openssl[name], field=f"{field}.openssl.{name}"
        )
        for name in ("libssl", "libcrypto", "config")
    }
    if (
        openssl_dependencies["config"]["logical_path"]
        != PROVIDER_OPENSSL_CONFIG_PATH
        or not Path(openssl_dependencies["libssl"]["resolved_path"]).name.startswith(
            "libssl.so"
        )
        or not Path(
            openssl_dependencies["libcrypto"]["resolved_path"]
        ).name.startswith("libcrypto.so")
    ):
        raise BenchmarkToolError(
            f"provider gate {field} OpenSSL dependencies changed class"
        )

    tls = _provider_gate_exact_keys(
        provenance["tls"],
        PROVIDER_TRANSPORT_TLS_KEYS,
        f"transport provenance {field}.tls",
    )
    expected_tls = {
        "protocol": "PROTOCOL_TLS_CLIENT",
        "protocol_value": 16,
        "server_hostname": "chatgpt.com",
        "server_port": 443,
        "certificate_source_mode": PROVIDER_CERTIFICATE_SOURCE_MODE,
        "default_capath_used": False,
        "verify_mode": "CERT_REQUIRED",
        "verify_mode_value": 2,
        "check_hostname": True,
        "minimum_version": "TLSv1_2",
        "minimum_version_value": 771,
        "maximum_version": "MAXIMUM_SUPPORTED",
        "maximum_version_value": -1,
        "alpn_protocols": PROVIDER_TLS_ALPN_PROTOCOLS,
        "keylog_enabled": False,
    }
    if (
        any(
            type(tls[name]) is not int
            for name in (
                "protocol_value",
                "server_port",
                "verify_mode_value",
                "minimum_version_value",
                "maximum_version_value",
            )
        )
        or tls["default_capath_used"] is not False
        or tls["check_hostname"] is not True
        or tls["keylog_enabled"] is not False
        or any(
            tls[name] != expected_value
            for name, expected_value in expected_tls.items()
        )
    ):
        raise BenchmarkToolError(
            f"provider gate {field} TLS policy changed"
        )
    ca = _validate_provider_transport_dependency(
        tls["certificate_source"],
        field=f"{field}.tls.certificate_source",
    )
    if (
        ca["logical_path"] != PROVIDER_CA_BUNDLE_PATH
        or ca["symlink_target"] is not None
    ):
        raise BenchmarkToolError(
            f"provider gate {field} CA bundle is not the fixed nofollow file"
        )
    _positive_int(
        tls["certificate_authority_count"],
        f"transport provenance {field}.tls.certificate_authority_count",
    )
    for name in ("context_options", "verify_flags", "security_level"):
        _nonnegative_int(
            tls[name], f"transport provenance {field}.tls.{name}"
        )
    _provider_gate_sha256(
        tls["cipher_names_sha256"],
        f"transport provenance {field}.tls.cipher_names_sha256",
    )

    resolver = _provider_gate_exact_keys(
        provenance["resolver"],
        PROVIDER_TRANSPORT_RESOLVER_KEYS,
        f"transport provenance {field}.resolver",
    )
    expected_resolver = {
        "policy": PROVIDER_RESOLVER_POLICY,
        "hostname": "chatgpt.com",
        "resolved_addresses_frozen": False,
        "variability_classification": (
            PROVIDER_RESOLVER_VARIABILITY_CLASSIFICATION
        ),
    }
    if any(
        resolver[name] != expected_value
        for name, expected_value in expected_resolver.items()
    ) or resolver["resolved_addresses_frozen"] is not False:
        raise BenchmarkToolError(
            f"provider gate {field} resolver policy changed"
        )
    resolver_dependencies = {
        name: _validate_provider_transport_dependency(
            resolver[name], field=f"{field}.resolver.{name}"
        )
        for name in (
            "resolv_conf",
            "nsswitch_conf",
            "hosts_file",
            "gai_conf",
            "libc",
            "libnss_dns",
            "libnss_files",
        )
    }
    expected_resolver_paths = {
        "resolv_conf": PROVIDER_RESOLV_CONF_PATH,
        "nsswitch_conf": PROVIDER_NSSWITCH_PATH,
        "hosts_file": PROVIDER_HOSTS_PATH,
        "gai_conf": PROVIDER_GAI_CONF_PATH,
    }
    if any(
        resolver_dependencies[name]["logical_path"] != expected_path
        for name, expected_path in expected_resolver_paths.items()
    ) or not all(
        Path(resolver_dependencies[name]["resolved_path"]).name.startswith(prefix)
        for name, prefix in (
            ("libc", "libc.so"),
            ("libnss_dns", "libnss_dns.so"),
            ("libnss_files", "libnss_files.so"),
        )
    ):
        raise BenchmarkToolError(
            f"provider gate {field} resolver dependencies changed class"
        )

    environment = _provider_gate_exact_keys(
        provenance["environment"],
        PROVIDER_TRANSPORT_ENVIRONMENT_KEYS,
        f"transport provenance {field}.environment",
    )
    required_absent = list(PROVIDER_TRANSPORT_ENV_REQUIRED_ABSENT)
    if (
        environment["required_absent"] != required_absent
        or environment["observed_absent"] != required_absent
        or environment["proxy_mode"] != PROVIDER_PROXY_MODE
    ):
        raise BenchmarkToolError(
            f"provider gate {field} transport environment changed"
        )
    if expected is not None and not _provider_gate_same_json(
        provenance, dict(expected)
    ):
        raise BenchmarkToolError(
            f"provider gate {field} transport provenance changed after prelaunch"
        )
    return provenance


def _provider_gate_exact_keys(
    value: Any, expected: set[str], field: str
) -> dict[str, Any]:
    if not isinstance(value, Mapping) or set(value) != expected:
        raise BenchmarkToolError(
            f"provider gate {field} has a missing or extra field"
        )
    return dict(value)


def _provider_gate_same_json(left: Any, right: Any) -> bool:
    """Compare parsed JSON without Python's bool/int equality aliasing."""

    return json.dumps(
        left,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    ) == json.dumps(
        right,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
    )


def _provider_gate_string(
    value: Any, field: str, *, nullable: bool = False
) -> str | None:
    if value is None and nullable:
        return None
    if not isinstance(value, str) or not value or "\x00" in value:
        raise BenchmarkToolError(f"provider gate {field} must be a nonempty string")
    return value


def _provider_gate_metadata(
    value: Any,
    field: str,
    *,
    require_thread_turn: bool = True,
) -> dict[str, str | None]:
    result = _provider_gate_exact_keys(
        value, PROVIDER_GATE_REQUEST_METADATA_KEYS, field
    )
    normalized: dict[str, str | None] = {}
    for name in sorted(PROVIDER_GATE_REQUEST_METADATA_KEYS):
        normalized[name] = _provider_gate_string(
            result[name],
            f"{field}.{name}",
            nullable=(
                not require_thread_turn or name not in {"thread_id", "turn_id"}
            ),
        )
    return normalized


def _provider_gate_crossing_release_kind(request_kind: Any) -> str:
    """Return the one safe release kind for an authenticated request purpose."""

    if request_kind == "turn":
        return PROVIDER_GATE_ORDINARY_CROSSING_RELEASE
    if request_kind == "compaction":
        return PROVIDER_GATE_COMPACTION_CROSSING_RELEASE
    raise BenchmarkToolError("provider gate crossing has an unknown request kind")


def _provider_gate_content_type_is_allowed(value: Any) -> bool:
    """Recognize only the frozen SSE media type and optional UTF-8 charset."""

    return isinstance(value, str) and (
        _PROVIDER_GATE_SSE_CONTENT_TYPE_RE.fullmatch(value) is not None
    )


def _validate_provider_gate_sse_authentication(
    call: dict[str, Any], *, field: str
) -> dict[str, Any]:
    """Authenticate the v3 header observation and strict SSE parser receipt."""

    content_type_occurrences = _nonnegative_int(
        call["upstream_content_type_occurrences"],
        f"{field}.upstream_content_type_occurrences",
    )
    content_encoding_occurrences = _nonnegative_int(
        call["upstream_content_encoding_occurrences"],
        f"{field}.upstream_content_encoding_occurrences",
    )
    if content_type_occurrences not in {0, 1}:
        raise BenchmarkToolError(
            f"provider gate {field} has ambiguous Content-Type occurrences"
        )
    if content_encoding_occurrences not in {0, 1}:
        raise BenchmarkToolError(
            f"provider gate {field} has ambiguous Content-Encoding occurrences"
        )

    raw_content_type = call["upstream_content_type"]
    if content_type_occurrences == 0:
        if raw_content_type is not None:
            raise BenchmarkToolError(
                f"provider gate {field} invented an upstream Content-Type"
            )
        expected_content_type_basis = (
            "authenticated_stream_request_header_absent"
        )
        expected_synthesized = True
    else:
        if not _provider_gate_content_type_is_allowed(raw_content_type):
            raise BenchmarkToolError(
                f"provider gate {field} has a disallowed upstream Content-Type"
            )
        expected_content_type_basis = "declared_text_event_stream"
        expected_synthesized = False

    raw_content_encoding = call["upstream_content_encoding"]
    if content_encoding_occurrences == 0:
        if raw_content_encoding is not None:
            raise BenchmarkToolError(
                f"provider gate {field} invented an upstream Content-Encoding"
            )
        expected_content_encoding_basis = "implicit_identity_header_absent"
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
                f"provider gate {field} has a disallowed upstream Content-Encoding"
            )
        expected_content_encoding_basis = "declared_identity"

    authentication = _provider_gate_exact_keys(
        call["upstream_sse_authentication"],
        PROVIDER_GATE_SSE_AUTHENTICATION_KEYS,
        f"{field}.upstream_sse_authentication",
    )
    json_event_count = _positive_int(
        authentication["json_event_count"],
        f"{field}.upstream_sse_authentication.json_event_count",
    )
    completed_event_index = _nonnegative_int(
        authentication["completed_event_index"],
        f"{field}.upstream_sse_authentication.completed_event_index",
    )
    done_count = _nonnegative_int(
        authentication["done_count"],
        f"{field}.upstream_sse_authentication.done_count",
    )
    body_sha256 = _provider_gate_sha256(
        authentication["body_sha256"],
        f"{field}.upstream_sse_authentication.body_sha256",
    )
    body_bytes = _positive_int(
        authentication["body_bytes"],
        f"{field}.upstream_sse_authentication.body_bytes",
    )
    if (
        authentication["schema_version"] != 1
        or isinstance(authentication["schema_version"], bool)
        or authentication["protocol"]
        != "highambench-responses-sse-envelope-v1"
        or authentication["parser"] != "highambench-strict-responses-sse-v2"
        or authentication["complete"] is not True
        or authentication["content_type_basis"]
        != expected_content_type_basis
        or authentication["content_type_basis"]
        not in PROVIDER_GATE_SSE_CONTENT_TYPE_BASES
        or authentication["content_encoding_basis"]
        != expected_content_encoding_basis
        or authentication["content_encoding_basis"]
        not in PROVIDER_GATE_SSE_CONTENT_ENCODING_BASES
        or completed_event_index != json_event_count - 1
        or done_count not in {0, 1}
        or body_sha256 != call["upstream_body_sha256"]
        or body_bytes != call["upstream_body_bytes"]
        or authentication["response_id"] != call["response_id"]
        or authentication["downstream_content_type_synthesized"]
        is not expected_synthesized
    ):
        raise BenchmarkToolError(
            f"provider gate {field} strict SSE authentication is inconsistent"
        )
    return {
        **authentication,
        "json_event_count": json_event_count,
        "completed_event_index": completed_event_index,
        "done_count": done_count,
        "body_sha256": body_sha256,
        "body_bytes": body_bytes,
    }


def _provider_gate_credential_headers(value: Any, field: str) -> list[str]:
    if (
        not isinstance(value, list)
        or value != sorted(set(value))
        or "authorization" not in value
        or any(
            not isinstance(item, str)
            or item not in PROVIDER_GATE_CREDENTIAL_HEADER_NAMES
            for item in value
        )
    ):
        raise BenchmarkToolError(
            f"provider gate {field} credential-header names are malformed"
        )
    return list(value)


def _provider_gate_usage(value: Any, field: str) -> dict[str, int]:
    result = _provider_gate_exact_keys(value, PROVIDER_GATE_USAGE_KEYS, field)
    normalized = {
        name: _nonnegative_int(result[name], f"{field}.{name}")
        for name in PROVIDER_GATE_USAGE_KEYS
    }
    if normalized["cached_input_tokens"] > normalized["input_tokens"]:
        raise BenchmarkToolError(f"provider gate {field} cached input exceeds input")
    if normalized["cache_write_input_tokens"] > normalized["input_tokens"]:
        raise BenchmarkToolError(f"provider gate {field} cache-write input exceeds input")
    if normalized["reasoning_output_tokens"] > normalized["output_tokens"]:
        raise BenchmarkToolError(f"provider gate {field} reasoning output exceeds output")
    if normalized["total_tokens"] != (
        normalized["input_tokens"] + normalized["output_tokens"]
    ):
        raise BenchmarkToolError(f"provider gate {field} total is not input plus output")
    return normalized


def _normalize_provider_api_usage(value: Any, field: str) -> dict[str, int]:
    if not isinstance(value, Mapping):
        raise BenchmarkToolError(f"provider gate {field} must be an object")
    input_tokens = _nonnegative_int(value.get("input_tokens"), f"{field}.input_tokens")
    output_tokens = _nonnegative_int(
        value.get("output_tokens"), f"{field}.output_tokens"
    )
    total_tokens = _nonnegative_int(value.get("total_tokens"), f"{field}.total_tokens")
    if total_tokens != input_tokens + output_tokens:
        raise BenchmarkToolError(f"provider gate {field} has an invalid total")
    details = value.get("input_tokens_details")
    if details is None:
        details = {}
    if isinstance(details, Mapping):
        cached = _nonnegative_int(
            details.get("cached_tokens", 0), f"{field}.input_tokens_details.cached_tokens"
        )
        cache_write = _nonnegative_int(
            details.get("cache_write_tokens", 0),
            f"{field}.input_tokens_details.cache_write_tokens",
        )
    else:
        raise BenchmarkToolError(f"provider gate {field}.input_tokens_details is invalid")
    output_details = value.get("output_tokens_details")
    if output_details is None:
        output_details = {}
    if not isinstance(output_details, Mapping):
        raise BenchmarkToolError(f"provider gate {field}.output_tokens_details is invalid")
    reasoning = _nonnegative_int(
        output_details.get("reasoning_tokens", 0),
        f"{field}.output_tokens_details.reasoning_tokens",
    )
    if cached > input_tokens or cache_write > input_tokens or reasoning > output_tokens:
        raise BenchmarkToolError(f"provider gate {field} token detail exceeds its total")
    return {
        "input_tokens": input_tokens,
        "cached_input_tokens": cached,
        "cache_write_input_tokens": cache_write,
        "output_tokens": output_tokens,
        "reasoning_output_tokens": reasoning,
        "total_tokens": total_tokens,
    }


def _read_provider_gate_json(
    path: Path, *, sealed: bool
) -> tuple[dict[str, Any], bytes]:
    """Read a canonical gate snapshot without trusting its summary fields."""

    if not path.is_absolute():
        raise BenchmarkToolError("provider gate artifact path must be absolute")
    if not hasattr(os, "O_NOFOLLOW"):
        raise BenchmarkToolError("provider gate authentication requires O_NOFOLLOW")
    try:
        descriptor = os.open(
            path,
            os.O_RDONLY | os.O_CLOEXEC | os.O_NOFOLLOW,
        )
    except OSError as error:
        raise BenchmarkToolError(
            f"cannot open provider-token-gate artifact: {error}"
        ) from error
    try:
        metadata = os.fstat(descriptor)
        expected_mode = 0o444 if sealed else 0o600
        if (
            not stat.S_ISREG(metadata.st_mode)
            or stat.S_IMODE(metadata.st_mode) != expected_mode
        ):
            raise BenchmarkToolError(
                "provider gate artifact is not a regular file with mode "
                f"{expected_mode:04o}"
            )
        payload = _provider_transport_read_all(descriptor)
        if len(payload) != metadata.st_size:
            raise BenchmarkToolError(
                "provider gate artifact changed while its fd was read"
            )
    finally:
        os.close(descriptor)
    if sealed:
        try:
            post = path.lstat()
        except OSError as error:
            raise BenchmarkToolError(
                f"sealed provider gate disappeared after authentication: {error}"
            ) from error
        if (
            not stat.S_ISREG(post.st_mode)
            or stat.S_ISLNK(post.st_mode)
            or (post.st_dev, post.st_ino, post.st_size, stat.S_IMODE(post.st_mode))
            != (
                metadata.st_dev,
                metadata.st_ino,
                metadata.st_size,
                0o444,
            )
        ):
            raise BenchmarkToolError(
                "sealed provider gate pathname changed during authentication"
            )
    try:
        text = payload.decode("utf-8")
        value = json.loads(text)
    except (UnicodeError, json.JSONDecodeError) as error:
        raise BenchmarkToolError(f"provider gate is not canonical UTF-8 JSON: {error}") from error
    record = _provider_gate_exact_keys(
        value, PROVIDER_GATE_TOP_LEVEL_KEYS, "top-level record"
    )
    canonical = (
        json.dumps(
            record,
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        ).encode("utf-8")
        + b"\n"
    )
    if payload != canonical:
        raise BenchmarkToolError("provider gate artifact is not canonical JSON")
    unsigned = {
        name: item for name, item in record.items() if name != "record_sha256"
    }
    expected_self_hash = hashlib.sha256(
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
    if (
        _provider_gate_sha256(record["record_sha256"], "record_sha256")
        != expected_self_hash
    ):
        raise BenchmarkToolError("provider gate artifact self-hash mismatch")
    return record, payload


def _provider_gate_prompt_release_sha256(record: Mapping[str, Any]) -> str:
    return hashlib.sha256(
        (
            json.dumps(
                dict(record),
                sort_keys=True,
                separators=(",", ":"),
                ensure_ascii=False,
            )
            + "\n"
        ).encode("utf-8")
    ).hexdigest()


def _validate_provider_gate_sanitized_release(
    call: Mapping[str, Any], raw_usage: Mapping[str, Any], *, field: str
) -> None:
    event = call.get("released_sanitized_event")
    events = call.get("released_sanitized_events")
    body_text = call.get("released_sanitized_body_utf8")
    if (
        not isinstance(event, Mapping)
        or not isinstance(events, list)
        or not events
        or any(not isinstance(item, Mapping) for item in events)
        or not isinstance(body_text, str)
    ):
        raise BenchmarkToolError(f"provider gate {field} lacks its sanitized body")

    release_kind = call.get("release_kind")
    request_metadata = call.get("request_metadata")
    request_kind = (
        request_metadata.get("request_kind")
        if isinstance(request_metadata, Mapping)
        else None
    )
    if release_kind == PROVIDER_GATE_COMPACTION_CROSSING_RELEASE:
        if request_kind != "compaction" or len(events) != 2:
            raise BenchmarkToolError(
                f"provider gate {field} compaction release kind/frame count changed"
            )
        item_event = events[0]
        if (
            set(item_event) != {"type", "item"}
            or item_event.get("type") != "response.output_item.done"
        ):
            raise BenchmarkToolError(
                f"provider gate {field} compaction event is not minimal"
            )
        item = item_event.get("item")
        if (
            not isinstance(item, Mapping)
            or set(item) != {"type", "encrypted_content"}
            or item.get("type") != "compaction"
            or not isinstance(item.get("encrypted_content"), str)
            or not item["encrypted_content"]
        ):
            raise BenchmarkToolError(
                f"provider gate {field} compaction item is not minimal"
            )
    elif release_kind == PROVIDER_GATE_ORDINARY_CROSSING_RELEASE:
        if request_kind != "turn" or len(events) != 1:
            raise BenchmarkToolError(
                f"provider gate {field} ordinary release kind/frame count changed"
            )
    else:
        raise BenchmarkToolError(f"provider gate {field} sanitized release kind changed")

    def canonical_event(value: Mapping[str, Any]) -> str:
        return json.dumps(
            dict(value),
            sort_keys=True,
            separators=(",", ":"),
            ensure_ascii=False,
        )

    if canonical_event(events[-1]) != canonical_event(event):
        raise BenchmarkToolError(
            f"provider gate {field} completion is not the final sanitized event"
        )
    expected_body = "".join(
        "event: "
        + str(item["type"])
        + "\ndata: "
        + canonical_event(item)
        + "\n\n"
        for item in events
    )
    if body_text != expected_body:
        raise BenchmarkToolError(f"provider gate {field} sanitized SSE is noncanonical")
    encoded = body_text.encode("utf-8")
    released_body_bytes = _positive_int(
        call.get("released_body_bytes"), f"{field}.released_body_bytes"
    )
    if (
        hashlib.sha256(encoded).hexdigest() != call.get("released_body_sha256")
        or len(encoded) != released_body_bytes
    ):
        raise BenchmarkToolError(f"provider gate {field} sanitized body hash disagrees")
    if set(event) != {"type", "response"} or event.get("type") != "response.completed":
        raise BenchmarkToolError(f"provider gate {field} sanitized event shape changed")
    response = event.get("response")
    if not isinstance(response, Mapping) or set(response) != {
        "id",
        "usage",
        "end_turn",
        "output",
    }:
        raise BenchmarkToolError(f"provider gate {field} sanitized response is absent")
    if (
        response.get("id") != call.get("response_id")
        or not _provider_gate_same_json(response.get("usage"), raw_usage)
        or response.get("output") != []
        or response.get("end_turn") is not True
    ):
        raise BenchmarkToolError(f"provider gate {field} sanitized completion binding changed")

    forbidden_names = {
        "items",
        "tool_calls",
        "function_call",
        "output_item",
        "output_items",
        "output_text",
        "content",
        "arguments",
        "call_id",
    }
    forbidden_types = {
        "function_call",
        "custom_tool_call",
        "computer_call",
        "shell_call",
        "tool_call",
        "message",
    }

    def reject_action_fields(value: Any) -> None:
        if isinstance(value, Mapping):
            for name, item in value.items():
                lowered = str(name).lower()
                if lowered in forbidden_names or lowered.endswith("_call"):
                    raise BenchmarkToolError(
                        f"provider gate {field} retained an action-bearing field"
                    )
                if lowered == "type" and isinstance(item, str) and item in forbidden_types:
                    raise BenchmarkToolError(
                        f"provider gate {field} retained an action-bearing event"
                    )
                reject_action_fields(item)
        elif isinstance(value, list):
            for item in value:
                reject_action_fields(item)

    # The forced empty output is intentionally inspected separately; recurse
    # through every other preserved metadata value for hidden action records.
    reject_action_fields(
        {name: value for name, value in response.items() if name != "output"}
    )


def _validate_provider_gate_configuration(
    value: Any,
    *,
    field: str,
    token_limit: int,
    model_catalog_sha256: str,
    model_entry_sha256: str,
    expected_transport_provenance: Mapping[str, Any],
) -> tuple[dict[str, Any], int]:
    configuration = _provider_gate_exact_keys(
        value,
        PROVIDER_GATE_CONFIGURATION_KEYS,
        field,
    )
    configured_limit = _positive_int(
        configuration["token_limit"], f"{field}.token_limit"
    )
    response_bound = _positive_int(
        configuration["response_bound"], f"{field}.response_bound"
    )
    if configured_limit != token_limit:
        raise BenchmarkToolError("provider gate token cap disagrees with the run")
    if response_bound != PROVIDER_RESPONSE_TOKEN_BOUND:
        raise BenchmarkToolError(
            "provider gate response bound is not the frozen model bound"
        )
    if configuration["strict_admission_inequality"] != (
        "completed_tokens + (open_request_count + 1) * response_bound < token_limit"
    ):
        raise BenchmarkToolError("provider gate has the wrong admission inequality")
    if (
        configuration["upstream_origin"] != "https://chatgpt.com"
        or configuration["upstream_base_path"] != "/backend-api/codex"
        or configuration["loopback_only"] is not True
        or configuration["websockets_supported"] is not False
        or type(configuration["request_retries"]) is not int
        or configuration["request_retries"] != 0
        or type(configuration["stream_retries"]) is not int
        or configuration["stream_retries"] != 0
        or configuration["request_compression"] is not False
        or configuration["response_compression"] != "identity"
        or configuration["capability_persisted"] is not False
        or configuration["response_bound_enforcement"]
        != "runtime_fail_closed_before_buffered_response_release"
        or configuration["counted_route"] != "POST /responses"
        or configuration["counted_request_kinds"] != ["turn", "compaction"]
        or configuration["rejected_inference_routes"]
        != ["POST /responses/compact"]
        or configuration["allowed_setup_route_prefixes"] != []
        or configuration["crossing_release_policy"]
        != PROVIDER_GATE_CROSSING_RELEASE_POLICY
    ):
        raise BenchmarkToolError("provider gate static transport contract changed")
    upstream_response_contract = _provider_gate_exact_keys(
        configuration["upstream_response_contract"],
        PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_KEYS,
        f"{field}.upstream_response_contract",
    )
    if not _provider_gate_same_json(
        upstream_response_contract,
        PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT,
    ):
        raise BenchmarkToolError("provider gate upstream SSE contract changed")
    if (
        _provider_gate_sha256(
            configuration["model_catalog_sha256"],
            f"{field}.model_catalog_sha256",
        )
        != model_catalog_sha256
        or _provider_gate_sha256(
            configuration["model_entry_sha256"],
            f"{field}.model_entry_sha256",
        )
        != model_entry_sha256
    ):
        raise BenchmarkToolError("provider gate model-catalog binding changed")
    configuration["transport_provenance"] = (
        _validate_provider_transport_provenance(
            configuration["transport_provenance"],
            field=f"{field}.transport_provenance",
            expected=expected_transport_provenance,
        )
    )
    configuration["upstream_response_contract"] = upstream_response_contract
    return configuration, response_bound


def authenticate_provider_gate_artifact(
    path: Path,
    *,
    token_limit: int,
    run_id: str,
    model: str,
    reasoning_effort: str,
    root_thread_id: str,
    prompt_release_sha256: str,
    prompt_release_protocol: str,
    prompt_sha256: str,
    model_catalog_sha256: str,
    model_entry_sha256: str,
    expected_transport_provenance: Mapping[str, Any],
    usage: Mapping[str, Any] | None,
    expected_source_sha256: str | None = None,
) -> dict[str, Any]:
    """Independently replay and authenticate one finalized provider-gate record.

    The proxy's booleans are evidence to audit, never the source of truth.  This
    verifier recomputes cached-inclusive totals, response identities, admission
    reservations, the unique crossing, release quarantine, denials, and every
    app-server crossbinding from the canonical mode-0444 artifact.
    """

    runner_and_core_keysets = (
        (PROVIDER_GATE_TOP_LEVEL_KEYS, CORE_PROVIDER_GATE_TOP_LEVEL_KEYS),
        (
            PROVIDER_GATE_CONFIGURATION_KEYS,
            CORE_PROVIDER_GATE_CONFIGURATION_KEYS,
        ),
        (
            PROVIDER_GATE_IMPLEMENTATION_KEYS,
            CORE_PROVIDER_GATE_IMPLEMENTATION_KEYS,
        ),
        (PROVIDER_GATE_BINDING_KEYS, CORE_PROVIDER_GATE_BINDING_KEYS),
        (PROVIDER_GATE_LIFECYCLE_KEYS, CORE_PROVIDER_GATE_LIFECYCLE_KEYS),
        (PROVIDER_GATE_STATE_KEYS, CORE_PROVIDER_GATE_STATE_KEYS),
        (PROVIDER_GATE_CALL_KEYS, CORE_PROVIDER_GATE_CALL_KEYS),
        (
            PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_KEYS,
            CORE_PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_KEYS,
        ),
        (
            PROVIDER_GATE_SSE_AUTHENTICATION_KEYS,
            CORE_PROVIDER_GATE_SSE_AUTHENTICATION_KEYS,
        ),
        (
            PROVIDER_GATE_REQUEST_METADATA_KEYS,
            CORE_PROVIDER_GATE_REQUEST_METADATA_KEYS,
        ),
        (PROVIDER_GATE_USAGE_KEYS, CORE_PROVIDER_GATE_NORMALIZED_USAGE_KEYS),
        (PROVIDER_GATE_CROSSBIND_KEYS, CORE_PROVIDER_GATE_CROSSBIND_KEYS),
        (
            PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_KEYS,
            CORE_PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_KEYS,
        ),
        (
            PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_ITEM_KEYS,
            CORE_PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_ITEM_KEYS,
        ),
        (
            PROVIDER_GATE_APPSERVER_DELIVERY_KEYS,
            CORE_PROVIDER_GATE_APPSERVER_DELIVERY_KEYS,
        ),
        (PROVIDER_GATE_DENIAL_KEYS, CORE_PROVIDER_GATE_DENIAL_KEYS),
        (PROVIDER_GATE_TRANSITION_KEYS, CORE_PROVIDER_GATE_TRANSITION_KEYS),
        (PROVIDER_GATE_CROSSING_KEYS, CORE_PROVIDER_GATE_CROSSING_KEYS),
    )
    if any(set(runner) != set(core) for runner, core in runner_and_core_keysets):
        raise BenchmarkToolError("runner/provider-gate static schemas disagree")
    if PROVIDER_GATE_INVARIANT_KEYS != set(CORE_PROVIDER_GATE_INVARIANT_KEYS):
        raise BenchmarkToolError("runner/provider-gate invariant schemas disagree")
    if (
        PROVIDER_GATE_SCHEMA_VERSION != CORE_PROVIDER_GATE_SCHEMA_VERSION
        or PROVIDER_GATE_PROTOCOL != CORE_PROVIDER_GATE_PROTOCOL
        or PROVIDER_GATE_IMPLEMENTATION_NAME != CORE_PROVIDER_GATE_IMPLEMENTATION_NAME
        or PROVIDER_GATE_IMPLEMENTATION_VERSION
        != CORE_PROVIDER_GATE_IMPLEMENTATION_VERSION
    ):
        raise BenchmarkToolError("runner/provider-gate v6 identity disagrees")
    core_upstream_response_contract = {
        "schema_version": CORE_PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT_SCHEMA_VERSION,
        "protocol": CORE_PROVIDER_GATE_UPSTREAM_RESPONSE_PROTOCOL,
        "success_status": 200,
        "content_type_policy": CORE_PROVIDER_GATE_CONTENT_TYPE_POLICY,
        "content_encoding_policy": CORE_PROVIDER_GATE_CONTENT_ENCODING_POLICY,
        "outbound_accept": CORE_PROVIDER_GATE_OUTBOUND_ACCEPT,
        "parser": CORE_PROVIDER_GATE_SSE_PARSER,
        "downstream_content_type": CORE_PROVIDER_GATE_DOWNSTREAM_CONTENT_TYPE,
        "downstream_content_encoding": CORE_PROVIDER_GATE_DOWNSTREAM_CONTENT_ENCODING,
    }
    if (
        not _provider_gate_same_json(
            PROVIDER_GATE_UPSTREAM_RESPONSE_CONTRACT,
            core_upstream_response_contract,
        )
        or PROVIDER_GATE_SSE_CONTENT_TYPE_BASES
        != set(CORE_PROVIDER_GATE_SSE_CONTENT_TYPE_BASES)
        or PROVIDER_GATE_SSE_CONTENT_ENCODING_BASES
        != set(CORE_PROVIDER_GATE_SSE_CONTENT_ENCODING_BASES)
    ):
        raise BenchmarkToolError("runner/provider-gate upstream SSE contract disagrees")
    if not path.is_absolute():
        raise BenchmarkToolError("provider gate artifact path must be absolute")
    record, payload = _read_provider_gate_json(path, sealed=True)
    if (
        type(record["schema_version"]) is not int
        or record["schema_version"] != PROVIDER_GATE_SCHEMA_VERSION
    ):
        raise BenchmarkToolError("provider gate has the wrong schema version")
    if record["protocol"] != PROVIDER_GATE_PROTOCOL:
        raise BenchmarkToolError("provider gate has the wrong protocol")
    if record["canonical_encoding"] != PROVIDER_GATE_CANONICAL_ENCODING:
        raise BenchmarkToolError("provider gate has the wrong canonical encoding")
    if record["sealed_mode"] != PROVIDER_GATE_SEALED_MODE:
        raise BenchmarkToolError("provider gate does not attest mode 0444 sealing")

    implementation = _provider_gate_exact_keys(
        record["implementation"],
        PROVIDER_GATE_IMPLEMENTATION_KEYS,
        "implementation",
    )
    if (
        implementation["name"] != PROVIDER_GATE_IMPLEMENTATION_NAME
        or implementation["version"] != PROVIDER_GATE_IMPLEMENTATION_VERSION
    ):
        raise BenchmarkToolError("provider gate implementation identity changed")
    source_digest = _provider_gate_sha256(
        implementation["source_sha256"], "implementation.source_sha256"
    )
    if expected_source_sha256 is not None and source_digest != expected_source_sha256:
        raise BenchmarkToolError("provider gate implementation source changed")

    configuration, response_bound = _validate_provider_gate_configuration(
        record["configuration"],
        field="configuration",
        token_limit=token_limit,
        model_catalog_sha256=model_catalog_sha256,
        model_entry_sha256=model_entry_sha256,
        expected_transport_provenance=expected_transport_provenance,
    )

    bindings = _provider_gate_exact_keys(
        record["bindings"], PROVIDER_GATE_BINDING_KEYS, "bindings"
    )
    expected_bindings = {
        "root_thread_id": root_thread_id,
        "prompt_release_sha256": prompt_release_sha256,
        "prompt_release_protocol": prompt_release_protocol,
        "prompt_sha256": prompt_sha256,
        "run_id": run_id,
        "model": model,
        "reasoning_effort": reasoning_effort,
    }
    if bindings != expected_bindings:
        raise BenchmarkToolError("provider gate run/prompt/model bindings disagree")

    lifecycle = _provider_gate_exact_keys(
        record["lifecycle"], PROVIDER_GATE_LIFECYCLE_KEYS, "lifecycle"
    )
    for clock in ("unix", "monotonic"):
        values = [
            _positive_int(
                lifecycle[f"{name}_{clock}_ns"],
                f"provider_gate.lifecycle.{name}_{clock}_ns",
            )
            for name in ("started", "stopped", "finalized")
        ]
        if values != sorted(values):
            raise BenchmarkToolError("provider gate lifecycle timestamps regress")

    state = _provider_gate_exact_keys(
        record["state"], PROVIDER_GATE_STATE_KEYS, "state"
    )
    phase = state["phase"]
    if phase not in {"CLOSED", "POISONED"}:
        raise BenchmarkToolError("final provider gate phase is not terminal")
    close_reason = state["close_reason"]
    if close_reason not in PROVIDER_GATE_CLOSE_REASONS:
        raise BenchmarkToolError("provider gate has an unknown close reason")
    poison_reasons = state["poison_reasons"]
    if (
        not isinstance(poison_reasons, list)
        or poison_reasons != sorted(set(poison_reasons))
        or any(not isinstance(item, str) or not item for item in poison_reasons)
        or (phase == "POISONED") != bool(poison_reasons)
        or (close_reason == "poison") != (phase == "POISONED")
    ):
        raise BenchmarkToolError("provider gate poison state is inconsistent")
    if state["open_request_ids"] != []:
        raise BenchmarkToolError("final provider gate still has an open upstream request")
    state_completed_tokens = _nonnegative_int(
        state["completed_tokens"], "provider_gate.state.completed_tokens"
    )
    active_handler_count = _nonnegative_int(
        state["active_handler_count"], "provider_gate.state.active_handler_count"
    )
    state_sequence = _positive_int(
        state["sequence"], "provider_gate.state.sequence"
    )
    if (
        state["all_complete"] is not True
        or state["no_post_close_upstream"] is not True
        or state["poisoned"] is not (phase == "POISONED")
        or not isinstance(state["crossing_closed"], bool)
        or active_handler_count != 0
        or state["handlers_quiescent"] is not True
        or state_sequence < 1
    ):
        raise BenchmarkToolError("provider gate final lifecycle summary is inconsistent")

    raw_calls = record["calls"]
    if not isinstance(raw_calls, list):
        raise BenchmarkToolError("provider gate calls must be a list")
    calls: list[dict[str, Any]] = []
    call_ids: set[str] = set()
    response_ids: set[str] = set()
    event_sequences: set[int] = set()
    global_sequences: set[int] = set()
    global_sequence_events: list[tuple[int, int]] = []
    prior_call_sequence = 0
    for index, raw_call in enumerate(raw_calls):
        call = _provider_gate_exact_keys(
            raw_call, PROVIDER_GATE_CALL_KEYS, f"calls[{index}]"
        )
        call_sequence = _positive_int(call["sequence"], f"calls[{index}].sequence")
        if call_sequence <= prior_call_sequence or call_sequence in global_sequences:
            raise BenchmarkToolError("provider gate call sequence is not canonical")
        global_sequences.add(call_sequence)
        prior_call_sequence = call_sequence
        call_id = _provider_gate_string(call["call_id"], f"calls[{index}].call_id")
        response_id = _provider_gate_string(
            call["response_id"], f"calls[{index}].response_id"
        )
        assert call_id is not None and response_id is not None
        if call_id != f"provider-call-{call_sequence:08d}":
            raise BenchmarkToolError("provider gate call identity is not sequence-bound")
        if call_id in call_ids or response_id in response_ids:
            raise BenchmarkToolError("provider gate has a duplicate call/response identity")
        call_ids.add(call_id)
        response_ids.add(response_id)
        if call["method"] != "POST" or call["route"] != "/responses":
            raise BenchmarkToolError("provider gate admitted an unknown inference route")
        if call["request_model"] != model or call["request_stream"] is not True:
            raise BenchmarkToolError("provider gate request model/stream binding changed")
        _provider_gate_sha256(
            call["request_body_sha256"], f"calls[{index}].request_body_sha256"
        )
        _positive_int(call["request_bytes"], f"calls[{index}].request_bytes")
        metadata = _provider_gate_metadata(
            call["request_metadata"], f"calls[{index}].request_metadata"
        )
        if any(metadata[name] is None for name in PROVIDER_GATE_REQUEST_METADATA_KEYS):
            raise BenchmarkToolError(
                "provider gate counted call lacks pinned app-server request metadata"
            )
        if metadata["request_kind"] not in configuration["counted_request_kinds"]:
            raise BenchmarkToolError(
                "provider gate counted call has an unknown request kind"
            )
        _provider_gate_credential_headers(
            call["credential_headers_present"],
            f"calls[{index}].credential_headers_present",
        )
        if call["admission_mode"] not in PROVIDER_GATE_ADMISSION_MODES:
            raise BenchmarkToolError("provider gate has an invalid admission mode")
        call_response_bound = _positive_int(
            call["response_bound"], f"calls[{index}].response_bound"
        )
        if call_response_bound != response_bound:
            raise BenchmarkToolError("provider gate call used another response bound")
        admitted_mono = _positive_int(
            call["admitted_monotonic_ns"],
            f"calls[{index}].admitted_monotonic_ns",
        )
        admitted_wall = _positive_int(
            call["admitted_unix_ns"], f"calls[{index}].admitted_unix_ns"
        )
        global_sequence_events.append((call_sequence, admitted_mono))
        upstream_mono = _positive_int(
            call["upstream_start_monotonic_ns"],
            f"calls[{index}].upstream_start_monotonic_ns",
        )
        upstream_wall = _positive_int(
            call["upstream_start_unix_ns"],
            f"calls[{index}].upstream_start_unix_ns",
        )
        commit_mono = _positive_int(
            call["commit_monotonic_ns"],
            f"calls[{index}].commit_monotonic_ns",
        )
        commit_wall = _positive_int(
            call["commit_unix_ns"], f"calls[{index}].commit_unix_ns"
        )
        for numeric_field in (
            "completed_before",
            "open_before",
            "reserved_before",
            "reservation_after",
            "previous_total",
            "committed_total",
        ):
            call[numeric_field] = _nonnegative_int(
                call[numeric_field], f"calls[{index}].{numeric_field}"
            )
        if not isinstance(call["crossed_cap"], bool):
            raise BenchmarkToolError(
                "provider gate call crossing flag is not Boolean"
            )
        if (
            call["upstream_started"] is not True
            or not admitted_mono <= upstream_mono <= commit_mono
            or not admitted_wall <= upstream_wall <= commit_wall
            or admitted_mono < lifecycle["started_monotonic_ns"]
            or commit_mono > lifecycle["stopped_monotonic_ns"]
        ):
            raise BenchmarkToolError("provider gate call timestamps/lifecycle are invalid")
        upstream_status = _positive_int(
            call["upstream_status"], f"calls[{index}].upstream_status"
        )
        if upstream_status != 200:
            raise BenchmarkToolError("provider gate upstream response contract changed")
        upstream_hash = _provider_gate_sha256(
            call["upstream_body_sha256"], f"calls[{index}].upstream_body_sha256"
        )
        upstream_bytes = _positive_int(
            call["upstream_body_bytes"], f"calls[{index}].upstream_body_bytes"
        )
        call["upstream_body_sha256"] = upstream_hash
        call["upstream_body_bytes"] = upstream_bytes
        call["upstream_sse_authentication"] = (
            _validate_provider_gate_sse_authentication(
                call,
                field=f"calls[{index}]",
            )
        )
        released_hash = _provider_gate_sha256(
            call["released_body_sha256"], f"calls[{index}].released_body_sha256"
        )
        released_bytes = _positive_int(
            call["released_body_bytes"], f"calls[{index}].released_body_bytes"
        )
        call_usage = _provider_gate_usage(
            call["normalized_usage"], f"calls[{index}].normalized_usage"
        )
        if _normalize_provider_api_usage(
            call["usage"], f"calls[{index}].usage"
        ) != call_usage:
            raise BenchmarkToolError("provider gate normalized usage is inconsistent")
        if call_usage["total_tokens"] > response_bound:
            raise BenchmarkToolError("provider response exceeded the frozen response bound")
        manifest = _provider_gate_exact_keys(
            call["response_output_manifest"],
            PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_KEYS,
            f"calls[{index}].response_output_manifest",
        )
        manifest_items = manifest.get("items")
        if (
            manifest.get("schema_version") != 1
            or manifest.get("response_id") != response_id
            or not isinstance(manifest_items, list)
            or manifest.get("output_item_count") != len(manifest_items)
        ):
            raise BenchmarkToolError("provider response output manifest is malformed")
        normalized_manifest_items: list[dict[str, Any]] = []
        action_capable_count = 0
        for item_index, raw_manifest_item in enumerate(manifest_items):
            manifest_item = _provider_gate_exact_keys(
                raw_manifest_item,
                PROVIDER_GATE_RESPONSE_OUTPUT_MANIFEST_ITEM_KEYS,
                f"calls[{index}].response_output_manifest.items[{item_index}]",
            )
            item_type = _provider_gate_string(
                manifest_item["type"],
                f"calls[{index}].response_output_manifest.items[{item_index}].type",
            )
            assert item_type is not None
            if item_type == "function_call" or item_type.endswith("_call"):
                action_capable_count += 1
            if manifest_item.get("index") != item_index:
                raise BenchmarkToolError("provider output manifest index is not canonical")
            for nullable_string in ("id", "name", "namespace", "call_id"):
                _provider_gate_string(
                    manifest_item.get(nullable_string),
                    f"calls[{index}].response_output_manifest.items[{item_index}].{nullable_string}",
                    nullable=True,
                )
            _provider_gate_sha256(
                manifest_item.get("payload_sha256"),
                f"calls[{index}].response_output_manifest.items[{item_index}].payload_sha256",
            )
            _positive_int(
                manifest_item.get("payload_bytes"),
                f"calls[{index}].response_output_manifest.items[{item_index}].payload_bytes",
            )
            arguments_sha = manifest_item.get("arguments_sha256")
            arguments_bytes = manifest_item.get("arguments_bytes")
            if (arguments_sha is None) != (arguments_bytes is None):
                raise BenchmarkToolError("provider output argument digest is incomplete")
            if arguments_sha is not None:
                _provider_gate_sha256(
                    arguments_sha,
                    f"calls[{index}].response_output_manifest.items[{item_index}].arguments_sha256",
                )
                _nonnegative_int(
                    arguments_bytes,
                    f"calls[{index}].response_output_manifest.items[{item_index}].arguments_bytes",
                )
            wait_timeout = manifest_item.get("wait_timeout_ms")
            if wait_timeout is not None:
                normalized_wait_timeout = _positive_int(
                    wait_timeout,
                    f"calls[{index}].response_output_manifest.items[{item_index}].wait_timeout_ms",
                )
                if (
                    not CORE_PROVIDER_GATE_WAIT_AGENT_MIN_TIMEOUT_MS
                    <= normalized_wait_timeout
                    <= CORE_PROVIDER_GATE_WAIT_AGENT_MAX_TIMEOUT_MS
                    or item_type != "function_call"
                    or manifest_item.get("name") != "wait_agent"
                    or manifest_item.get("namespace") != "collaboration"
                    or not isinstance(manifest_item.get("id"), str)
                    or not manifest_item["id"]
                    or not isinstance(manifest_item.get("call_id"), str)
                    or not manifest_item["call_id"]
                    or arguments_sha is None
                ):
                    raise BenchmarkToolError(
                        "provider collaboration-wait manifest identity is inconsistent"
                    )
            normalized_manifest_items.append(manifest_item)
        if manifest.get("action_capable_item_count") != action_capable_count:
            raise BenchmarkToolError(
                "provider output manifest action count is inconsistent"
            )
        call["response_output_manifest"] = {
            **manifest,
            "items": normalized_manifest_items,
        }
        if call["release_kind"] == "byte_identity":
            if (released_hash, released_bytes) != (upstream_hash, upstream_bytes):
                raise BenchmarkToolError("provider byte-identity release changed its body")
            if (
                call["released_sanitized_event"] is not None
                or call["released_sanitized_events"] is not None
                or call["released_sanitized_body_utf8"] is not None
            ):
                raise BenchmarkToolError("provider byte-identity call has sanitized data")
        elif call["release_kind"] in {
            PROVIDER_GATE_ORDINARY_CROSSING_RELEASE,
            PROVIDER_GATE_COMPACTION_CROSSING_RELEASE,
        }:
            _validate_provider_gate_sanitized_release(
                call,
                call["usage"],
                field=f"calls[{index}]",
            )
        else:
            raise BenchmarkToolError("provider gate has an unknown response release kind")
        delivery = _provider_gate_exact_keys(
            call["appserver_delivery"],
            PROVIDER_GATE_APPSERVER_DELIVERY_KEYS,
            f"calls[{index}].appserver_delivery",
        )
        delivery_bind_mono = _positive_int(
            delivery["bind_monotonic_ns"],
            f"calls[{index}].appserver_delivery.bind_monotonic_ns",
        )
        delivery_bind_wall = _positive_int(
            delivery["bind_unix_ns"],
            f"calls[{index}].appserver_delivery.bind_unix_ns",
        )
        if delivery_bind_mono < commit_mono or delivery_bind_wall < commit_wall:
            raise BenchmarkToolError("provider delivery predates provider commit")
        crossbind: dict[str, Any] | None = None
        if delivery.get("kind") == "direct_raw_response":
            if (
                call["client_release_complete"] is not True
                or call["error"] is not None
                or delivery.get("successor_call_id") is not None
                or delivery.get("successor_response_id") is not None
            ):
                raise BenchmarkToolError("direct provider delivery names a successor")
            crossbind = _provider_gate_exact_keys(
                call["appserver_crossbind"],
                PROVIDER_GATE_CROSSBIND_KEYS,
                f"calls[{index}].appserver_crossbind",
            )
            event_sequence = _positive_int(
                crossbind["event_sequence"],
                f"calls[{index}].appserver_crossbind.event_sequence",
            )
            if event_sequence in event_sequences:
                raise BenchmarkToolError(
                    "provider gate reused an app-server event sequence"
                )
            event_sequences.add(event_sequence)
            if (
                crossbind["thread_id"] != metadata["thread_id"]
                or crossbind["turn_id"] != metadata["turn_id"]
                or _provider_gate_usage(
                    crossbind["normalized_usage"],
                    f"calls[{index}].appserver_crossbind.normalized_usage",
                )
                != call_usage
                or _positive_int(
                    crossbind["bind_monotonic_ns"],
                    f"calls[{index}].appserver_crossbind.bind_monotonic_ns",
                )
                != delivery_bind_mono
                or _positive_int(
                    crossbind["bind_unix_ns"],
                    f"calls[{index}].appserver_crossbind.bind_unix_ns",
                )
                != delivery_bind_wall
            ):
                raise BenchmarkToolError(
                    "provider gate app-server crossbinding disagrees"
                )
        elif delivery.get("kind") == "suppressed_collaboration_wait":
            manifest_items = call["response_output_manifest"]["items"]
            waits = [
                item for item in manifest_items if item.get("wait_timeout_ms") is not None
            ]
            if (
                call["client_release_complete"] is not True
                or call["error"] is not None
                or call["appserver_crossbind"] is not None
                or call["release_kind"] != "byte_identity"
                or call["crossed_cap"] is not False
                or metadata.get("request_kind") != "turn"
                or call["response_output_manifest"].get(
                    "action_capable_item_count"
                )
                != 1
                or len(waits) != 1
                or any(
                    item is not waits[0] and item.get("type") != "reasoning"
                    for item in manifest_items
                )
                or waits[0].get("type") != "function_call"
                or waits[0].get("name") != "wait_agent"
                or waits[0].get("namespace") != "collaboration"
                or not isinstance(waits[0].get("id"), str)
                or not isinstance(waits[0].get("call_id"), str)
                or not isinstance(delivery.get("successor_call_id"), str)
                or not delivery["successor_call_id"]
                or not isinstance(delivery.get("successor_response_id"), str)
                or not delivery["successor_response_id"]
            ):
                raise BenchmarkToolError(
                    "provider suppressed delivery is not one exact collaboration wait"
                )
        elif delivery.get("kind") == "superseded_by_collaboration_message":
            if (
                call["client_release_complete"] is not True
                or call["error"] is not None
                or call["appserver_crossbind"] is not None
                or call["release_kind"] != "byte_identity"
                or call["crossed_cap"] is not False
                or metadata.get("request_kind") != "turn"
                or not isinstance(delivery.get("successor_call_id"), str)
                or not delivery["successor_call_id"]
                or not isinstance(delivery.get("successor_response_id"), str)
                or not delivery["successor_response_id"]
            ):
                raise BenchmarkToolError(
                    "provider superseded delivery is not an exact complete response"
                )
        elif delivery.get("kind") == "discarded_after_explicit_child_interrupt":
            if (
                call["client_release_complete"] is not False
                or call["error"] is not None
                or call["appserver_crossbind"] is not None
                or call["release_kind"] != "byte_identity"
                or call["crossed_cap"] is not False
                or metadata.get("request_kind") != "turn"
                or not isinstance(delivery.get("successor_call_id"), str)
                or not delivery["successor_call_id"]
                or not isinstance(delivery.get("successor_response_id"), str)
                or not delivery["successor_response_id"]
            ):
                raise BenchmarkToolError(
                    "provider interrupted-child discard is not an exact committed response"
                )
        else:
            raise BenchmarkToolError("provider gate has an unknown delivery kind")
        call["request_metadata"] = metadata
        call["normalized_usage"] = call_usage
        call["appserver_crossbind"] = (
            {**crossbind, "normalized_usage": call_usage}
            if crossbind is not None
            else None
        )
        call["appserver_delivery"] = delivery
        calls.append(call)

    reported_crossing: dict[str, Any] | None = None
    if state["crossing"] is not None:
        reported_crossing = _provider_gate_exact_keys(
            state["crossing"], PROVIDER_GATE_CROSSING_KEYS, "state.crossing"
        )
        crossing_sequence = _positive_int(
            reported_crossing["sequence"], "state.crossing.sequence"
        )
        _provider_gate_string(
            reported_crossing["call_id"], "state.crossing.call_id"
        )
        _provider_gate_string(
            reported_crossing["response_id"], "state.crossing.response_id"
        )
        crossing_request_kind = _provider_gate_string(
            reported_crossing["request_kind"], "state.crossing.request_kind"
        )
        for numeric_field in (
            "previous_total",
            "response_tokens",
            "completed_tokens",
            "overshoot_tokens",
        ):
            reported_crossing[numeric_field] = _nonnegative_int(
                reported_crossing[numeric_field],
                f"state.crossing.{numeric_field}",
            )
        _positive_int(
            reported_crossing["commit_unix_ns"],
            "state.crossing.commit_unix_ns",
        )
        if (
            reported_crossing["sole_inflight"] is not True
            or reported_crossing["release_kind"]
            != _provider_gate_crossing_release_kind(crossing_request_kind)
        ):
            raise BenchmarkToolError(
                "provider gate crossing quarantine contract changed"
            )
        if crossing_sequence in global_sequences:
            raise BenchmarkToolError("provider gate crossing reused a global sequence")
        global_sequences.add(crossing_sequence)
        global_sequence_events.append(
            (
                crossing_sequence,
                _positive_int(
                    reported_crossing["commit_monotonic_ns"],
                    "state.crossing.commit_monotonic_ns",
                ),
            )
        )

    # Replay admissions independently of the proxy's phase/invariant summary.
    commit_order = sorted(calls, key=lambda item: item["commit_monotonic_ns"])
    direct_calls = [
        call
        for call in calls
        if call["appserver_delivery"]["kind"] == "direct_raw_response"
    ]
    suppressed_calls = [
        call
        for call in calls
        if call["appserver_delivery"]["kind"]
        == "suppressed_collaboration_wait"
    ]
    superseded_calls = [
        call
        for call in calls
        if call["appserver_delivery"]["kind"]
        == "superseded_by_collaboration_message"
    ]
    discarded_calls = [
        call
        for call in calls
        if call["appserver_delivery"]["kind"]
        == "discarded_after_explicit_child_interrupt"
    ]
    calls_by_response = {call["response_id"]: call for call in calls}
    direct_by_response = {call["response_id"]: call for call in direct_calls}
    for call in suppressed_calls:
        delivery = call["appserver_delivery"]
        successor = direct_by_response.get(delivery["successor_response_id"])
        metadata = call["request_metadata"]
        if (
            successor is None
            or successor["call_id"] != delivery["successor_call_id"]
            or successor["request_metadata"]["thread_id"] != metadata["thread_id"]
            or successor["request_metadata"]["turn_id"] != metadata["turn_id"]
            or successor["request_metadata"]["request_kind"] != "turn"
            or successor["commit_monotonic_ns"] <= call["commit_monotonic_ns"]
            or successor["admitted_monotonic_ns"] <= call["commit_monotonic_ns"]
            or successor["admitted_unix_ns"] <= call["commit_unix_ns"]
        ):
            raise BenchmarkToolError(
                "suppressed provider wait lacks its later direct successor"
            )
        eligible_successors = [
            candidate
            for candidate in direct_calls
            if candidate["commit_monotonic_ns"] > call["commit_monotonic_ns"]
            and candidate["request_metadata"]["thread_id"] == metadata["thread_id"]
            and candidate["request_metadata"]["turn_id"] == metadata["turn_id"]
            and candidate["request_metadata"]["request_kind"] == "turn"
        ]
        if not eligible_successors or min(
            eligible_successors,
            key=lambda candidate: (
                candidate["commit_monotonic_ns"],
                candidate["sequence"],
            ),
        ) is not successor:
            raise BenchmarkToolError(
                "suppressed provider wait does not name the earliest direct successor"
            )
    for call in superseded_calls:
        delivery = call["appserver_delivery"]
        successor = calls_by_response.get(delivery["successor_response_id"])
        metadata = call["request_metadata"]
        eligible_successors = [
            candidate
            for candidate in calls
            if candidate is not call
            and candidate["admitted_monotonic_ns"] > call["commit_monotonic_ns"]
            and candidate["request_metadata"] == metadata
            and candidate["request_metadata"]["request_kind"] == "turn"
        ]
        if (
            successor is None
            or successor["call_id"] != delivery["successor_call_id"]
            or successor["request_metadata"] != metadata
            or successor["request_metadata"]["request_kind"] != "turn"
            or successor["appserver_delivery"]["kind"]
            not in ("direct_raw_response", "superseded_by_collaboration_message")
            or successor["admitted_unix_ns"] <= call["commit_unix_ns"]
            or not eligible_successors
            or min(
                eligible_successors,
                key=lambda candidate: (
                    candidate["admitted_monotonic_ns"],
                    candidate["sequence"],
                ),
            )
            is not successor
        ):
            raise BenchmarkToolError(
                "superseded provider response lacks its immediate same-request successor"
            )
    for origin in superseded_calls:
        cursor = origin
        seen: set[str] = set()
        while cursor["appserver_delivery"]["kind"] == (
            "superseded_by_collaboration_message"
        ):
            if cursor["response_id"] in seen:
                raise BenchmarkToolError("superseded provider chain has a cycle")
            seen.add(cursor["response_id"])
            cursor = calls_by_response[
                cursor["appserver_delivery"]["successor_response_id"]
            ]
        if cursor["appserver_delivery"]["kind"] != "direct_raw_response":
            raise BenchmarkToolError(
                "superseded provider chain does not end in direct delivery"
            )
    for call in discarded_calls:
        delivery = call["appserver_delivery"]
        interrupting = calls_by_response.get(delivery["successor_response_id"])
        interrupt_items = (
            interrupting["response_output_manifest"]["items"]
            if isinstance(interrupting, Mapping)
            else []
        )
        interrupt_functions = [
            item
            for item in interrupt_items
            if item.get("type") == "function_call"
            and item.get("name") == "interrupt_agent"
            and item.get("namespace") == "collaboration"
        ]
        provider_order_exact = isinstance(interrupting, Mapping) and all(
            max(
                call[f"admitted_{suffix}"],
                interrupting[f"admitted_{suffix}"],
            )
            < interrupting[f"commit_{suffix}"]
            < interrupting["appserver_delivery"][f"bind_{suffix}"]
            < call[f"commit_{suffix}"]
            < delivery[f"bind_{suffix}"]
            for suffix in ("unix_ns", "monotonic_ns")
        )
        if (
            interrupting is None
            or interrupting["call_id"] != delivery["successor_call_id"]
            or interrupting["appserver_delivery"]["kind"] != "direct_raw_response"
            or not provider_order_exact
            or interrupting["response_output_manifest"][
                "action_capable_item_count"
            ]
            != 1
            or len(interrupt_functions) != 1
            or any(
                item is not interrupt_functions[0]
                and item.get("type") != "reasoning"
                for item in interrupt_items
            )
        ):
            raise BenchmarkToolError(
                "interrupted-child discard lacks its exact earlier parent interrupt"
            )
    if len({item["admitted_monotonic_ns"] for item in calls}) != len(calls):
        raise BenchmarkToolError("provider gate admission order is ambiguous")
    if len({item["commit_monotonic_ns"] for item in calls}) != len(calls):
        raise BenchmarkToolError("provider gate completion order is ambiguous")
    if {
        item["admitted_monotonic_ns"] for item in calls
    } & {item["commit_monotonic_ns"] for item in calls}:
        raise BenchmarkToolError("provider gate admission/completion order is ambiguous")
    completed_before: dict[str, int] = {}
    running_total = 0
    derived_crossing: dict[str, Any] | None = None
    for call in commit_order:
        completed_before[str(call["call_id"])] = running_total
        running_total += call["normalized_usage"]["total_tokens"]
        if (
            call["previous_total"] != completed_before[str(call["call_id"])]
            or call["committed_total"] != running_total
        ):
            raise BenchmarkToolError("provider gate committed total is not reproducible")
        crossed = completed_before[str(call["call_id"])] < token_limit <= running_total
        if call["crossed_cap"] is not crossed:
            raise BenchmarkToolError("provider gate crossing flag is inconsistent")
        if crossed:
            if derived_crossing is not None:
                raise BenchmarkToolError("provider gate has more than one first crossing")
            if reported_crossing is None:
                raise BenchmarkToolError("provider gate omitted the first crossing record")
            open_at_crossing = [
                candidate
                for candidate in calls
                if candidate["admitted_monotonic_ns"] <= call["commit_monotonic_ns"]
                and candidate["commit_monotonic_ns"] >= call["commit_monotonic_ns"]
            ]
            if [item["call_id"] for item in open_at_crossing] != [call["call_id"]]:
                raise BenchmarkToolError("provider crossing was not the sole in-flight request")
            call_request_kind = call["request_metadata"]["request_kind"]
            expected_release_kind = _provider_gate_crossing_release_kind(
                call_request_kind
            )
            if (
                not isinstance(call_request_kind, str)
                or not call_request_kind
                or call["release_kind"] != expected_release_kind
                or call["appserver_delivery"]["kind"] != "direct_raw_response"
                or call["appserver_crossbind"] is None
            ):
                raise BenchmarkToolError("provider crossing response was not quarantined")
            derived_crossing = {
                "call_id": call["call_id"],
                "response_id": call["response_id"],
                "sequence": (
                    reported_crossing["sequence"]
                    if reported_crossing is not None
                    else None
                ),
                "previous_total": completed_before[str(call["call_id"])],
                "response_tokens": call["normalized_usage"]["total_tokens"],
                "completed_tokens": running_total,
                "overshoot_tokens": running_total - token_limit,
                "commit_unix_ns": call["commit_unix_ns"],
                "commit_monotonic_ns": call["commit_monotonic_ns"],
                "sole_inflight": True,
                "release_kind": expected_release_kind,
                "request_kind": call_request_kind,
            }
        elif call["release_kind"] != "byte_identity":
            raise BenchmarkToolError("provider gate sanitized a non-crossing response")

    for call in calls:
        open_before = [
            candidate
            for candidate in calls
            if candidate["call_id"] != call["call_id"]
            and candidate["admitted_monotonic_ns"] < call["admitted_monotonic_ns"]
            < candidate["commit_monotonic_ns"]
        ]
        completed_at_admission = sum(
            candidate["normalized_usage"]["total_tokens"]
            for candidate in calls
            if candidate["commit_monotonic_ns"] < call["admitted_monotonic_ns"]
        )
        if (
            call["completed_before"] != completed_at_admission
            or call["open_before"] != len(open_before)
            or call["reserved_before"]
            != completed_at_admission + len(open_before) * response_bound
            or call["reservation_after"]
            != completed_at_admission + (len(open_before) + 1) * response_bound
        ):
            raise BenchmarkToolError("provider gate admission reservation is not reproducible")
        if call["admission_mode"] == "CONCURRENT":
            if not (
                completed_at_admission
                + (len(open_before) + 1) * response_bound
                < token_limit
            ):
                raise BenchmarkToolError("provider gate violated its concurrent reservation")
        elif open_before:
            raise BenchmarkToolError("provider gate admitted concurrent exclusive work")

    if derived_crossing is None:
        if reported_crossing is not None:
            raise BenchmarkToolError("provider gate reports an unobserved crossing")
        if running_total >= token_limit:
            raise BenchmarkToolError("provider total crossed without a crossing record")
    else:
        if reported_crossing != derived_crossing:
            raise BenchmarkToolError("provider gate first-crossing record is not reproducible")
        if commit_order[-1]["call_id"] != derived_crossing["call_id"]:
            raise BenchmarkToolError("provider gate final response is not the first crossing")
        if running_total != derived_crossing["completed_tokens"]:
            raise BenchmarkToolError("provider gate drained tokens after first crossing")
    if state_completed_tokens != running_total:
        raise BenchmarkToolError("provider gate final total is not reproducible")
    if close_reason == "token_limit" and derived_crossing is None:
        raise BenchmarkToolError("token-limit gate close has no exact crossing")
    if state["crossing_closed"] is not (derived_crossing is not None):
        raise BenchmarkToolError("provider gate crossing-closed status is inconsistent")

    transitions = record["transitions"]
    if not isinstance(transitions, list) or not transitions:
        raise BenchmarkToolError("provider gate has no phase-transition ledger")
    previous_phase: str | None = None
    previous_mono = 0
    prior_transition_sequence = 0
    for index, raw_transition in enumerate(transitions):
        transition = _provider_gate_exact_keys(
            raw_transition,
            PROVIDER_GATE_TRANSITION_KEYS,
            f"transitions[{index}]",
        )
        transition_sequence = _positive_int(
            transition["sequence"], f"transitions[{index}].sequence"
        )
        if (
            transition_sequence <= prior_transition_sequence
            or transition_sequence in global_sequences
        ):
            raise BenchmarkToolError("provider gate transition sequence is not canonical")
        global_sequences.add(transition_sequence)
        prior_transition_sequence = transition_sequence
        if (
            transition["from_phase"] not in PROVIDER_GATE_PHASES
            or transition["to_phase"] not in PROVIDER_GATE_PHASES
            or transition["from_phase"] == transition["to_phase"]
            or (previous_phase is not None and transition["from_phase"] != previous_phase)
        ):
            raise BenchmarkToolError("provider gate transition chain is inconsistent")
        if index == 0 and transition["from_phase"] != "CONCURRENT":
            raise BenchmarkToolError("provider gate transition chain does not start at CONCURRENT")
        mono = _positive_int(
            transition["monotonic_ns"],
            f"transitions[{index}].monotonic_ns",
        )
        _positive_int(
            transition["unix_ns"], f"transitions[{index}].unix_ns"
        )
        if mono < previous_mono:
            raise BenchmarkToolError("provider gate transition timestamps regress")
        previous_mono = mono
        global_sequence_events.append((transition_sequence, mono))
        previous_phase = str(transition["to_phase"])
        _provider_gate_string(
            transition["reason"], f"transitions[{index}].reason"
        )
        transition_call_id = transition["call_id"]
        if transition_call_id is not None and transition_call_id not in call_ids:
            raise BenchmarkToolError("provider gate transition cites an unknown call")
        transition_edge = (transition["from_phase"], transition["to_phase"])
        if transition_edge == ("CONCURRENT", "DRAINING"):
            valid_transition = (
                transition["reason"]
                == "concurrent_reservation_would_reach_limit"
                and transition_call_id is None
            )
        elif transition_edge == ("DRAINING", "EXCLUSIVE"):
            valid_transition = (
                transition["reason"] == "concurrent_requests_drained"
                and transition_call_id is None
            )
        elif transition["to_phase"] == "CLOSED":
            if transition["reason"] == "first_token_limit_crossing":
                valid_transition = (
                    transition["from_phase"] == "EXCLUSIVE"
                    and derived_crossing is not None
                    and transition_call_id == derived_crossing["call_id"]
                    and close_reason == "token_limit"
                )
            elif transition["reason"] == "stop_without_terminal_close":
                valid_transition = (
                    transition_call_id is None and close_reason == "system_error"
                )
            else:
                valid_transition = (
                    transition["reason"] == f"terminal_close:{close_reason}"
                    and transition_call_id is None
                    and close_reason
                    in {"accepted_submission", "natural_end", "system_error"}
                )
        elif transition["to_phase"] == "POISONED":
            valid_transition = (
                transition_call_id is None
                and transition["reason"] in poison_reasons
                and close_reason == "poison"
            )
        else:
            valid_transition = False
        if not valid_transition:
            raise BenchmarkToolError(
                "provider gate transition edge/reason is not in the static state machine"
            )
    if previous_phase != phase:
        raise BenchmarkToolError("provider gate transition chain has the wrong final phase")
    for call in calls:
        phase_at_admission = "CONCURRENT"
        for transition in transitions:
            if transition["sequence"] >= call["sequence"]:
                break
            phase_at_admission = transition["to_phase"]
        if phase_at_admission != call["admission_mode"]:
            raise BenchmarkToolError(
                "provider gate admission mode disagrees with its phase history"
            )
    terminal_transitions = [
        transition
        for transition in transitions
        if isinstance(transition, Mapping)
        and transition.get("to_phase") in {"CLOSED", "POISONED"}
    ]
    if len(terminal_transitions) != 1 or terminal_transitions[0] != transitions[-1]:
        raise BenchmarkToolError("provider gate terminal transition is not unique/final")
    terminal_monotonic_ns = terminal_transitions[0]["monotonic_ns"]
    if any(call["upstream_start_monotonic_ns"] >= terminal_monotonic_ns for call in calls):
        raise BenchmarkToolError("provider gate started upstream work at/after close")

    denials = record["denials"]
    if not isinstance(denials, list):
        raise BenchmarkToolError("provider gate denials must be a list")
    denial_ids: set[str] = set()
    prior_denial_sequence = 0
    for index, raw_denial in enumerate(denials):
        denial = _provider_gate_exact_keys(
            raw_denial, PROVIDER_GATE_DENIAL_KEYS, f"denials[{index}]"
        )
        denial_sequence = _positive_int(denial["sequence"], f"denials[{index}].sequence")
        if denial_sequence <= prior_denial_sequence or denial_sequence in global_sequences:
            raise BenchmarkToolError("provider gate denial sequence is not canonical")
        global_sequences.add(denial_sequence)
        prior_denial_sequence = denial_sequence
        denial_id = _provider_gate_string(
            denial["denial_id"], f"denials[{index}].denial_id"
        )
        assert denial_id is not None
        if denial_id != f"deny-{denial_sequence:08d}":
            raise BenchmarkToolError("provider gate denial identity is not sequence-bound")
        if denial_id in denial_ids:
            raise BenchmarkToolError("provider gate has a duplicate denial identity")
        denial_ids.add(denial_id)
        _provider_gate_string(denial["method"], f"denials[{index}].method")
        _provider_gate_string(denial["route"], f"denials[{index}].route")
        _provider_gate_string(denial["reason"], f"denials[{index}].reason")
        if denial["phase"] not in PROVIDER_GATE_PHASES:
            raise BenchmarkToolError("provider gate denial has an invalid phase")
        if denial["upstream_started"] is not False:
            raise BenchmarkToolError("provider gate denial reached the upstream provider")
        denial_mono = _positive_int(
            denial["monotonic_ns"], f"denials[{index}].monotonic_ns"
        )
        global_sequence_events.append((denial_sequence, denial_mono))
        _positive_int(denial["unix_ns"], f"denials[{index}].unix_ns")
        # Codex may probe the local provider endpoint with an unmetered model-
        # catalog lookup before it has created a thread or turn.  The gate
        # rejects that setup-only request without starting upstream work, so
        # absent thread/turn metadata is expected and carries no token-accounting
        # ambiguity.  Keep inference denials strict: a denied POST /responses
        # must still be bound to a concrete thread and turn.
        setup_catalog_denial = (
            denial["method"] == "GET" and denial["route"] == "/models"
        )
        _provider_gate_metadata(
            denial["request_metadata"],
            f"denials[{index}].request_metadata",
            require_thread_turn=not setup_catalog_denial,
        )
        if (
            derived_crossing is not None
            and denial_mono >= derived_crossing["commit_monotonic_ns"]
            and denial["phase"] not in {"CLOSED", "POISONED"}
        ):
            raise BenchmarkToolError("post-cap denial was not made by a closed gate")

    if record["setup_requests"] != []:
        raise BenchmarkToolError(
            "scoreable provider gate must not forward setup or unknown routes"
        )
    ordered_global_events = sorted(global_sequence_events)
    if any(
        later_mono < earlier_mono
        for (_earlier_sequence, earlier_mono), (_later_sequence, later_mono) in zip(
            ordered_global_events, ordered_global_events[1:]
        )
    ):
        raise BenchmarkToolError("provider gate global sequence contradicts monotonic time")
    expected_final_sequence = max(global_sequences, default=0)
    if state_sequence != expected_final_sequence:
        raise BenchmarkToolError("provider gate final global sequence is inconsistent")
    if global_sequences != set(range(1, expected_final_sequence + 1)):
        raise BenchmarkToolError("provider gate global sequence ledger has an unexplained gap")

    invariants = record["invariants"]
    if (
        not isinstance(invariants, Mapping)
        or set(invariants) != PROVIDER_GATE_INVARIANT_KEYS
        or any(not isinstance(name, str) or value is not True for name, value in invariants.items())
    ):
        raise BenchmarkToolError("provider gate invariant attestations are incomplete")

    if usage is not None:
        for usage_field in (
            "response_count",
            "notification_sequence",
            "input_tokens",
            "cached_input_tokens",
            "cache_write_input_tokens",
            "output_tokens",
            "reasoning_output_tokens",
            "model_tokens",
            "pending_interrupt_response_count",
        ):
            _nonnegative_int(
                usage.get(usage_field), f"provider app-server usage.{usage_field}"
            )
        expected_event_sequences = set(range(1, len(direct_calls) + 1))
        if event_sequences != expected_event_sequences:
            raise BenchmarkToolError("provider gate app-server event ledger has gaps")
        ordered_calls = sorted(
            direct_calls,
            key=lambda item: item["appserver_crossbind"]["event_sequence"],
        )
        ordered_response_ids = [call["response_id"] for call in ordered_calls]
        provider_response_ids = [call["response_id"] for call in commit_order]
        suppressed_response_ids = [
            call["response_id"]
            for call in commit_order
            if call["appserver_delivery"]["kind"]
            == "suppressed_collaboration_wait"
        ]
        superseded_response_ids = [
            call["response_id"]
            for call in commit_order
            if call["appserver_delivery"]["kind"]
            == "superseded_by_collaboration_message"
        ]
        discarded_response_ids = [
            call["response_id"]
            for call in commit_order
            if call["appserver_delivery"]["kind"]
            == "discarded_after_explicit_child_interrupt"
        ]
        provider_sums = {
            field: sum(call["normalized_usage"][field] for call in calls)
            for field in PROVIDER_GATE_USAGE_KEYS
        }
        appserver_sums = {
            field: sum(call["normalized_usage"][field] for call in direct_calls)
            for field in PROVIDER_GATE_USAGE_KEYS
        }
        suppressed_sums = {
            field: sum(call["normalized_usage"][field] for call in suppressed_calls)
            for field in PROVIDER_GATE_USAGE_KEYS
        }
        superseded_sums = {
            field: sum(call["normalized_usage"][field] for call in superseded_calls)
            for field in PROVIDER_GATE_USAGE_KEYS
        }
        discarded_sums = {
            field: sum(call["normalized_usage"][field] for call in discarded_calls)
            for field in PROVIDER_GATE_USAGE_KEYS
        }
        if (
            not isinstance(usage.get("response_ids"), list)
            or usage["response_ids"] != provider_response_ids
            or usage.get("response_count") != len(calls)
            or usage.get("provider_response_count") != len(calls)
            or usage.get("provider_response_ids") != provider_response_ids
            or usage.get("provider_usage") != provider_sums
            or usage.get("appserver_response_count") != len(direct_calls)
            or usage.get("appserver_response_ids") != ordered_response_ids
            or usage.get("appserver_usage") != appserver_sums
            or usage.get("suppressed_collaboration_wait_response_count")
            != len(suppressed_calls)
            or usage.get("suppressed_collaboration_wait_response_ids")
            != suppressed_response_ids
            or usage.get("suppressed_collaboration_wait_usage")
            != suppressed_sums
            or usage.get("superseded_by_collaboration_message_response_count")
            != len(superseded_calls)
            or usage.get("superseded_by_collaboration_message_response_ids")
            != superseded_response_ids
            or usage.get("superseded_by_collaboration_message_usage")
            != superseded_sums
            or usage.get(
                "discarded_after_explicit_child_interrupt_response_count"
            )
            != len(discarded_calls)
            or usage.get(
                "discarded_after_explicit_child_interrupt_response_ids"
            )
            != discarded_response_ids
            or usage.get("discarded_after_explicit_child_interrupt_usage")
            != discarded_sums
            or usage.get("notification_sequence") != len(direct_calls)
            or usage.get("input_tokens") != provider_sums["input_tokens"]
            or usage.get("cached_input_tokens")
            != provider_sums["cached_input_tokens"]
            or usage.get("output_tokens") != provider_sums["output_tokens"]
            or usage.get("cache_write_input_tokens")
            != provider_sums["cache_write_input_tokens"]
            or usage.get("reasoning_output_tokens")
            != provider_sums["reasoning_output_tokens"]
            or usage.get("model_tokens") != running_total
        ):
            raise BenchmarkToolError(
                "provider gate and reconciled usage ledgers disagree"
            )
        reconciliation = usage.get("provider_usage_reconciliation")
        if (
            not isinstance(reconciliation, Mapping)
            or set(reconciliation) != set(PROVIDER_USAGE_RECONCILIATION_KEYS)
            or reconciliation.get("schema_version")
            != PROVIDER_USAGE_RECONCILIATION_SCHEMA_VERSION
            or reconciliation.get("provider_response_count") != len(calls)
            or reconciliation.get("appserver_response_count") != len(direct_calls)
            or reconciliation.get(
                "suppressed_collaboration_wait_response_count"
            )
            != len(suppressed_calls)
            or reconciliation.get("provider_usage") != provider_sums
            or reconciliation.get("appserver_usage") != appserver_sums
            or reconciliation.get("suppressed_collaboration_wait_usage")
            != suppressed_sums
            or reconciliation.get(
                "superseded_by_collaboration_message_response_count"
            )
            != len(superseded_calls)
            or reconciliation.get(
                "superseded_by_collaboration_message_usage"
            )
            != superseded_sums
            or reconciliation.get(
                "discarded_after_explicit_child_interrupt_response_count"
            )
            != len(discarded_calls)
            or reconciliation.get(
                "discarded_after_explicit_child_interrupt_usage"
            )
            != discarded_sums
            or reconciliation.get("provider_response_ids")
            != provider_response_ids
            or reconciliation.get("appserver_response_ids")
            != ordered_response_ids
            or reconciliation.get(
                "suppressed_collaboration_wait_response_ids"
            )
            != suppressed_response_ids
            or reconciliation.get(
                "superseded_by_collaboration_message_response_ids"
            )
            != superseded_response_ids
            or reconciliation.get(
                "discarded_after_explicit_child_interrupt_response_ids"
            )
            != discarded_response_ids
        ):
            raise BenchmarkToolError("provider usage reconciliation changed")
        reconciliation_evidence = reconciliation.get(
            "suppressed_collaboration_wait_evidence"
        )
        if (
            not isinstance(reconciliation_evidence, list)
            or len(reconciliation_evidence) != len(suppressed_calls)
        ):
            raise BenchmarkToolError("provider suppressed-wait evidence is incomplete")
        suppressed_by_response = {
            call["response_id"]: call for call in suppressed_calls
        }
        seen_agent_messages: set[str] = set()
        for evidence_index, evidence in enumerate(reconciliation_evidence):
            if (
                not isinstance(evidence, Mapping)
                or set(evidence)
                != set(SUPPRESSED_COLLABORATION_WAIT_EVIDENCE_KEYS)
                or evidence.get("response_id")
                != suppressed_response_ids[evidence_index]
            ):
                raise BenchmarkToolError(
                    "provider suppressed-wait evidence order/schema changed"
                )
            suppressed_call = suppressed_by_response[evidence["response_id"]]
            successor = direct_by_response.get(
                suppressed_call["appserver_delivery"]["successor_response_id"]
            )
            message_mono = _positive_int(
                evidence.get("agent_message_observed_at_monotonic_ns"),
                "suppressed evidence.agent_message_observed_at_monotonic_ns",
            )
            message_wall = _positive_int(
                evidence.get("agent_message_observed_at_unix_ns"),
                "suppressed evidence.agent_message_observed_at_unix_ns",
            )
            message_id = evidence.get("agent_message_item_id")
            message_author = evidence.get("agent_message_author")
            message_digest = evidence.get("agent_message_sha256")
            if (
                successor is None
                or evidence.get("provider_call_id") != suppressed_call["call_id"]
                or evidence.get("thread_id")
                != suppressed_call["request_metadata"]["thread_id"]
                or evidence.get("turn_id")
                != suppressed_call["request_metadata"]["turn_id"]
                or evidence.get("successor_response_id") != successor["response_id"]
                or evidence.get("successor_call_id") != successor["call_id"]
                or evidence.get("agent_message_recipient") != "/root"
                or not isinstance(message_author, str)
                or not message_author.startswith("/root/")
                or message_author == "/root/"
                or not isinstance(message_digest, str)
                or re.fullmatch(r"[0-9a-f]{64}", message_digest) is None
                or not isinstance(message_id, str)
                or not message_id
                or message_id in seen_agent_messages
                or not suppressed_call["commit_unix_ns"]
                < message_wall
                or message_wall + 1_000_000
                > successor["admitted_unix_ns"]
            ):
                raise BenchmarkToolError(
                    "provider suppressed-wait child-result evidence changed"
                )
            seen_agent_messages.add(message_id)
        superseded_reconciliation_evidence = reconciliation.get(
            "superseded_by_collaboration_message_evidence"
        )
        if (
            not isinstance(superseded_reconciliation_evidence, list)
            or len(superseded_reconciliation_evidence) != len(superseded_calls)
        ):
            raise BenchmarkToolError(
                "provider superseded-response evidence is incomplete"
            )
        superseded_by_response = {
            call["response_id"]: call for call in superseded_calls
        }
        raw_usage_threads = usage.get("thread_accounting")
        usage_threads = {
            str(thread["thread_id"]): thread
            for thread in raw_usage_threads
            if isinstance(thread, Mapping)
            and isinstance(thread.get("thread_id"), str)
        } if isinstance(raw_usage_threads, list) else {}
        for evidence_index, superseded_evidence in enumerate(
            superseded_reconciliation_evidence
        ):
            if (
                not isinstance(superseded_evidence, Mapping)
                or set(superseded_evidence)
                != set(SUPERSEDED_BY_COLLABORATION_MESSAGE_EVIDENCE_KEYS)
                or superseded_evidence.get("response_id")
                != superseded_response_ids[evidence_index]
            ):
                raise BenchmarkToolError(
                    "provider superseded-response evidence order/schema changed"
                )
            superseded_call = superseded_by_response[
                superseded_evidence["response_id"]
            ]
            successor = calls_by_response.get(
                superseded_call["appserver_delivery"]["successor_response_id"]
            )
            messages = superseded_evidence.get("collaboration_messages")
            if (
                successor is None
                or superseded_evidence.get("provider_call_id")
                != superseded_call["call_id"]
                or superseded_evidence.get("thread_id")
                != superseded_call["request_metadata"]["thread_id"]
                or superseded_evidence.get("turn_id")
                != superseded_call["request_metadata"]["turn_id"]
                or superseded_evidence.get("successor_response_id")
                != successor["response_id"]
                or superseded_evidence.get("successor_call_id")
                != successor["call_id"]
                or not isinstance(messages, list)
                or not messages
            ):
                raise BenchmarkToolError(
                    "provider superseded-response binding evidence changed"
                )
            normalized_messages: list[dict[str, Any]] = []
            for message in messages:
                message_mono = _positive_int(
                    message.get("observed_at_monotonic_ns")
                    if isinstance(message, Mapping)
                    else None,
                    "superseded evidence.message.observed_at_monotonic_ns",
                )
                message_wall = _positive_int(
                    message.get("observed_at_unix_ns")
                    if isinstance(message, Mapping)
                    else None,
                    "superseded evidence.message.observed_at_unix_ns",
                )
                if (
                    not isinstance(message, Mapping)
                    or set(message) != set(COLLABORATION_MESSAGE_EVIDENCE_KEYS)
                    or not isinstance(message.get("item_id"), str)
                    or not message["item_id"]
                    or message["item_id"] in seen_agent_messages
                    or not isinstance(message.get("item_sha256"), str)
                    or re.fullmatch(r"[0-9a-f]{64}", message["item_sha256"])
                    is None
                    or not _rooted_collaboration_route_matches(
                        thread_id=superseded_call["request_metadata"][
                            "thread_id"
                        ],
                        author=message.get("author"),
                        recipient=message.get("recipient"),
                        projected_threads=usage_threads,
                        root_thread_id=root_thread_id,
                    )
                    or not superseded_call["commit_unix_ns"]
                    < message_wall
                    or message_wall + 1_000_000
                    > successor["admitted_unix_ns"]
                ):
                    raise BenchmarkToolError(
                        "provider superseded-response child-message evidence changed"
                    )
                seen_agent_messages.add(message["item_id"])
                normalized_messages.append(dict(message))
            if normalized_messages != sorted(
                normalized_messages,
                key=lambda message: (
                    message["observed_at_unix_ns"],
                    message["item_id"],
                    message["observed_at_monotonic_ns"],
                ),
            ):
                raise BenchmarkToolError(
                    "provider superseded-response message evidence is out of order"
                )
        discarded_reconciliation_evidence = reconciliation.get(
            "discarded_after_explicit_child_interrupt_evidence"
        )
        if (
            not isinstance(discarded_reconciliation_evidence, list)
            or len(discarded_reconciliation_evidence) != len(discarded_calls)
        ):
            raise BenchmarkToolError(
                "provider explicit-child-interrupt evidence is incomplete"
            )
        discarded_by_response = {
            call["response_id"]: call for call in discarded_calls
        }
        for evidence_index, evidence in enumerate(
            discarded_reconciliation_evidence
        ):
            if (
                not isinstance(evidence, Mapping)
                or set(evidence)
                != set(DISCARDED_AFTER_EXPLICIT_CHILD_INTERRUPT_EVIDENCE_KEYS)
                or evidence.get("response_id")
                != discarded_response_ids[evidence_index]
            ):
                raise BenchmarkToolError(
                    "provider explicit-child-interrupt evidence order/schema changed"
                )
            discarded_call = discarded_by_response[evidence["response_id"]]
            delivery = discarded_call["appserver_delivery"]
            interrupting = calls_by_response.get(
                delivery["successor_response_id"]
            )
            manifest_items = (
                interrupting["response_output_manifest"]["items"]
                if isinstance(interrupting, Mapping)
                else []
            )
            function_items = [
                item
                for item in manifest_items
                if item.get("type") == "function_call"
                and item.get("name") == "interrupt_agent"
                and item.get("namespace") == "collaboration"
            ]
            child = usage_threads.get(str(evidence.get("thread_id")))
            parent = usage_threads.get(
                str(evidence.get("interrupt_parent_thread_id"))
            )
            observed_pairs: list[tuple[int, int]] = []
            for prefix in (
                "interrupt_function",
                "interrupt_activity",
                "interrupt_output",
                "interrupted_turn",
            ):
                observed_pairs.append(
                    (
                        _positive_int(
                            evidence.get(f"{prefix}_observed_at_unix_ns"),
                            f"discarded evidence.{prefix}_observed_at_unix_ns",
                        ),
                        _positive_int(
                            evidence.get(f"{prefix}_observed_at_monotonic_ns"),
                            f"discarded evidence.{prefix}_observed_at_monotonic_ns",
                        ),
                    )
                )
            digest_fields = (
                "interrupt_function_arguments_sha256",
                "interrupt_activity_item_sha256",
                "interrupt_output_item_sha256",
            )
            if (
                interrupting is None
                or len(function_items) != 1
                or evidence.get("provider_call_id")
                != discarded_call["call_id"]
                or evidence.get("thread_id")
                != discarded_call["request_metadata"]["thread_id"]
                or evidence.get("turn_id")
                != discarded_call["request_metadata"]["turn_id"]
                or evidence.get("interrupting_response_id")
                != interrupting["response_id"]
                or evidence.get("interrupting_provider_call_id")
                != interrupting["call_id"]
                or evidence.get("interrupting_response_id")
                != delivery["successor_response_id"]
                or evidence.get("interrupting_provider_call_id")
                != delivery["successor_call_id"]
                or evidence.get("interrupt_function_item_id")
                != function_items[0].get("id")
                or evidence.get("interrupt_function_call_id")
                != function_items[0].get("call_id")
                or evidence.get("interrupt_function_arguments_sha256")
                != function_items[0].get("arguments_sha256")
                or evidence.get("interrupt_parent_thread_id")
                != interrupting["request_metadata"]["thread_id"]
                or evidence.get("interrupt_parent_turn_id")
                != interrupting["request_metadata"]["turn_id"]
                or not isinstance(child, Mapping)
                or not isinstance(parent, Mapping)
                or child.get("parent_thread_id")
                != evidence.get("interrupt_parent_thread_id")
                or child.get("agent_path")
                != evidence.get("interrupted_agent_path")
                or evidence.get("interrupt_function_item_id")
                == evidence.get("interrupt_output_item_id")
                or any(
                    not isinstance(evidence.get(field), str)
                    or re.fullmatch(r"[0-9a-f]{64}", evidence[field]) is None
                    for field in digest_fields
                )
                or interrupting["commit_unix_ns"] >= observed_pairs[0][0]
                or any(
                    discarded_call["admitted_unix_ns"] >= wall_ns
                    or
                    wall_ns + 1_000_000 > discarded_call["commit_unix_ns"]
                    for wall_ns, mono_ns in observed_pairs
                )
            ):
                raise BenchmarkToolError(
                    "provider explicit-child-interrupt binding evidence changed"
                )
        if (
            usage.get("interrupt_requested") is not False
            or usage.get("pending_interrupt_response_count") != 0
            or usage.get("invalid_reasons") != []
            or usage.get("measurement_exact") is not True
        ):
            raise BenchmarkToolError("provider gate attempt used an interrupt or invalid ledger")
        response_ledger = usage.get("appserver_response_ledger")
        if (
            not isinstance(response_ledger, list)
            or len(response_ledger) != len(direct_calls)
        ):
            raise BenchmarkToolError("provider gate lacks the exact app-server response ledger")
        calls_by_response = {call["response_id"]: call for call in calls}
        for index, response in enumerate(response_ledger):
            if (
                not isinstance(response, Mapping)
                or set(response) != ULTRA_RESPONSE_LEDGER_KEYS
            ):
                raise BenchmarkToolError("provider gate response ledger entry is malformed")
            response_id = response.get("response_id")
            call = calls_by_response.get(response_id)
            if call is None:
                raise BenchmarkToolError("provider gate response ledger cites an unknown response")
            crossbind = call["appserver_crossbind"]
            if (
                response.get("raw_response_notification_sequence") != index + 1
                or response_id != ordered_response_ids[index]
                or response.get("thread_id") != crossbind["thread_id"]
                or response.get("turn_id") != crossbind["turn_id"]
                or response.get("raw_response_notification_sequence")
                != crossbind["event_sequence"]
                or not _provider_gate_same_json(
                    response.get("usage"), call["normalized_usage"]
                )
                or not _provider_gate_same_json(
                    response.get("provider_gate_call"), call
                )
                or not isinstance(response.get("raw_response_observed_at_monotonic_ns"), int)
                or isinstance(response.get("raw_response_observed_at_monotonic_ns"), bool)
                or crossbind["bind_monotonic_ns"]
                > response["raw_response_observed_at_monotonic_ns"]
                or not isinstance(response.get("raw_response_observed_at_unix_ns"), int)
                or isinstance(response.get("raw_response_observed_at_unix_ns"), bool)
                or crossbind["bind_unix_ns"] > response["raw_response_observed_at_unix_ns"]
            ):
                raise BenchmarkToolError("provider gate app-server response crossbinding changed")
        gate_summary = usage.get("provider_token_gate")
        if (
            not isinstance(gate_summary, Mapping)
            or set(gate_summary) != ULTRA_PROVIDER_GATE_SUMMARY_KEYS
            or gate_summary.get("enabled") is not True
            or type(gate_summary.get("response_token_bound")) is not int
            or gate_summary.get("response_token_bound") != response_bound
            or gate_summary.get("artifact_path") != str(path)
            or gate_summary.get("record_sha256") != record["record_sha256"]
            or gate_summary.get("final_attached") is not True
            or gate_summary.get("exact_for_usage") is not True
            or not _provider_gate_same_json(gate_summary.get("terminal"), state)
        ):
            raise BenchmarkToolError("app-server usage did not attach the exact sealed gate")
        teardown = usage.get("adapter_teardown")
        if (
            not isinstance(teardown, Mapping)
            or set(teardown) != ULTRA_ADAPTER_TEARDOWN_KEYS
            or teardown.get("process_group_isolated") is not True
            or teardown.get("stdin_closed") is not True
            or teardown.get("completed") is not True
            or teardown.get("immediate")
            is not (close_reason != "natural_end")
            or not isinstance(teardown.get("returncode"), int)
            or isinstance(teardown.get("returncode"), bool)
        ):
            raise BenchmarkToolError("app-server process group lacks clean teardown evidence")
        for clock in ("unix", "monotonic"):
            teardown_started = _positive_int(
                teardown.get(f"started_at_{clock}_ns"),
                f"usage.adapter_teardown.started_at_{clock}_ns",
            )
            teardown_completed = _positive_int(
                teardown.get(f"completed_at_{clock}_ns"),
                f"usage.adapter_teardown.completed_at_{clock}_ns",
            )
            if teardown_completed < teardown_started:
                raise BenchmarkToolError("app-server teardown timestamps regress")
        usage_crossing = usage.get("first_crossing")
        if derived_crossing is None:
            if usage_crossing is not None:
                raise BenchmarkToolError("app-server usage reports a gate-absent crossing")
        elif (
            not isinstance(usage_crossing, Mapping)
            or usage_crossing.get("tokens") != derived_crossing["completed_tokens"]
            or usage.get("stop_reason") != "token_limit"
            or usage.get("measurement_exact") is not True
            or usage.get("interrupt_requested") is not False
        ):
            raise BenchmarkToolError("app-server token crossing is not gate-crossbound")

    return {
        "path": str(path),
        "file_sha256": hashlib.sha256(payload).hexdigest(),
        "record_sha256": record["record_sha256"],
        "size_bytes": len(payload),
        "mode": "0444",
        "authenticated": True,
        "record": {
            **record,
            "calls": calls,
            "state": {**state, "crossing": derived_crossing},
        },
        "derived": {
            "completed_tokens": running_total,
            "response_count": len(calls),
            "response_ids": [call["response_id"] for call in commit_order],
            "provider_response_count": len(calls),
            "provider_response_ids": [
                call["response_id"] for call in commit_order
            ],
            "appserver_response_count": len(direct_calls),
            "appserver_response_ids": [
                call["response_id"]
                for call in sorted(
                    direct_calls,
                    key=lambda item: item["appserver_crossbind"]["event_sequence"],
                )
            ],
            "suppressed_collaboration_wait_response_count": len(
                suppressed_calls
            ),
            "suppressed_collaboration_wait_response_ids": [
                call["response_id"] for call in commit_order
                if call["appserver_delivery"]["kind"]
                == "suppressed_collaboration_wait"
            ],
            "superseded_by_collaboration_message_response_count": len(
                superseded_calls
            ),
            "superseded_by_collaboration_message_response_ids": [
                call["response_id"]
                for call in commit_order
                if call["appserver_delivery"]["kind"]
                == "superseded_by_collaboration_message"
            ],
            "discarded_after_explicit_child_interrupt_response_count": len(
                discarded_calls
            ),
            "discarded_after_explicit_child_interrupt_response_ids": [
                call["response_id"] for call in commit_order
                if call["appserver_delivery"]["kind"]
                == "discarded_after_explicit_child_interrupt"
            ],
            "first_crossing": derived_crossing,
            "poisoned": phase == "POISONED",
            "appserver_deliveries_reconciled": usage is not None,
        },
    }


def authenticate_provider_gate_live_crossing(
    path: Path,
    *,
    token_limit: int,
    run_id: str,
    model: str,
    reasoning_effort: str,
    root_thread_id: str,
    prompt_release_sha256: str,
    prompt_release_protocol: str,
    prompt_sha256: str,
    model_catalog_sha256: str,
    model_entry_sha256: str,
    expected_transport_provenance: Mapping[str, Any],
    expected_source_sha256: str,
) -> dict[str, Any] | None:
    """Authenticate only the provisional CROSS_COMMIT needed for wall ordering.

    A live record can stop the runner from killing a pre-wall crossing while the
    adapter waits for app-server crossbinding.  It can never make an attempt
    scoreable; the finalized artifact is re-read and fully replayed separately.
    """

    if not path.is_file():
        return None
    record, payload = _read_provider_gate_json(path, sealed=False)
    if (
        type(record["schema_version"]) is not int
        or record["schema_version"] != PROVIDER_GATE_SCHEMA_VERSION
        or record["protocol"] != PROVIDER_GATE_PROTOCOL
        or record["canonical_encoding"] != PROVIDER_GATE_CANONICAL_ENCODING
        or record["sealed_mode"] != "0600-live"
    ):
        raise BenchmarkToolError("live provider gate has the wrong static protocol")
    state = _provider_gate_exact_keys(
        record["state"], PROVIDER_GATE_STATE_KEYS, "live.state"
    )
    raw_crossing = state["crossing"]
    if raw_crossing is None:
        return None
    if record["setup_requests"] != []:
        raise BenchmarkToolError("live provider gate forwarded a setup route")
    implementation = _provider_gate_exact_keys(
        record["implementation"],
        PROVIDER_GATE_IMPLEMENTATION_KEYS,
        "live.implementation",
    )
    if (
        implementation["name"] != PROVIDER_GATE_IMPLEMENTATION_NAME
        or implementation["version"] != PROVIDER_GATE_IMPLEMENTATION_VERSION
        or _provider_gate_sha256(
            implementation["source_sha256"], "live.implementation.source_sha256"
        )
        != expected_source_sha256
    ):
        raise BenchmarkToolError("live provider gate implementation source changed")
    configuration, _response_bound = _validate_provider_gate_configuration(
        record["configuration"],
        field="live.configuration",
        token_limit=token_limit,
        model_catalog_sha256=model_catalog_sha256,
        model_entry_sha256=model_entry_sha256,
        expected_transport_provenance=expected_transport_provenance,
    )
    expected_bindings = {
        "root_thread_id": root_thread_id,
        "run_id": run_id,
        "model": model,
        "reasoning_effort": reasoning_effort,
        "prompt_release_sha256": prompt_release_sha256,
        "prompt_release_protocol": prompt_release_protocol,
        "prompt_sha256": prompt_sha256,
    }
    if _provider_gate_exact_keys(
        record["bindings"], PROVIDER_GATE_BINDING_KEYS, "live.bindings"
    ) != expected_bindings:
        raise BenchmarkToolError("live provider gate bindings disagree")
    crossing = _provider_gate_exact_keys(
        raw_crossing, PROVIDER_GATE_CROSSING_KEYS, "live.state.crossing"
    )
    completed = _nonnegative_int(
        crossing["completed_tokens"], "live.state.crossing.completed_tokens"
    )
    previous = _nonnegative_int(
        crossing["previous_total"], "live.state.crossing.previous_total"
    )
    response_tokens = _nonnegative_int(
        crossing["response_tokens"], "live.state.crossing.response_tokens"
    )
    overshoot = _nonnegative_int(
        crossing["overshoot_tokens"], "live.state.crossing.overshoot_tokens"
    )
    crossing_request_kind = _provider_gate_string(
        crossing["request_kind"], "live.state.crossing.request_kind"
    )
    expected_crossing_release = _provider_gate_crossing_release_kind(
        crossing_request_kind
    )
    state_completed = _nonnegative_int(
        state["completed_tokens"], "live.state.completed_tokens"
    )
    if (
        state["phase"] != "CLOSED"
        or state["close_reason"] != "token_limit"
        or state["crossing_closed"] is not True
        or state_completed != completed
        or state["open_request_ids"] != []
        or state["poisoned"] is not False
        or state["poison_reasons"] != []
        or state["no_post_close_upstream"] is not True
        or crossing["sole_inflight"] is not True
        or crossing["release_kind"] != expected_crossing_release
        or previous >= token_limit
        or completed < token_limit
        or previous + response_tokens != completed
        or overshoot != completed - token_limit
    ):
        raise BenchmarkToolError("live provider gate crossing is inconsistent")
    call_id = _provider_gate_string(crossing["call_id"], "live.crossing.call_id")
    response_id = _provider_gate_string(
        crossing["response_id"], "live.crossing.response_id"
    )
    sequence = _positive_int(crossing["sequence"], "live.crossing.sequence")
    commit_mono = _positive_int(
        crossing["commit_monotonic_ns"], "live.crossing.commit_monotonic_ns"
    )
    commit_wall = _positive_int(
        crossing["commit_unix_ns"], "live.crossing.commit_unix_ns"
    )
    matching_calls = [
        call
        for call in record["calls"]
        if isinstance(call, Mapping) and call.get("call_id") == call_id
    ] if isinstance(record["calls"], list) else []
    if len(matching_calls) != 1:
        raise BenchmarkToolError("live provider gate crossing call is absent")
    call = _provider_gate_exact_keys(
        matching_calls[0], PROVIDER_GATE_CALL_KEYS, "live.crossing.call"
    )
    call_metadata = _provider_gate_metadata(
        call["request_metadata"], "live.crossing.call.request_metadata"
    )
    if any(
        call_metadata[name] is None for name in PROVIDER_GATE_REQUEST_METADATA_KEYS
    ):
        raise BenchmarkToolError("live crossing lacks pinned app-server request metadata")
    _provider_gate_credential_headers(
        call["credential_headers_present"],
        "live.crossing.call.credential_headers_present",
    )
    call_sequence = _positive_int(
        call["sequence"], "live.crossing.call.sequence"
    )
    call_previous = _nonnegative_int(
        call["previous_total"], "live.crossing.call.previous_total"
    )
    call_committed = _nonnegative_int(
        call["committed_total"], "live.crossing.call.committed_total"
    )
    call_commit_mono = _positive_int(
        call["commit_monotonic_ns"], "live.crossing.call.commit_monotonic_ns"
    )
    call_commit_wall = _positive_int(
        call["commit_unix_ns"], "live.crossing.call.commit_unix_ns"
    )
    call_bound = _positive_int(
        call["response_bound"], "live.crossing.call.response_bound"
    )
    _provider_gate_sha256(
        call["request_body_sha256"], "live.crossing.call.request_body_sha256"
    )
    _positive_int(call["request_bytes"], "live.crossing.call.request_bytes")
    call["upstream_body_sha256"] = _provider_gate_sha256(
        call["upstream_body_sha256"], "live.crossing.call.upstream_body_sha256"
    )
    call["upstream_body_bytes"] = _positive_int(
        call["upstream_body_bytes"], "live.crossing.call.upstream_body_bytes"
    )
    call["upstream_sse_authentication"] = (
        _validate_provider_gate_sse_authentication(
            call,
            field="live.crossing.call",
        )
    )
    normalized = _provider_gate_usage(
        call["normalized_usage"], "live.crossing.call.normalized_usage"
    )
    if _normalize_provider_api_usage(
        call["usage"], "live.crossing.call.usage"
    ) != normalized:
        raise BenchmarkToolError("live provider gate normalized usage disagrees")
    _validate_provider_gate_sanitized_release(
        call, call["usage"], field="live.crossing.call"
    )
    if (
        call["response_id"] != response_id
        or call_sequence >= sequence
        or call_previous != previous
        or call_committed != completed
        or call_commit_mono != commit_mono
        or call_commit_wall != commit_wall
        or call["method"] != "POST"
        or call["route"] != "/responses"
        or call["request_model"] != model
        or call["request_stream"] is not True
        or call["admission_mode"] != "EXCLUSIVE"
        or call_bound != configuration["response_bound"]
        or call["upstream_started"] is not True
        or type(call["upstream_status"]) is not int
        or call["upstream_status"] != 200
        or call["crossed_cap"] is not True
        or call["release_kind"] != expected_crossing_release
        or call_metadata["request_kind"] != crossing_request_kind
        or normalized["total_tokens"] != response_tokens
        or normalized["total_tokens"] > configuration["response_bound"]
    ):
        raise BenchmarkToolError("live provider gate crossing/call binding disagrees")
    return {
        "path": str(path),
        "file_sha256": hashlib.sha256(payload).hexdigest(),
        "record_sha256": record["record_sha256"],
        "crossing": crossing,
        "authenticated": True,
        "scoreable": False,
    }


def validate_provider_gate_outcome(
    gate: Mapping[str, Any],
    *,
    token_limited: bool,
    accepted_request: Mapping[str, Any] | None,
    natural_end: bool = False,
    timed_out: bool = False,
) -> None:
    """Bind the terminal gate close to the winning benchmark endpoint."""

    record = gate.get("record")
    if not isinstance(record, Mapping):
        raise BenchmarkToolError("authenticated provider gate has no record")
    state = record.get("state")
    calls = record.get("calls")
    transitions = record.get("transitions")
    if not isinstance(state, Mapping) or not isinstance(calls, list) or not isinstance(
        transitions, list
    ):
        raise BenchmarkToolError("authenticated provider gate has no terminal ledger")
    if token_limited:
        crossing = state.get("crossing")
        crossing_calls = [
            call
            for call in calls
            if isinstance(call, Mapping)
            and isinstance(crossing, Mapping)
            and call.get("response_id") == crossing.get("response_id")
        ]
        close_transitions = [
            transition
            for transition in transitions
            if isinstance(transition, Mapping)
            and transition.get("to_phase") == "CLOSED"
            and transition.get("reason") == "first_token_limit_crossing"
        ]
        if (
            state.get("phase") != "CLOSED"
            or state.get("close_reason") != "token_limit"
            or not isinstance(crossing, Mapping)
            or state.get("open_request_ids") != []
            or accepted_request is not None
            or len(close_transitions) != 1
            or len(crossing_calls) != 1
            or crossing_calls[0].get("appserver_delivery", {}).get("kind")
            != "direct_raw_response"
            or not isinstance(crossing_calls[0].get("appserver_crossbind"), Mapping)
            or close_transitions[0].get("call_id") != crossing.get("call_id")
            or not isinstance(close_transitions[0].get("sequence"), int)
            or isinstance(close_transitions[0].get("sequence"), bool)
            or close_transitions[0]["sequence"] <= crossing.get("sequence", 0)
        ):
            raise BenchmarkToolError("TOKEN_LIMIT is not an exact CLOSED gate crossing")
        return
    if timed_out:
        if accepted_request is not None:
            raise BenchmarkToolError("wall-time outcome conflicts with an accepted proof")
        return
    if accepted_request is None:
        if state.get("crossing") is not None:
            raise BenchmarkToolError("non-token outcome retained a provider crossing")
        if natural_end:
            closes = [
                transition
                for transition in transitions
                if isinstance(transition, Mapping)
                and transition.get("to_phase") == "CLOSED"
                and transition.get("reason") == "terminal_close:natural_end"
            ]
            if (
                state.get("phase") != "CLOSED"
                or state.get("close_reason") != "natural_end"
                or state.get("open_request_ids") != []
                or len(closes) != 1
                or closes[0].get("call_id") is not None
            ):
                raise BenchmarkToolError(
                    "natural Ultra completion lacks an exact natural-end gate close"
                )
        return

    if (
        state.get("phase") != "CLOSED"
        or state.get("close_reason") != "accepted_submission"
        or state.get("crossing") is not None
        or state.get("crossing_closed") is not False
        or state.get("open_request_ids") != []
        or state.get("poisoned") is not False
    ):
        raise BenchmarkToolError(
            "accepted proof lacks an atomic zero-open accepted-submission gate close"
        )
    response_id = accepted_request.get("response_id")
    matching = [
        call
        for call in calls
        if isinstance(call, Mapping) and call.get("response_id") == response_id
    ]
    if len(matching) != 1:
        raise BenchmarkToolError("accepted proof response is absent from provider gate")
    call = matching[0]
    crossbind = call.get("appserver_crossbind")
    delivery = call.get("appserver_delivery")
    request_published_ns = _positive_int(
        accepted_request.get("request_published_at_monotonic_ns"),
        "accepted_request.request_published_at_monotonic_ns",
    )
    request_published_unix_ns = _positive_int(
        accepted_request.get("request_published_at_unix_ns"),
        "accepted_request.request_published_at_unix_ns",
    )
    if (
        call.get("crossed_cap") is not False
        or call.get("release_kind") != "byte_identity"
        or call.get("client_release_complete") is not True
        or call.get("commit_monotonic_ns") is None
        or call["commit_monotonic_ns"] >= request_published_ns
        or call.get("commit_unix_ns") is None
        or call["commit_unix_ns"] >= request_published_unix_ns
        or not isinstance(crossbind, Mapping)
        or not isinstance(delivery, Mapping)
        or delivery.get("kind") != "direct_raw_response"
        or delivery.get("successor_call_id") is not None
        or delivery.get("successor_response_id") is not None
        or crossbind.get("event_sequence")
        != accepted_request.get("raw_response_notification_sequence")
        or any(
            isinstance(candidate, Mapping)
            and isinstance(candidate.get("admitted_monotonic_ns"), int)
            and not isinstance(candidate.get("admitted_monotonic_ns"), bool)
            and candidate["admitted_monotonic_ns"] >= request_published_ns
            for candidate in calls
        )
        or any(
            isinstance(candidate, Mapping)
            and isinstance(candidate.get("admitted_unix_ns"), int)
            and not isinstance(candidate.get("admitted_unix_ns"), bool)
            and candidate["admitted_unix_ns"] >= request_published_unix_ns
            for candidate in calls
        )
        or any(
            not isinstance(candidate, Mapping)
            or not isinstance(candidate.get("upstream_start_monotonic_ns"), int)
            or isinstance(candidate.get("upstream_start_monotonic_ns"), bool)
            or candidate["upstream_start_monotonic_ns"] > request_published_ns
            or not isinstance(candidate.get("commit_monotonic_ns"), int)
            or isinstance(candidate.get("commit_monotonic_ns"), bool)
            or candidate["commit_monotonic_ns"] > request_published_ns
            or not isinstance(candidate.get("upstream_start_unix_ns"), int)
            or isinstance(candidate.get("upstream_start_unix_ns"), bool)
            or candidate["upstream_start_unix_ns"] > request_published_unix_ns
            or not isinstance(candidate.get("commit_unix_ns"), int)
            or isinstance(candidate.get("commit_unix_ns"), bool)
            or candidate["commit_unix_ns"] > request_published_unix_ns
            for candidate in calls
        )
    ):
        raise BenchmarkToolError(
            "accepted proof was not fully committed before its gate close"
        )
    close_transitions = [
        transition
        for transition in transitions
        if isinstance(transition, Mapping)
        and transition.get("to_phase") == "CLOSED"
        and transition.get("reason") == "terminal_close:accepted_submission"
    ]
    if len(close_transitions) != 1:
        raise BenchmarkToolError("accepted-submission gate close transition is absent")
    close_transition = close_transitions[0]
    gate_close = accepted_request.get("provider_gate_close")
    if (
        close_transition.get("monotonic_ns") is None
        or close_transition["monotonic_ns"] <= request_published_ns
        or close_transition.get("unix_ns") is None
        or close_transition["unix_ns"] <= request_published_unix_ns
        or close_transition.get("call_id") is not None
        or not isinstance(gate_close, Mapping)
        or set(gate_close)
        != {"won", "requested_reason", "effective_reason", "phase", "sequence"}
        or gate_close.get("won") is not True
        or gate_close.get("requested_reason") != "accepted_submission"
        or gate_close.get("effective_reason") != "accepted_submission"
        or gate_close.get("phase") != "CLOSED"
        or gate_close.get("sequence") != close_transition.get("sequence")
    ):
        raise BenchmarkToolError("accepted-submission close has the wrong event order")


def _prompt_common_identity(
    args: argparse.Namespace,
    *,
    run_id: str,
    nonce: str,
    root_thread_id: str,
    effective_prompt_sha256: str,
    effective_prompt_bytes: int,
) -> dict[str, Any]:
    return {
        "schema_version": PROMPT_RELEASE_SCHEMA_VERSION,
        "protocol_version": PROMPT_RELEASE_PROTOCOL_VERSION,
        "handshake_nonce": nonce,
        "run_id": run_id,
        "condition": args.condition,
        "model": args.model,
        "reasoning_effort": args.reasoning_effort,
        "root_thread_id": root_thread_id,
        "turn_start_request_id": TURN_START_REQUEST_ID,
        "effective_prompt_sha256": effective_prompt_sha256,
        "effective_prompt_bytes": effective_prompt_bytes,
        "adapter_name": PROMPT_RELEASE_ADAPTER_NAME,
        "adapter_version": PROMPT_RELEASE_ADAPTER_VERSION,
        "app_server_client_name": APP_SERVER_CLIENT_NAME,
        "app_server_client_version": APP_SERVER_CLIENT_VERSION,
        "elapsed_clock": "CLOCK_MONOTONIC",
    }


def _remove_prompt_handshake_stale_artifacts(
    paths: Mapping[str, Path], logs_dir: Path
) -> list[str]:
    """Remove only exact per-attempt stale handshake paths before Popen."""

    removed: list[str] = []
    trusted = logs_dir.resolve()
    for path in paths.values():
        if not path.is_absolute() or path.parent != trusted:
            raise BenchmarkToolError("prompt-handshake path is outside trusted logs")
        candidates = [path]
        candidates.extend(path.parent.glob(f".{path.name}.*.tmp"))
        for candidate in candidates:
            try:
                details = candidate.lstat()
            except FileNotFoundError:
                continue
            if stat.S_ISDIR(details.st_mode) and not stat.S_ISLNK(details.st_mode):
                raise BenchmarkToolError(
                    "stale prompt-handshake artifact is an unsafe directory"
                )
            candidate.unlink()
            removed.append(str(candidate))
    return sorted(set(removed))


def _validate_prompt_handshake_command(
    command: Sequence[str],
    *,
    paths: Mapping[str, Path],
    nonce: str,
    run_id: str,
) -> None:
    expected = {
        "--prompt-ready-output": str(paths["ready"]),
        "--prompt-go-input": str(paths["go"]),
        "--prompt-release-output": str(paths["release"]),
        "--prompt-handshake-nonce": nonce,
        "--prompt-run-id": run_id,
    }
    for option, value in expected.items():
        actual = _command_option_value(command, option, required=True)
        if actual != value:
            raise BenchmarkToolError(
                f"agent command {option} disagrees with the trusted runner"
            )


def _prompt_artifact_descriptor(
    path: Path, record: Mapping[str, Any], hash_field: str
) -> dict[str, Any]:
    try:
        details = path.lstat()
    except OSError as error:
        raise BenchmarkToolError("prompt-handshake artifact disappeared") from error
    if (
        not stat.S_ISREG(details.st_mode)
        or stat.S_ISLNK(details.st_mode)
        or stat.S_IMODE(details.st_mode) != 0o444
    ):
        raise BenchmarkToolError(
            "prompt-handshake artifact is not a sealed 0444 regular file"
        )
    digest = record.get(hash_field)
    if not isinstance(digest, str):
        raise BenchmarkToolError("prompt-handshake record lacks its self-hash")
    return {
        "path": str(path),
        "file_sha256": sha256_file(path),
        "record_sha256": digest,
        "record": dict(record),
    }


def _authenticate_prompt_ready(
    path: Path,
    args: argparse.Namespace,
    *,
    run_id: str,
    nonce: str,
    effective_prompt_sha256: str,
    effective_prompt_bytes: int,
    process_started_monotonic_ns: int,
) -> dict[str, Any]:
    try:
        ready = read_authenticated_record_file(path, "ready_sha256")
    except (OSError, RuntimeError) as error:
        raise BenchmarkToolError(f"invalid prompt READY artifact: {error}") from error
    root_thread_id = ready.get("root_thread_id")
    if not isinstance(root_thread_id, str) or not root_thread_id:
        raise BenchmarkToolError("prompt READY has no root thread id")
    expected = {
        **_prompt_common_identity(
            args,
            run_id=run_id,
            nonce=nonce,
            root_thread_id=root_thread_id,
            effective_prompt_sha256=effective_prompt_sha256,
            effective_prompt_bytes=effective_prompt_bytes,
        ),
        "kind": PROMPT_READY_KIND,
        "turn_start_write_state": "not_started",
        "ready_at_monotonic_ns": ready.get("ready_at_monotonic_ns"),
        "ready_at_unix_ns": ready.get("ready_at_unix_ns"),
    }
    if set(ready) != set(expected) | {"ready_sha256"} or any(
        ready.get(field) != value for field, value in expected.items()
    ):
        raise BenchmarkToolError("prompt READY identity or fields are inconsistent")
    ready_mono = ready.get("ready_at_monotonic_ns")
    ready_wall = ready.get("ready_at_unix_ns")
    now = time.monotonic_ns()
    if (
        not isinstance(ready_mono, int)
        or isinstance(ready_mono, bool)
        or ready_mono < process_started_monotonic_ns
        or ready_mono > now
        or not isinstance(ready_wall, int)
        or isinstance(ready_wall, bool)
        or ready_wall <= 0
    ):
        raise BenchmarkToolError("prompt READY timestamps are invalid")
    return ready


def _make_prompt_go(
    path: Path,
    ready: Mapping[str, Any],
) -> dict[str, Any]:
    common_fields = (
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
    authorized_at_monotonic_ns = time.monotonic_ns()
    authorized_at_unix_ns = time.time_ns()
    return write_authenticated_record_atomic(
        path,
        {
            **{field: ready[field] for field in common_fields},
            "kind": PROMPT_GO_KIND,
            "ready_sha256": ready["ready_sha256"],
            "turn_start_write_authorized": True,
            "authorized_at_monotonic_ns": authorized_at_monotonic_ns,
            "authorized_at_unix_ns": authorized_at_unix_ns,
        },
        "go_sha256",
    )


def _authenticate_prompt_release(
    path: Path,
    args: argparse.Namespace,
    *,
    run_id: str,
    nonce: str,
    ready: Mapping[str, Any],
    go: Mapping[str, Any],
    effective_prompt: str,
) -> dict[str, Any]:
    try:
        released = read_authenticated_record_file(path, "release_sha256")
    except (OSError, RuntimeError) as error:
        raise BenchmarkToolError(f"invalid prompt RELEASED artifact: {error}") from error
    effective_bytes = effective_prompt.encode("utf-8")
    common = _prompt_common_identity(
        args,
        run_id=run_id,
        nonce=nonce,
        root_thread_id=str(ready["root_thread_id"]),
        effective_prompt_sha256=hashlib.sha256(effective_bytes).hexdigest(),
        effective_prompt_bytes=len(effective_bytes),
    )
    request = prompt_turn_start_request(
        prompt=effective_prompt,
        root_thread_id=str(ready["root_thread_id"]),
        model=args.model,
        reasoning_effort=args.reasoning_effort,
    )
    wire = canonical_protocol_wire(request)
    variable_fields = (
        "released_at_monotonic_ns",
        "released_at_unix_ns",
        "turn_start_flushed_at_monotonic_ns",
        "turn_start_flushed_at_unix_ns",
    )
    expected = {
        **common,
        "kind": PROMPT_RELEASED_KIND,
        "ready_sha256": ready["ready_sha256"],
        "go_sha256": go["go_sha256"],
        "turn_start_write_state": "flushed",
        "timestamp_capture_point": "immediately_before_turn_start_write",
        "turn_start_request_sha256": hashlib.sha256(wire).hexdigest(),
        "turn_start_request_bytes": len(wire),
        **{field: released.get(field) for field in variable_fields},
    }
    if set(released) != set(expected) | {"release_sha256"} or any(
        released.get(field) != value for field, value in expected.items()
    ):
        raise BenchmarkToolError("prompt RELEASED identity or fields are inconsistent")
    release_mono = released.get("released_at_monotonic_ns")
    release_wall = released.get("released_at_unix_ns")
    flushed_mono = released.get("turn_start_flushed_at_monotonic_ns")
    flushed_wall = released.get("turn_start_flushed_at_unix_ns")
    now = time.monotonic_ns()
    if (
        any(
            not isinstance(value, int) or isinstance(value, bool) or value <= 0
            for value in (release_mono, release_wall, flushed_mono, flushed_wall)
        )
        or release_mono < go["authorized_at_monotonic_ns"]
        or release_mono < ready["ready_at_monotonic_ns"]
        or flushed_mono < release_mono
        or flushed_mono > now
        or flushed_wall < release_wall
    ):
        raise BenchmarkToolError("prompt RELEASED timestamps are invalid")
    return released


def _elapsed_from_prompt_release(released_at_monotonic_ns: int) -> float:
    now = time.monotonic_ns()
    if now < released_at_monotonic_ns:
        raise BenchmarkToolError("local monotonic clock predates prompt release")
    return (now - released_at_monotonic_ns) / 1_000_000_000


def _prompt_release_run_record(
    *,
    required: bool,
    status: str,
    authenticated: bool,
    timing_exact: bool,
    useful_work_basis: str,
    startup_timeout_seconds: float,
    startup_timeout_triggered: bool,
    nonce: str,
    paths: Mapping[str, Path] | None,
    effective_prompt_sha256: str | None,
    effective_prompt_bytes: int | None,
    ready_descriptor: Mapping[str, Any] | None,
    go_descriptor: Mapping[str, Any] | None,
    released_descriptor: Mapping[str, Any] | None,
    stale_artifacts_removed: Sequence[str],
    error: str | None,
) -> dict[str, Any]:
    return {
        "schema_version": PROMPT_RELEASE_SCHEMA_VERSION,
        "protocol_version": PROMPT_RELEASE_PROTOCOL_VERSION,
        "required": required,
        "status": status,
        "authenticated": authenticated,
        "timing_exact": timing_exact,
        "useful_work_basis": useful_work_basis,
        "startup_timeout_seconds": startup_timeout_seconds,
        "startup_timeout_triggered": startup_timeout_triggered,
        "go_minimum_release_window_seconds": (
            PROMPT_GO_MINIMUM_RELEASE_WINDOW_SECONDS
        ),
        "handshake_nonce": nonce,
        "elapsed_clock": "CLOCK_MONOTONIC",
        "artifact_paths": (
            {name: str(path) for name, path in paths.items()}
            if paths is not None
            else None
        ),
        "effective_prompt_sha256": effective_prompt_sha256,
        "effective_prompt_bytes": effective_prompt_bytes,
        "ready": dict(ready_descriptor) if ready_descriptor is not None else None,
        "go": dict(go_descriptor) if go_descriptor is not None else None,
        "released": (
            dict(released_descriptor) if released_descriptor is not None else None
        ),
        "stale_artifacts_removed": list(stale_artifacts_removed),
        "error": error,
    }


def wait_for_usage_after_acceptance(
    process: subprocess.Popen[Any],
    usage_path: Path | None,
    existing_usage: dict[str, Any] | None,
    *,
    submission_detected_at_unix_ns: int,
    grace_seconds: float,
    poll_seconds: float,
) -> tuple[dict[str, Any] | None, dict[str, Any]]:
    """Drain for usage demonstrably at least as new as the accepted submission.

    Acceptance time is recorded before this grace and never changes.  A trusted
    adapter timestamp at or after submission detection, a notification sequence
    newer than the pre-validation observation, or clean adapter completion can
    establish that the retained cumulative total is not stale pre-proof usage.
    """

    started_ns = time.monotonic_ns()
    baseline_sequence = (
        existing_usage.get("notification_sequence")
        if existing_usage is not None
        else None
    )
    details: dict[str, Any] = {
        "configured_seconds": grace_seconds,
        "attempted": False,
        "usage_available_at_acceptance": existing_usage is not None,
        "usage_captured_during_grace": False,
        "fresh_update_required": True,
        "fresh_update_captured": False,
        "post_submission_usage_established": False,
        "freshness_basis": None,
        "submission_detected_at_unix_ns": submission_detected_at_unix_ns,
        "baseline_notification_sequence": baseline_sequence,
        "captured_notification_sequence": None,
        "process_exited_during_grace": process.poll() is not None,
        "waited_seconds": 0.0,
    }

    def establish(candidate: dict[str, Any], basis: str, *, fresh: bool) -> None:
        details["post_submission_usage_established"] = True
        details["freshness_basis"] = basis
        details["fresh_update_captured"] = fresh
        details["usage_captured_during_grace"] = fresh
        details["captured_notification_sequence"] = candidate[
            "notification_sequence"
        ]

    if usage_path is None:
        return existing_usage, details

    initial_exit = process.poll()
    if initial_exit == 0:
        details["process_exited_during_grace"] = True
        final_usage = read_token_usage(usage_path)
        if final_usage is not None:
            establish(
                final_usage,
                "clean_adapter_exit_with_final_usage",
                fresh=(
                    final_usage["notification_sequence"] != baseline_sequence
                ),
            )
            return final_usage, details
    if (
        existing_usage is not None
        and existing_usage["observed_at_unix_ns"] >= submission_detected_at_unix_ns
    ):
        establish(
            existing_usage,
            "trusted_notification_observed_at_or_after_submission_detection",
            fresh=False,
        )
        return existing_usage, details
    if grace_seconds <= 0:
        return existing_usage, details

    details["attempted"] = True
    deadline_ns = started_ns + int(grace_seconds * 1_000_000_000)
    usage = existing_usage
    while True:
        candidate = read_token_usage(usage_path)
        if candidate is not None:
            usage = candidate
            candidate_sequence = candidate["notification_sequence"]
            if (
                candidate["observed_at_unix_ns"]
                >= submission_detected_at_unix_ns
            ):
                establish(
                    candidate,
                    "trusted_notification_observed_at_or_after_submission_detection",
                    fresh=candidate_sequence != baseline_sequence,
                )
                break
            if (
                isinstance(baseline_sequence, int)
                and candidate_sequence > baseline_sequence
            ):
                establish(
                    candidate,
                    "newer_notification_sequence",
                    fresh=True,
                )
                break
        exit_code = process.poll()
        if exit_code is not None:
            details["process_exited_during_grace"] = True
            # The adapter writes atomically before exiting. One immediate final
            # read covers the small interval between poll and file visibility.
            candidate = read_token_usage(usage_path)
            if candidate is not None:
                usage = candidate
                if exit_code == 0:
                    establish(
                        candidate,
                        "clean_adapter_exit_with_final_usage",
                        fresh=(
                            candidate["notification_sequence"] != baseline_sequence
                        ),
                    )
            break
        remaining = (deadline_ns - time.monotonic_ns()) / 1_000_000_000
        if remaining <= 0:
            break
        time.sleep(min(poll_seconds, remaining))
    details["waited_seconds"] = round(
        (time.monotonic_ns() - started_ns) / 1_000_000_000, 6
    )
    return usage, details


def initial_usage_capture(args: argparse.Namespace) -> dict[str, Any]:
    return {
        "configured_seconds": args.usage_grace_seconds,
        "attempted": False,
        "usage_available_at_acceptance": False,
        "usage_captured_during_grace": False,
        "fresh_update_required": False,
        "fresh_update_captured": False,
        "post_submission_usage_established": False,
        "freshness_basis": None,
        "submission_detected_at_unix_ns": None,
        "baseline_notification_sequence": None,
        "captured_notification_sequence": None,
        "process_exited_during_grace": False,
        "waited_seconds": 0.0,
    }


def exact_ultra_stop_error(
    usage: Mapping[str, Any] | None, agent_exit_code: int | None
) -> str | None:
    """Explain why a stopped Ultra tree is not an exact validation boundary."""

    if agent_exit_code != 0:
        return f"Ultra adapter did not exit cleanly (exit code {agent_exit_code})"
    if usage is None:
        return "Ultra adapter exited without a final rooted-tree usage ledger"
    if usage.get("usage_scope") != ULTRA_USAGE_SCOPE:
        return "Ultra adapter exited without rooted-tree usage scope"
    if (
        usage.get("drain_complete") is not True
        or usage.get("tree_quiescent") is not True
        or usage.get("measurement_exact") is not True
        or usage.get("active_thread_ids") != []
        or usage.get("unresolved_thread_ids") != []
        or usage.get("invalid_reasons") != []
        or usage.get("interrupt_requested") is not False
        or usage.get("first_crossing") is not None
    ):
        return "Ultra adapter exited without an exact quiescent rooted-tree ledger"
    return None


def exact_ultra_token_drain_error(
    usage: Mapping[str, Any] | None,
    *,
    token_limit: int,
    first_crossing: Mapping[str, Any],
) -> str | None:
    """Authenticate a post-cap gate endpoint while its active tree is torn down.

    A token crossing intentionally does not wait for natural turn/cumulative
    tails.  Exactness comes from the finalized provider-response ledger, its
    app-server crossbindings, the CLOSED sole-inflight crossing, and immediate
    process-group teardown.  Rooted-tree accounting may therefore remain
    incomplete without weakening token accounting.
    """

    if usage is None:
        return "Ultra adapter exited without a final token-limit usage ledger"
    if usage.get("usage_scope") != ULTRA_USAGE_SCOPE:
        return "Ultra token-limit ledger lacks rooted-tree usage scope"
    if usage.get("model_tokens", -1) < token_limit:
        return "Ultra token-limit ledger fell below the configured cap"
    if usage.get("first_crossing") != dict(first_crossing):
        return "Ultra token-limit first-crossing identity changed during cleanup"
    if usage.get("stop_reason") != "token_limit":
        return "Ultra token-limit ledger has the wrong stop reason"
    if (
        usage.get("accounting_projection_schema_version")
        != ULTRA_ACCOUNTING_PROJECTION_SCHEMA_VERSION
        or usage.get("drain_complete") is not False
        or usage.get("measurement_exact") is not True
        or usage.get("submission_boundary_exact") is not False
        or usage.get("submission_boundary") is not None
        or usage.get("invalid_reasons") != []
        or usage.get("interrupt_requested") is not False
        or usage.get("pending_interrupt_response_count") != 0
    ):
        return "Ultra adapter did not preserve the exact provider-gated token endpoint"

    summary = usage.get("provider_token_gate")
    if not isinstance(summary, Mapping) or (
        set(summary) != ULTRA_PROVIDER_GATE_SUMMARY_KEYS
        or summary.get("enabled") is not True
        or summary.get("response_token_bound") != PROVIDER_RESPONSE_TOKEN_BOUND
        or summary.get("final_attached") is not True
        or summary.get("exact_for_usage") is not True
        or not isinstance(summary.get("artifact_path"), str)
        or not Path(summary["artifact_path"]).is_absolute()
    ):
        return "Ultra token-limit ledger lacks its exact final gate attachment"
    try:
        _provider_gate_sha256(
            summary.get("record_sha256"),
            "token cleanup provider-gate record_sha256",
        )
    except BenchmarkToolError:
        return "Ultra token-limit ledger has a malformed gate record hash"
    terminal = summary.get("terminal")
    if not isinstance(terminal, Mapping):
        return "Ultra token-limit ledger lacks its terminal gate state"
    gate_crossing = terminal.get("crossing")
    gate_request_kind = (
        gate_crossing.get("request_kind")
        if isinstance(gate_crossing, Mapping)
        else None
    )
    expected_crossing_release = (
        _provider_gate_crossing_release_kind(gate_request_kind)
        if isinstance(gate_request_kind, str) and gate_request_kind
        else None
    )
    if (
        terminal.get("phase") != "CLOSED"
        or terminal.get("close_reason") != "token_limit"
        or terminal.get("completed_tokens") != usage.get("model_tokens")
        or terminal.get("crossing_closed") is not True
        or terminal.get("open_request_ids") != []
        or terminal.get("all_complete") is not True
        or terminal.get("no_post_close_upstream") is not True
        or terminal.get("poisoned") is not False
        or terminal.get("poison_reasons") != []
        or terminal.get("active_handler_count") != 0
        or isinstance(terminal.get("active_handler_count"), bool)
        or terminal.get("handlers_quiescent") is not True
        or not isinstance(gate_crossing, Mapping)
        or gate_crossing.get("response_id") != first_crossing.get("response_id")
        or gate_crossing.get("completed_tokens") != usage.get("model_tokens")
        or gate_crossing.get("sole_inflight") is not True
        or gate_crossing.get("release_kind") != expected_crossing_release
    ):
        return "Ultra token-limit ledger lacks an exact CLOSED gate crossing"

    response_ledger = usage.get("appserver_response_ledger")
    if not isinstance(response_ledger, list) or not response_ledger:
        return "Ultra token-limit ledger lacks provider-response evidence"
    crossing_responses = [
        response
        for response in response_ledger
        if isinstance(response, Mapping)
        and response.get("response_id") == gate_crossing.get("response_id")
    ]
    if len(crossing_responses) != 1:
        return "Ultra token-limit crossing response is not unique"
    crossing_response = crossing_responses[0]
    crossing_call = crossing_response.get("provider_gate_call")
    crossbind = (
        crossing_call.get("appserver_crossbind")
        if isinstance(crossing_call, Mapping)
        else None
    )
    call_request_metadata = (
        crossing_call.get("request_metadata")
        if isinstance(crossing_call, Mapping)
        else None
    )
    if (
        not isinstance(crossing_call, Mapping)
        or crossing_call.get("call_id") != gate_crossing.get("call_id")
        or crossing_call.get("response_id") != gate_crossing.get("response_id")
        or crossing_call.get("normalized_usage") != crossing_response.get("usage")
        or crossing_call.get("committed_total") != usage.get("model_tokens")
        or crossing_call.get("crossed_cap") is not True
        or not isinstance(call_request_metadata, Mapping)
        or call_request_metadata.get("request_kind") != gate_request_kind
        or crossing_call.get("release_kind") != expected_crossing_release
        or crossing_call.get("client_release_complete") is not True
        or not isinstance(crossing_call.get("appserver_delivery"), Mapping)
        or crossing_call["appserver_delivery"].get("kind")
        != "direct_raw_response"
        or crossing_call.get("commit_monotonic_ns")
        != gate_crossing.get("commit_monotonic_ns")
        or crossing_call.get("commit_unix_ns")
        != gate_crossing.get("commit_unix_ns")
        or not isinstance(crossbind, Mapping)
        or crossbind.get("thread_id") != crossing_response.get("thread_id")
        or crossbind.get("turn_id") != crossing_response.get("turn_id")
        or crossbind.get("event_sequence")
        != crossing_response.get("raw_response_notification_sequence")
        or crossbind.get("normalized_usage") != crossing_response.get("usage")
    ):
        return "Ultra token-limit crossing lacks an exact app-server crossbinding"
    crossing_commit = crossing_call.get("commit_monotonic_ns")
    if not isinstance(crossing_commit, int) or isinstance(crossing_commit, bool):
        return "Ultra token-limit crossing commit clock is malformed"
    for response in response_ledger:
        if not isinstance(response, Mapping):
            return "Ultra token-limit response ledger is malformed"
        call = response.get("provider_gate_call")
        if (
            not isinstance(call, Mapping)
            or call.get("response_id") != response.get("response_id")
            or call.get("normalized_usage") != response.get("usage")
            or call.get("client_release_complete") is not True
            or not isinstance(call.get("admitted_monotonic_ns"), int)
            or isinstance(call.get("admitted_monotonic_ns"), bool)
            or call["admitted_monotonic_ns"] > crossing_commit
            or not isinstance(call.get("commit_monotonic_ns"), int)
            or isinstance(call.get("commit_monotonic_ns"), bool)
            or call["commit_monotonic_ns"] > crossing_commit
            or (call is not crossing_call and call.get("crossed_cap") is not False)
        ):
            return "Ultra token-limit response ledger permits post-crossing work"

    teardown = usage.get("adapter_teardown")
    if not isinstance(teardown, Mapping) or (
        set(teardown) != ULTRA_ADAPTER_TEARDOWN_KEYS
        or teardown.get("process_group_isolated") is not True
        or teardown.get("immediate") is not True
        or teardown.get("stdin_closed") is not True
        or teardown.get("completed") is not True
        or not isinstance(teardown.get("returncode"), int)
        or isinstance(teardown.get("returncode"), bool)
    ):
        return "Ultra token-limit ledger lacks completed immediate teardown"
    return None


def ultra_stop_usage_capture(
    args: argparse.Namespace,
    usage: Mapping[str, Any],
    *,
    boundary_observed_at_unix_ns: int,
) -> dict[str, Any]:
    """Describe the exact final ledger available at a clean Ultra tree stop."""

    details = initial_usage_capture(args)
    details.update(
        {
            "usage_available_at_acceptance": True,
            "post_submission_usage_established": True,
            "freshness_basis": "clean_ultra_adapter_exit_with_exact_quiescent_final_ledger",
            "submission_detected_at_unix_ns": boundary_observed_at_unix_ns,
            "captured_notification_sequence": usage["notification_sequence"],
            "process_exited_during_grace": True,
            "ultra_tree_drain": True,
        }
    )
    return details


def ultra_boundary_usage_capture(
    args: argparse.Namespace,
    usage: Mapping[str, Any],
    request: Mapping[str, Any],
) -> dict[str, Any]:
    """Describe usage made exact by an unanswered authenticated submit call."""

    details = initial_usage_capture(args)
    details.update(
        {
            "usage_available_at_acceptance": True,
            "post_submission_usage_established": True,
            "freshness_basis": "authenticated_outer_exec_raw_response_with_blocked_inner_submit_boundary",
            "submission_detected_at_unix_ns": request[
                "request_published_at_unix_ns"
            ],
            "captured_notification_sequence": usage["notification_sequence"],
            "process_exited_during_grace": True,
            "ultra_tree_drain": False,
            "ultra_submission_boundary": True,
        }
    )
    return details


def apply_ultra_boundary_deviation(
    protocol: dict[str, Any],
    args: argparse.Namespace,
    *,
    authenticated_boundary_verified: bool = False,
    proof_accepted: bool = False,
) -> None:
    """Require the barrier for accepted proofs, not for exact failure stops."""

    if args.reasoning_effort != "ultra":
        return
    protocol["verified"]["authenticated_first_valid_proof_boundary"] = (
        authenticated_boundary_verified
    )
    if authenticated_boundary_verified or not proof_accepted:
        return
    protocol["complete"] = False
    note = (
        "Ultra attempt lacks a runner-verified authenticated first-valid-proof "
        "submission boundary; the result cannot be an official specification score"
    )
    if note not in protocol["notes"]:
        protocol["notes"].append(note)


def token_measurement_record(
    args: argparse.Namespace,
    usage: dict[str, Any] | None,
    usage_capture: Mapping[str, Any],
    *,
    limit_triggered: bool,
    limit_observed_tokens: int | None,
    trusted_usage_path_outside_workspace: bool,
    measurement_error: str | None,
) -> dict[str, Any]:
    ultra = args.reasoning_effort == "ultra"
    overshoot = (
        limit_observed_tokens - args.token_limit
        if limit_triggered and limit_observed_tokens is not None
        else None
    )
    final_tokens = usage.get("model_tokens") if usage is not None else None
    final_overshoot = (
        max(0, int(final_tokens) - args.token_limit)
        if limit_triggered and isinstance(final_tokens, int)
        else None
    )
    return {
        "source": (
            ULTRA_TOKEN_MEASUREMENT_SOURCE if ultra else TOKEN_MEASUREMENT_SOURCE
        ),
        "provider_cumulative_total_exact": (
            usage is not None
            and measurement_error is None
            and (not ultra or usage.get("measurement_exact") is True)
        ),
        "cached_input_counted_once": True,
        "measurement_error": measurement_error,
        "trusted_usage_path_outside_workspace": (
            trusted_usage_path_outside_workspace
        ),
        "post_submission_usage_established": bool(
            usage_capture.get("post_submission_usage_established")
        ),
        "capture_grace": dict(usage_capture),
        "usage_scope": usage.get("usage_scope") if usage is not None else None,
        "thread_count": (
            usage.get("thread_count") if ultra and usage is not None else (1 if usage else 0)
        ),
        "response_count": (
            usage.get("call_count") if ultra and usage is not None else (1 if usage else 0)
        ),
        "tree_drain_complete": (
            usage.get("drain_complete")
            if ultra and usage is not None
            else (False if ultra else usage is not None)
        ),
        "limit_enforcement": {
            "mode": (
                ULTRA_TOKEN_LIMIT_ENFORCEMENT_MODE
                if ultra
                else TOKEN_LIMIT_ENFORCEMENT_MODE
            ),
            "notification": (
                ULTRA_USAGE_NOTIFICATION if ultra else TOKEN_USAGE_NOTIFICATION
            ),
            "configured_limit_tokens": args.token_limit,
            "triggered": limit_triggered,
            "observed_tokens": limit_observed_tokens if limit_triggered else None,
            "overshoot_tokens": overshoot,
            "first_crossing_tokens": (
                limit_observed_tokens if limit_triggered else None
            ),
            "first_crossing_overshoot_tokens": overshoot,
            "final_endpoint_tokens": final_tokens if limit_triggered else None,
            "final_overshoot_tokens": final_overshoot,
            "checked_before_submission_validation": True,
            "one_response_overshoot_possible": True,
            "concurrent_inflight_overshoot_possible": False,
        },
    }


def apply_token_protocol_status(
    protocol: dict[str, Any],
    args: argparse.Namespace,
    usage: dict[str, Any] | None,
    token_measurement: Mapping[str, Any],
    *,
    failure_code: str | None,
    proof_accepted: bool,
) -> None:
    """Fail closed unless the outcome agrees with trusted live token evidence."""

    if usage is None:
        protocol["complete"] = False
        protocol["notes"].append(
            "trusted live cumulative provider token usage was not supplied"
        )
        return
    if token_measurement.get("measurement_error") is not None:
        protocol["complete"] = False
        protocol["notes"].append(
            "the trusted live cumulative usage stream became malformed or unreadable"
        )
        return

    ultra = usage.get("usage_scope") == ULTRA_USAGE_SCOPE
    gate_summary = usage.get("provider_token_gate") if ultra else None
    exact_gate_crossing = bool(
        ultra
        and usage.get("first_crossing") is not None
        and isinstance(gate_summary, Mapping)
        and gate_summary.get("final_attached") is True
        and gate_summary.get("exact_for_usage") is True
    )
    if ultra and (
        usage.get("measurement_exact") is not True
        or (
            usage.get("drain_complete") is not True
            and usage.get("submission_boundary_exact") is not True
            and not exact_gate_crossing
        )
    ):
        protocol["complete"] = False
        protocol["notes"].append(
            "the Ultra tree produced neither an exact drain nor an exact "
            "authenticated submission-boundary ledger"
        )

    enforcement = token_measurement["limit_enforcement"]
    at_or_above_limit = usage["model_tokens"] >= args.token_limit
    expected_observed = _limit_observation(usage)
    trigger_consistent = (
        enforcement["triggered"] is True
        and enforcement["observed_tokens"] == expected_observed
        and enforcement["overshoot_tokens"]
        == expected_observed - args.token_limit
    )
    if at_or_above_limit:
        if failure_code not in ("TIME_LIMIT", "TOKEN_LIMIT") or not trigger_consistent:
            protocol["complete"] = False
            protocol["notes"].append(
                "live cumulative usage reached the token cap, but the recorded "
                "outcome is not the matching TIME_LIMIT/TOKEN_LIMIT result"
            )
        elif usage["model_tokens"] > args.token_limit:
            protocol["notes"].append(
                (
                    "the final Ultra tree ledger can include concurrent response "
                    "tail after the first crossing"
                    if ultra
                    else "the first observed threshold-crossing notification "
                    "includes one provider response of token overshoot"
                )
            )
    elif enforcement["triggered"] or failure_code == "TOKEN_LIMIT":
        protocol["complete"] = False
        protocol["notes"].append(
            "token-limit outcome disagrees with live cumulative usage below the cap"
        )

    if proof_accepted and not token_measurement["post_submission_usage_established"]:
        protocol["complete"] = False
        protocol["notes"].append(
            "no trusted post-submission or clean-final usage update was captured"
        )


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
    required_claims = {
        name: value
        for name, value in claims.items()
        if name not in ("backend_seed_supplied", "seed_enforced_by_agent")
    }
    seed_mode_complete = (
        claims["backend_seed_supplied"] == claims["seed_enforced_by_agent"]
    )
    complete = (
        all(required_claims.values())
        and seed_mode_complete
        and all(verified.values())
    )
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
        reject_workspace_local_module_imports=bool(
            getattr(args, "reject_workspace_local_module_imports", False)
        ),
    )


def _validate_ultra_submission_yield_envelope(
    args: argparse.Namespace, freeze_check: Mapping[str, Any]
) -> None:
    """Bind the canonical exec yield to the complete frozen post-prompt tail."""

    if args.reasoning_effort != "ultra":
        return
    limits = freeze_check.get("limits")
    if not isinstance(limits, Mapping):
        raise BenchmarkToolError(
            "Ultra frozen-run verification lacks authenticated timing limits"
        )
    wall_seconds = limits.get("wall_clock_seconds")
    reserve_seconds = limits.get("post_submission_validation_reserve_seconds")
    if (
        isinstance(wall_seconds, bool)
        or not isinstance(wall_seconds, (int, float))
        or float(wall_seconds)
        != NESTED_SUBMISSION_EXEC_YIELD_ATTEMPT_WALL_SECONDS
    ):
        raise BenchmarkToolError(
            "Ultra frozen wall-clock limit must be exactly 1800 seconds"
        )
    if (
        isinstance(reserve_seconds, bool)
        or not isinstance(reserve_seconds, (int, float))
        or float(reserve_seconds)
        != NESTED_SUBMISSION_EXEC_YIELD_POST_SUBMISSION_VALIDATION_RESERVE_SECONDS
    ):
        raise BenchmarkToolError(
            "Ultra frozen post-submission validation reserve must be exactly 369 seconds"
        )

    synthetic = freeze_check.get("synthetic_canary")
    synthetic_canary = bool(
        isinstance(synthetic, Mapping)
        and synthetic.get("scored") is False
        and synthetic.get("matrix_assignment") is False
    )
    time_limit = args.time_limit_seconds
    if isinstance(time_limit, bool) or not isinstance(time_limit, (int, float)):
        raise BenchmarkToolError("Ultra runner wall-clock limit is invalid")
    if synthetic_canary:
        if not 0 < float(time_limit) <= float(wall_seconds):
            raise BenchmarkToolError(
                "synthetic Ultra canary wall time must not exceed the frozen limit"
            )
    elif float(time_limit) != float(wall_seconds):
        raise BenchmarkToolError(
            "official Ultra runner wall-clock limit must equal the frozen 1800 seconds"
        )

    compile_timeout = args.validation_timeout_seconds
    audit_timeout = args.audit_timeout_seconds
    if any(
        isinstance(value, bool)
        or not isinstance(value, (int, float))
        or not 0 < float(value) < float("inf")
        for value in (compile_timeout, audit_timeout)
    ):
        raise BenchmarkToolError(
            "Ultra hidden-validation timeouts must be finite and positive"
        )
    actual_tail_seconds = (
        2 * float(compile_timeout)
        + float(audit_timeout)
        + ACCEPTED_SUBMISSION_CLOSE_TIMEOUT_SECONDS
        + FORCED_TERMINATION_WINDOWS * FORCED_TERMINATION_GRACE_SECONDS
    )
    if actual_tail_seconds > float(reserve_seconds):
        raise BenchmarkToolError(
            "Ultra hidden-validation and process-close tail exceeds the frozen reserve"
        )
    if not synthetic_canary and actual_tail_seconds != float(reserve_seconds):
        raise BenchmarkToolError(
            "official Ultra validation timeouts do not exactly realize the 369-second reserve"
        )
    if (
        NESTED_SUBMISSION_EXEC_YIELD_TIME_MS
        <= 1_000 * (float(wall_seconds) + float(reserve_seconds))
    ):
        raise BenchmarkToolError(
            "canonical outer exec yield does not exceed the frozen post-prompt envelope"
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
    _validate_ultra_submission_yield_envelope(args, freeze_check)
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
            "prompt_startup_seconds": float(
                getattr(args, "prompt_startup_timeout_seconds", 120.0)
            ),
            "post_acceptance_usage_grace_seconds": args.usage_grace_seconds,
        },
    }


def classify_final_outcome(
    *,
    timed_out: bool,
    token_limited: bool,
    submission_present: bool,
    ultra_submission_attempted: bool,
    direct_submission_violation: bool,
    startup_agent_failure: bool,
    useful_work_started: bool,
    network_violation: Mapping[str, Any],
    first_valid_seconds: float | None,
    validation_result: Mapping[str, Any] | None,
    agent_system_error: str | None,
    usage: Mapping[str, Any] | None,
) -> tuple[bool, str | None, str]:
    """Apply the specification's failure precedence to simultaneous evidence.

    A validated Ultra request counts as a submission even when Lean rejects it;
    only an attempt with no such request and no final submission receives
    ``NO_SUBMISSION``.  Failures before any useful work remain infrastructure
    incidents rather than model outcomes.
    """

    if timed_out:
        return False, "TIME_LIMIT", "fixed wall-clock limit reached"
    if token_limited:
        note = (
            "first exact completed-response aggregate over the Ultra thread "
            "tree reached or crossed the configured limit"
            if usage is not None and usage.get("usage_scope") == ULTRA_USAGE_SCOPE
            else "first observed live cumulative model-token update reached or "
            "crossed the configured limit"
        )
        return False, "TOKEN_LIMIT", note

    if not useful_work_started and (startup_agent_failure or agent_system_error):
        note = agent_system_error or "agent adapter failed before useful work began"
        return False, "SYSTEM_ERROR", note

    validated_request_exists = bool(
        ultra_submission_attempted and validation_result is not None
    )
    if not submission_present and not validated_request_exists:
        return False, "NO_SUBMISSION", "agent ended without a proof submission"

    validation_failed = bool(
        validation_result is not None and validation_result.get("pass") is not True
    )
    validation_code = (
        validation_result.get("failure_code")
        if validation_failed and validation_result is not None
        else None
    )
    if validation_failed and validation_code not in FAILURE_PRECEDENCE:
        validation_code = "PROOF_ERROR"

    rule_notes: list[str] = []
    if direct_submission_violation:
        rule_notes.append(
            "Ultra agent created or modified runner-owned Submission.lean"
        )
    if network_violation.get("detected") is True:
        rule_notes.append(
            str(network_violation.get("note") or "blocked network access was detected")
        )
    if validation_code == "RULE_VIOLATION" and validation_result is not None:
        rule_notes.append(
            str(validation_result.get("note") or "hidden validation found a rule violation")
        )
    if rule_notes:
        return False, "RULE_VIOLATION", "; ".join(dict.fromkeys(rule_notes))

    if validation_code in ("SYNTAX_OR_ELAB", "PROOF_ERROR"):
        assert validation_result is not None
        return (
            False,
            str(validation_code),
            str(validation_result.get("note") or "Lean rejected the submitted proof"),
        )

    if validation_code == "SYSTEM_ERROR":
        assert validation_result is not None
        return (
            False,
            "SYSTEM_ERROR",
            str(validation_result.get("note") or "hidden validation failed"),
        )
    if agent_system_error:
        return False, "SYSTEM_ERROR", agent_system_error

    if (
        first_valid_seconds is not None
        and validation_result is not None
        and validation_result.get("pass") is True
    ):
        return True, None, ""
    return False, "SYSTEM_ERROR", "submission was not validated"


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
    controlled_manifest_sha256 = sha256_file(args.controlled_manifest)
    validator_contract_sha256 = _validator_contract_sha256(
        args,
        compile_command=compile_command,
        audit_command=audit_command,
    )

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
    validation_log_sha256: str | None = None
    validation_record_sha256: str | None = None
    submission: Path | None = None
    agent_exit_code: int | None = None
    process: subprocess.Popen[Any] | None = None
    agent_system_error: str | None = None
    useful_work_started = False
    timed_out = False
    token_limited = False
    first_valid_seconds: float | None = None
    actual_stop_seconds = 0.0
    usage: dict[str, Any] | None = None
    usage_path: Path | None = None
    provider_gate_artifacts: dict[str, Path] | None = None
    provider_gate_source_sha256: str | None = None
    provider_gate_catalog: dict[str, Any] | None = None
    provider_gate_transport: dict[str, Any] | None = None
    provider_gate_live_crossing: dict[str, Any] | None = None
    provider_gate_final: dict[str, Any] | None = None
    provider_gate_error: str | None = None
    provider_gate_status = "not_required"
    provider_gate_cleanup_deadline_ns: int | None = None
    trusted_usage_path_ready = False
    usage_measurement_error: str | None = None
    limit_observed_tokens: int | None = None
    submission_digest: str | None = None
    final_submission_digest: str | None = None
    accepted_submission_log: Path | None = None
    frozen_workspace: Path | None = None
    ultra_baseline_workspace: Path | None = None
    prompt_provenance: dict[str, Any] | None = None
    effective_prompt_text: str | None = None
    effective_prompt_sha256: str | None = None
    effective_prompt_bytes: int | None = None
    prompt_handshake_nonce = secrets.token_hex(32)
    prompt_paths: dict[str, Path] | None = None
    prompt_release_required = False
    prompt_release_status = "not_initialized"
    prompt_release_authenticated = False
    prompt_release_timing_exact = False
    prompt_release_useful_basis = "not_started"
    prompt_startup_timeout_triggered = False
    prompt_stale_artifacts_removed: list[str] = []
    prompt_ready_record: dict[str, Any] | None = None
    prompt_go_record: dict[str, Any] | None = None
    prompt_released_record: dict[str, Any] | None = None
    prompt_ready_descriptor: dict[str, Any] | None = None
    prompt_go_descriptor: dict[str, Any] | None = None
    prompt_released_descriptor: dict[str, Any] | None = None
    prompt_release_error: str | None = None
    prompt_released_monotonic_ns: int | None = None
    process_started_monotonic_ns: int | None = None
    network_marker: Path | None = None
    network_monitor: NetworkViolationMonitor | None = None
    submission_monitor: SubmissionViolationMonitor | None = None
    direct_submission_violation = False
    ultra_submission_attempted = False
    ultra_boundary_verified = False
    accepted_boundary_request: dict[str, Any] | None = None
    accepted_boundary_ack: dict[str, Any] | None = None
    accepted_barrier_artifacts: dict[str, Any] | None = None
    handled_request_sha256: str | None = None
    expected_submission_sequence = 1
    last_rejected_validation: dict[str, Any] | None = None
    network_violation: dict[str, Any] = {
        "detected": False,
        "event_count": 0,
        "saturated": False,
        "integrity_ok": True,
        "note": "agent execution did not start",
        "saved_marker_log": None,
        "marker_sha256": None,
    }
    usage_capture = initial_usage_capture(args)
    ultra_attempt = args.reasoning_effort == "ultra"
    prompt_startup_timeout_seconds = float(
        getattr(args, "prompt_startup_timeout_seconds", 120.0)
    )
    try:
        if ultra_attempt and not bool(
            getattr(args, "reject_workspace_local_module_imports", False)
        ):
            raise BenchmarkToolError(
                "Ultra authenticated submission requires workspace-local import rejection"
            )
        usage_path = trusted_usage_output(args, logs_dir)
        if usage_path.exists() or usage_path.with_suffix(usage_path.suffix + ".tmp").exists():
            raise BenchmarkToolError(
                f"trusted usage output already exists before prompt release: {usage_path}"
            )
        if ultra_attempt:
            provider_gate_artifacts = provider_gate_paths(usage_path)
            stale_gate_paths = [
                path
                for path in (
                    provider_gate_artifacts["live"],
                    provider_gate_artifacts["final"],
                    Path(str(provider_gate_artifacts["live"]) + ".tmp"),
                    Path(str(provider_gate_artifacts["final"]) + ".tmp"),
                )
                if path.exists() or path.is_symlink()
            ]
            for gate_path in provider_gate_artifacts.values():
                stale_gate_paths.extend(
                    gate_path.parent.glob(f".{gate_path.name}.*.tmp")
                )
            if stale_gate_paths:
                raise BenchmarkToolError("stale provider-token-gate artifact exists")
            gate_source = Path(__file__).with_name("provider_token_gate.py")
            if gate_source.is_symlink() or not gate_source.is_file():
                raise BenchmarkToolError("provider-token-gate source is not a regular file")
            provider_gate_source_sha256 = sha256_file(gate_source)
            provider_gate_status = "artifacts_prepared"
        prompt_paths = prompt_handshake_paths(usage_path)
        prompt_stale_artifacts_removed = _remove_prompt_handshake_stale_artifacts(
            prompt_paths, logs_dir
        )
        prompt_release_status = "artifacts_prepared"
        if ultra_attempt:
            barrier_paths = submission_barrier_paths(usage_path)
            stale_barrier = [
                path
                for path in (
                    barrier_paths["request"],
                    barrier_paths["ack"],
                    barrier_paths["call"],
                    barrier_paths["challenge"],
                    Path(str(barrier_paths["request"]) + ".tmp"),
                    Path(str(barrier_paths["ack"]) + ".tmp"),
                    Path(str(barrier_paths["call"]) + ".tmp"),
                    Path(str(barrier_paths["challenge"]) + ".tmp"),
                )
                if path.exists() or path.is_symlink()
            ]
            stale_barrier.extend(
                usage_path.parent.glob(usage_path.name + ".submission-*.lean")
            )
            if stale_barrier:
                raise BenchmarkToolError("stale submission-barrier artifact exists")
            submission_challenge = _make_submission_challenge(
                args,
                run_id=run_id,
                compile_command=compile_command,
                audit_command=audit_command,
            )
            write_json(barrier_paths["challenge"], submission_challenge)
        copytree_fresh(args.base_workspace, workspace)
        try:
            usage_path.relative_to(workspace)
        except ValueError:
            pass
        else:
            raise BenchmarkToolError(
                "trusted usage output must be outside the model-writable workspace"
            )
        trusted_usage_path_ready = True
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
                        "token_measurement": token_measurement_record(
                            args,
                            None,
                            usage_capture,
                            limit_triggered=False,
                            limit_observed_tokens=None,
                            trusted_usage_path_outside_workspace=(
                                trusted_usage_path_ready
                            ),
                            measurement_error=usage_measurement_error,
                        ),
                        "library_use": False,
                        "library_declarations": [],
                        "network_violation": network_violation,
                        "n_preflight": n_preflight,
                        "prompt_release": _prompt_release_run_record(
                            required=False,
                            status="preflight_failed_before_ready",
                            authenticated=False,
                            timing_exact=False,
                            useful_work_basis="not_started",
                            startup_timeout_seconds=(
                                prompt_startup_timeout_seconds
                            ),
                            startup_timeout_triggered=False,
                            nonce=prompt_handshake_nonce,
                            paths=prompt_paths,
                            effective_prompt_sha256=None,
                            effective_prompt_bytes=None,
                            ready_descriptor=None,
                            go_descriptor=None,
                            released_descriptor=None,
                            stale_artifacts_removed=(
                                prompt_stale_artifacts_removed
                            ),
                            error="condition N isolation preflight failed",
                        ),
                        "provider_token_gate": provider_gate_run_record(
                            required=ultra_attempt,
                            status=provider_gate_status,
                            paths=provider_gate_artifacts,
                            source_sha256=provider_gate_source_sha256,
                            catalog=provider_gate_catalog,
                            transport_provenance=provider_gate_transport,
                            live_crossing=provider_gate_live_crossing,
                            final=provider_gate_final,
                            error="condition N isolation preflight failed",
                        ),
                    }
                )
                protocol = protocol_status(args, n_preflight=n_preflight)
                apply_token_protocol_status(
                    protocol,
                    args,
                    None,
                    record["token_measurement"],
                    failure_code="SYSTEM_ERROR",
                    proof_accepted=False,
                )
                record["protocol"] = protocol
                record["scored"] = False
                return record
        submission = resolve_below(workspace, args.submission_relative)
        if submission.exists():
            raise BenchmarkToolError(
                "submission path exists before prompt release; task package may expose a proof"
            )
        submission.parent.mkdir(parents=True, exist_ok=True)
        if ultra_attempt:
            submission_monitor = SubmissionViolationMonitor(submission)
            ultra_baseline_workspace = workspace_parent / (
                f"highambench-ultra-baseline-{uuid.uuid4().hex}"
            )
            freeze_stopped_workspace(workspace, ultra_baseline_workspace)
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
            "usage_output": usage_path,
            "network_violation_marker": network_marker,
            "prompt_ready_output": prompt_paths["ready"],
            "prompt_go_input": prompt_paths["go"],
            "prompt_release_output": prompt_paths["release"],
            "prompt_handshake_nonce": prompt_handshake_nonce,
            "run_id": run_id,
            "provider_gate_live_output": (
                provider_gate_artifacts["live"] if provider_gate_artifacts else ""
            ),
            "provider_gate_output": (
                provider_gate_artifacts["final"] if provider_gate_artifacts else ""
            ),
            "model_catalog_sha256": "0" * 64,
            "model_entry_sha256": "0" * 64,
            "provider_response_bound": PROVIDER_RESPONSE_TOKEN_BOUND,
        }
        agent_command = render_command(agent_command_template, command_values)
        if ultra_attempt:
            provider_gate_catalog = authenticate_bundled_model_catalog(
                agent_command,
                model=args.model,
                reasoning_effort=args.reasoning_effort,
                freeze_check=record["frozen_run_verification"]["freeze_check"],
            )
            provider_gate_transport = authenticate_provider_transport_provenance(
                agent_command
            )
            command_values["model_catalog_sha256"] = provider_gate_catalog[
                "catalog_sha256"
            ]
            command_values["model_entry_sha256"] = provider_gate_catalog[
                "entry_sha256"
            ]
            command_values["provider_response_bound"] = provider_gate_catalog[
                "response_bound"
            ]
            agent_command = render_command(agent_command_template, command_values)
            assert provider_gate_artifacts is not None
            expected_gate_options = {
                "--provider-gate-live-output": str(provider_gate_artifacts["live"]),
                "--provider-gate-output": str(provider_gate_artifacts["final"]),
                "--model-catalog-sha256": str(
                    provider_gate_catalog["catalog_sha256"]
                ),
                "--model-entry-sha256": str(provider_gate_catalog["entry_sha256"]),
                "--provider-response-bound": str(
                    provider_gate_catalog["response_bound"]
                ),
            }
            for option, expected in expected_gate_options.items():
                if _command_option_value(agent_command, option, required=True) != expected:
                    raise BenchmarkToolError(
                        f"agent command {option} disagrees with the trusted provider gate"
                    )
            provider_gate_status = "static_contract_authenticated"
        prompt_provenance = build_prompt_provenance(
            condition=args.condition,
            freeze_check=record["frozen_run_verification"]["freeze_check"],
            agent_command=agent_command,
            task_root=args.task_root,
            task_destination=task_destination,
            controlled_manifest=manifest,
            canonical_target=resolve_below(workspace, args.canonical_relative),
            include_effective_text=True,
        )
        if prompt_provenance is not None:
            raw_effective_prompt = prompt_provenance.pop("_effective_prompt_text", None)
            if not isinstance(raw_effective_prompt, str):
                raise BenchmarkToolError(
                    "authenticated prompt provenance omitted the effective prompt"
                )
            effective_prompt_text = raw_effective_prompt
            effective = prompt_provenance.get("effective_prompt")
            if not isinstance(effective, Mapping):
                raise BenchmarkToolError("prompt provenance lacks effective-prompt identity")
            effective_prompt_sha256 = effective.get("sha256")
            effective_prompt_bytes = effective.get("bytes")
            if (
                not isinstance(effective_prompt_sha256, str)
                or re.fullmatch(r"[0-9a-f]{64}", effective_prompt_sha256) is None
                or not isinstance(effective_prompt_bytes, int)
                or isinstance(effective_prompt_bytes, bool)
                or effective_prompt_bytes <= 0
            ):
                raise BenchmarkToolError("effective-prompt identity is malformed")
            prompt_release_required = True
            _validate_prompt_handshake_command(
                agent_command,
                paths=prompt_paths,
                nonce=prompt_handshake_nonce,
                run_id=run_id,
            )
            prompt_release_status = "awaiting_ready"
        else:
            prompt_release_status = "not_required_legacy_prompt"
            prompt_release_useful_basis = "legacy_process_start"
        protocol = protocol_status(args, n_preflight=n_preflight)
        if args.strict_protocol and not protocol["complete"]:
            raise BenchmarkToolError(
                "strict protocol requested but controls are incomplete: "
                + "; ".join(protocol["notes"])
            )

        environment = _sanitized_provider_transport_environment()
        environment.update(
            {
                "HIGHAMBENCH_CONDITION": args.condition,
                "HIGHAMBENCH_REPETITION_ID": args.repetition_id,
                "HIGHAMBENCH_SEED": "" if args.seed is None else str(args.seed),
                "HIGHAMBENCH_WORKSPACE": str(workspace),
                "HIGHAMBENCH_SUBMISSION": str(submission),
                "HIGHAMBENCH_TIME_LIMIT": str(args.time_limit_seconds),
                "HIGHAMBENCH_TOKEN_LIMIT": str(args.token_limit),
                "HIGHAMBENCH_USAGE_OUTPUT": str(usage_path),
                "HIGHAMBENCH_PROMPT_READY_OUTPUT": str(prompt_paths["ready"]),
                "HIGHAMBENCH_PROMPT_GO_INPUT": str(prompt_paths["go"]),
                "HIGHAMBENCH_PROMPT_RELEASE_OUTPUT": str(prompt_paths["release"]),
                "HIGHAMBENCH_PROMPT_HANDSHAKE_NONCE": prompt_handshake_nonce,
                "HIGHAMBENCH_PROMPT_RUN_ID": run_id,
                "HIGHAMBENCH_MODEL": args.model,
                "HIGHAMBENCH_REASONING_EFFORT": args.reasoning_effort,
                "HIGHAMBENCH_PROVIDER_GATE_LIVE_OUTPUT": (
                    str(provider_gate_artifacts["live"])
                    if provider_gate_artifacts
                    else ""
                ),
                "HIGHAMBENCH_PROVIDER_GATE_OUTPUT": (
                    str(provider_gate_artifacts["final"])
                    if provider_gate_artifacts
                    else ""
                ),
                "HIGHAMBENCH_MODEL_CATALOG_SHA256": (
                    str(provider_gate_catalog["catalog_sha256"])
                    if provider_gate_catalog
                    else ""
                ),
                "HIGHAMBENCH_MODEL_ENTRY_SHA256": (
                    str(provider_gate_catalog["entry_sha256"])
                    if provider_gate_catalog
                    else ""
                ),
                "HIGHAMBENCH_PROVIDER_RESPONSE_BOUND": (
                    str(provider_gate_catalog["response_bound"])
                    if provider_gate_catalog
                    else ""
                ),
                "HIGHAMBENCH_PROMPT_EFFECTIVE_SHA256": (
                    effective_prompt_sha256 or ""
                ),
                "HIGHAMBENCH_PROMPT_EFFECTIVE_BYTES": (
                    str(effective_prompt_bytes)
                    if effective_prompt_bytes is not None
                    else ""
                ),
                NETWORK_VIOLATION_MARKER_ENV: str(network_marker),
            }
        )
        with agent_log.open("w", encoding="utf-8", newline="") as log:
            log.write(f"$ {command_display(agent_command)}\n\n")
            log.flush()
            process_started_monotonic_ns = time.monotonic_ns()
            measurement_origin_monotonic_ns: int | None = None
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
                if prompt_release_required:
                    prompt_release_status = "awaiting_ready"
                    prompt_release_useful_basis = "not_started"
                else:
                    # Compatibility for old, non-signposted snapshots only.
                    # This is explicitly not represented as authenticated prompt
                    # release in the run record.
                    useful_work_started = True
                    measurement_origin_monotonic_ns = process_started_monotonic_ns
            except OSError as error:
                process = None
                agent_system_error = str(error)

            if process is not None and prompt_release_required:
                assert prompt_paths is not None
                assert effective_prompt_text is not None
                assert effective_prompt_sha256 is not None
                assert effective_prompt_bytes is not None
                startup_deadline_ns = process_started_monotonic_ns + int(
                    prompt_startup_timeout_seconds * 1_000_000_000
                )
                while prompt_released_record is None and agent_system_error is None:
                    now_ns = time.monotonic_ns()
                    if prompt_go_record is None and (
                        prompt_paths["go"].exists()
                        or prompt_paths["go"].is_symlink()
                        or prompt_paths["release"].exists()
                        or prompt_paths["release"].is_symlink()
                    ):
                        prompt_release_status = "unexpected_artifact_before_go"
                        prompt_release_error = (
                            "prompt GO/RELEASED artifact appeared before runner authorization"
                        )
                        agent_system_error = prompt_release_error
                        terminate_process(process)
                        break
                    if prompt_ready_record is None and (
                        prompt_paths["ready"].exists()
                        or prompt_paths["ready"].is_symlink()
                    ):
                        try:
                            prompt_ready_record = _authenticate_prompt_ready(
                                prompt_paths["ready"],
                                args,
                                run_id=run_id,
                                nonce=prompt_handshake_nonce,
                                effective_prompt_sha256=effective_prompt_sha256,
                                effective_prompt_bytes=effective_prompt_bytes,
                                process_started_monotonic_ns=(
                                    process_started_monotonic_ns
                                ),
                            )
                            os.chmod(
                                prompt_paths["ready"], 0o444, follow_symlinks=False
                            )
                            prompt_ready_descriptor = _prompt_artifact_descriptor(
                                prompt_paths["ready"],
                                prompt_ready_record,
                                "ready_sha256",
                            )
                            prompt_release_status = "ready_authenticated"
                        except BenchmarkToolError as error:
                            prompt_release_status = "invalid_ready_before_go"
                            prompt_release_error = str(error)
                            agent_system_error = str(error)
                            terminate_process(process)
                            break
                    if prompt_ready_record is not None and prompt_go_record is None:
                        minimum_window_ns = int(
                            PROMPT_GO_MINIMUM_RELEASE_WINDOW_SECONDS * 1_000_000_000
                        )
                        if now_ns + minimum_window_ns >= startup_deadline_ns:
                            prompt_startup_timeout_triggered = True
                            prompt_release_status = "startup_timeout_before_go"
                            prompt_release_error = (
                                "prompt startup timeout expired before a safe GO window"
                            )
                            agent_system_error = prompt_release_error
                            terminate_process(process)
                            break
                        try:
                            prompt_go_record = _make_prompt_go(
                                prompt_paths["go"], prompt_ready_record
                            )
                            os.chmod(
                                prompt_paths["go"], 0o444, follow_symlinks=False
                            )
                            prompt_go_descriptor = _prompt_artifact_descriptor(
                                prompt_paths["go"], prompt_go_record, "go_sha256"
                            )
                        except (OSError, RuntimeError, BenchmarkToolError) as error:
                            prompt_release_status = "go_publication_failed"
                            prompt_release_error = str(error)
                            agent_system_error = str(error)
                            terminate_process(process)
                            break
                        # GO authorizes the trusted adapter to flush turn/start.
                        # Any subsequent ambiguity is charged and never retried.
                        useful_work_started = True
                        prompt_release_useful_basis = "authenticated_go_authorization"
                        prompt_release_status = "go_issued"
                    if prompt_go_record is not None and (
                        prompt_paths["release"].exists()
                        or prompt_paths["release"].is_symlink()
                    ):
                        try:
                            prompt_released_record = _authenticate_prompt_release(
                                prompt_paths["release"],
                                args,
                                run_id=run_id,
                                nonce=prompt_handshake_nonce,
                                ready=prompt_ready_record,
                                go=prompt_go_record,
                                effective_prompt=effective_prompt_text,
                            )
                            os.chmod(
                                prompt_paths["release"], 0o444, follow_symlinks=False
                            )
                            prompt_released_descriptor = _prompt_artifact_descriptor(
                                prompt_paths["release"],
                                prompt_released_record,
                                "release_sha256",
                            )
                        except BenchmarkToolError as error:
                            prompt_release_status = "invalid_release_after_go"
                            prompt_release_error = str(error)
                            agent_system_error = str(error)
                            terminate_process(process)
                            break
                        prompt_released_monotonic_ns = prompt_released_record[
                            "released_at_monotonic_ns"
                        ]
                        measurement_origin_monotonic_ns = (
                            prompt_released_monotonic_ns
                        )
                        prompt_release_authenticated = True
                        prompt_release_timing_exact = True
                        prompt_release_useful_basis = "authenticated_release"
                        prompt_release_status = "released_authenticated"
                        break
                    exit_code = process.poll()
                    if exit_code is not None:
                        agent_exit_code = exit_code
                        if prompt_go_record is None:
                            prompt_release_status = "adapter_exit_before_go"
                            prompt_release_error = (
                                f"adapter exited with code {exit_code} before prompt GO"
                            )
                        else:
                            prompt_release_status = "release_unknown_after_go"
                            prompt_release_error = (
                                f"adapter exited with code {exit_code} after GO without "
                                "an authenticated RELEASED record"
                            )
                        agent_system_error = prompt_release_error
                        break
                    if now_ns >= startup_deadline_ns:
                        prompt_startup_timeout_triggered = True
                        if prompt_go_record is None:
                            prompt_release_status = "startup_timeout_before_go"
                            prompt_release_error = (
                                "prompt startup timeout expired before authenticated GO"
                            )
                        else:
                            prompt_release_status = "release_unknown_after_go"
                            prompt_release_error = (
                                "prompt startup timeout expired after GO without an "
                                "authenticated RELEASED record"
                            )
                        agent_system_error = prompt_release_error
                        terminate_process(process)
                        break
                    time.sleep(min(args.poll_seconds, 0.02))

            last_stamp: tuple[int, int] | None = None
            while process is not None and measurement_origin_monotonic_ns is not None:
                if ultra_attempt:
                    assert usage_path is not None
                    assert submission_monitor is not None
                    assert ultra_baseline_workspace is not None
                    exit_code = process.poll()
                    if exit_code is not None:
                        agent_exit_code = exit_code
                        break
                    barrier_paths = submission_barrier_paths(usage_path)
                    pending_call_elapsed: float | None = None
                    if (
                        barrier_paths["call"].exists()
                        or barrier_paths["call"].is_symlink()
                    ):
                        try:
                            _pending_call, pending_call_elapsed = (
                                _read_submission_call(
                                    usage_path,
                                    expected_sequence=expected_submission_sequence,
                                    prompt_released_monotonic_ns=(
                                        measurement_origin_monotonic_ns
                                    ),
                                )
                            )
                        except BenchmarkToolError as error:
                            agent_system_error = str(error)
                            terminate_process(process)
                            break
                    elapsed = _elapsed_from_prompt_release(
                        measurement_origin_monotonic_ns
                    )
                    assert provider_gate_artifacts is not None
                    assert provider_gate_source_sha256 is not None
                    assert provider_gate_catalog is not None
                    assert provider_gate_transport is not None
                    assert prompt_released_record is not None
                    assert effective_prompt_sha256 is not None
                    try:
                        live_crossing = authenticate_provider_gate_live_crossing(
                            provider_gate_artifacts["live"],
                            token_limit=args.token_limit,
                            run_id=run_id,
                            model=args.model,
                            reasoning_effort=args.reasoning_effort,
                            root_thread_id=str(
                                prompt_released_record["root_thread_id"]
                            ),
                            prompt_release_sha256=(
                                _provider_gate_prompt_release_sha256(
                                    prompt_released_record
                                )
                            ),
                            prompt_release_protocol=str(
                                prompt_released_record["protocol_version"]
                            ),
                            prompt_sha256=effective_prompt_sha256,
                            model_catalog_sha256=str(
                                provider_gate_catalog["catalog_sha256"]
                            ),
                            model_entry_sha256=str(
                                provider_gate_catalog["entry_sha256"]
                            ),
                            expected_transport_provenance=provider_gate_transport,
                            expected_source_sha256=provider_gate_source_sha256,
                        )
                    except BenchmarkToolError as error:
                        provider_gate_error = str(error)
                        provider_gate_status = "invalid_live_artifact"
                        agent_system_error = str(error)
                        terminate_process(process)
                        break
                    if live_crossing is not None:
                        crossing = live_crossing["crossing"]
                        if (
                            provider_gate_live_crossing is not None
                            and provider_gate_live_crossing["crossing"] != crossing
                        ):
                            provider_gate_error = (
                                "provider gate live crossing identity changed"
                            )
                            agent_system_error = provider_gate_error
                            terminate_process(process)
                            break
                        provider_gate_live_crossing = live_crossing
                        crossing_elapsed = (
                            crossing["commit_monotonic_ns"]
                            - measurement_origin_monotonic_ns
                        ) / 1_000_000_000
                        if crossing_elapsed < 0:
                            provider_gate_error = (
                                "provider gate crossing predates prompt release"
                            )
                            agent_system_error = provider_gate_error
                            terminate_process(process)
                            break
                        if crossing_elapsed >= args.time_limit_seconds:
                            # The wall endpoint won according to one monotonic
                            # clock.  A later provider completion cannot turn
                            # the TIME_LIMIT into a scoreable token stop.
                            timed_out = True
                            provider_gate_status = "crossing_at_or_after_wall"
                            terminate_process(process)
                            break
                        token_limited = True
                        limit_observed_tokens = crossing["completed_tokens"]
                        provider_gate_status = "live_crossing_authenticated"
                        if provider_gate_cleanup_deadline_ns is None:
                            provider_gate_cleanup_deadline_ns = (
                                time.monotonic_ns()
                                + int(
                                    PROVIDER_GATE_CLEANUP_GRACE_SECONDS
                                    * 1_000_000_000
                                )
                            )
                    if (
                        pending_call_elapsed is not None
                        and pending_call_elapsed >= args.time_limit_seconds
                    ):
                        timed_out = True
                        terminate_process(process)
                        break
                    if (
                        elapsed >= args.time_limit_seconds
                        and pending_call_elapsed is None
                        and provider_gate_live_crossing is None
                    ):
                        timed_out = True
                        terminate_process(process)
                        break
                    if (
                        pending_call_elapsed is not None
                        and not barrier_paths["request"].exists()
                        and elapsed - pending_call_elapsed > MAX_USAGE_GRACE_SECONDS
                    ):
                        agent_system_error = (
                            "submission call did not finalize an exact raw-response ledger"
                        )
                        terminate_process(process)
                        break
                    direct_submission_violation = (
                        submission_monitor.poll(submission)
                        or direct_submission_violation
                    )
                    try:
                        usage = read_token_usage(usage_path)
                    except BenchmarkToolError as error:
                        usage_measurement_error = str(error)
                        agent_system_error = str(error)
                        terminate_process(process)
                        break
                    if (
                        provider_gate_live_crossing is not None
                        and (usage is None or usage["model_tokens"] < args.token_limit)
                    ):
                        if any(
                            path.exists() or path.is_symlink()
                            for path in (
                                barrier_paths["call"],
                                barrier_paths["request"],
                                barrier_paths["ack"],
                            )
                        ):
                            provider_gate_error = (
                                "submission-barrier activity overlapped a provider crossing"
                            )
                            agent_system_error = provider_gate_error
                            terminate_process(process)
                            break
                        assert provider_gate_cleanup_deadline_ns is not None
                        if time.monotonic_ns() >= provider_gate_cleanup_deadline_ns:
                            provider_gate_error = (
                                "provider gate crossing did not receive an app-server "
                                "crossbinding within cleanup grace"
                            )
                            usage_measurement_error = provider_gate_error
                            agent_system_error = provider_gate_error
                            terminate_process(process)
                            break
                        time.sleep(min(args.poll_seconds, 0.05))
                        continue
                    if usage is not None and usage["model_tokens"] >= args.token_limit:
                        token_limited = True
                        limit_observed_tokens = _limit_observation(usage)
                        first_crossing = usage.get("first_crossing")
                        if not isinstance(first_crossing, Mapping):
                            usage_measurement_error = (
                                "Ultra token crossing lacks an authenticated "
                                "first-crossing record"
                            )
                            agent_system_error = usage_measurement_error
                            terminate_process(process)
                            break

                        # The authenticated gate has already stopped inference
                        # admission and withheld the crossing output.  Give core
                        # handler quiescence, final crossbinding, immediate child
                        # teardown, and state cleanup their frozen bounded grace.
                        # This interval begins after the token endpoint and cannot
                        # convert a pre-wall token stop into TIME_LIMIT.
                        cap_drain_deadline_ns = (
                            provider_gate_cleanup_deadline_ns
                            if provider_gate_cleanup_deadline_ns is not None
                            else time.monotonic_ns()
                            + int(
                                PROVIDER_GATE_CLEANUP_GRACE_SECONDS
                                * 1_000_000_000
                            )
                        )
                        exact_cap_usage: dict[str, Any] | None = (
                            usage
                            if exact_ultra_token_drain_error(
                                usage,
                                token_limit=args.token_limit,
                                first_crossing=first_crossing,
                            )
                            is None
                            else None
                        )
                        prior_cap_usage = usage
                        while True:
                            direct_submission_violation = (
                                submission_monitor.poll(submission)
                                or direct_submission_violation
                            )
                            if direct_submission_violation:
                                agent_system_error = (
                                    "direct Submission.lean write occurred during "
                                    "Ultra token-limit cleanup"
                                )
                                usage_measurement_error = agent_system_error
                                terminate_process(process)
                                break

                            if any(
                                path.exists() or path.is_symlink()
                                for path in (
                                    barrier_paths["call"],
                                    barrier_paths["request"],
                                    barrier_paths["ack"],
                                )
                            ):
                                agent_system_error = (
                                    "submission-barrier activity occurred after "
                                    "the Ultra token limit"
                                )
                                usage_measurement_error = agent_system_error
                                terminate_process(process)
                                break

                            exit_code = process.poll()
                            if exit_code is not None:
                                agent_exit_code = exit_code
                                if exit_code != 0:
                                    usage_measurement_error = (
                                        "Ultra provider-gated adapter did not exit "
                                        f"cleanly (exit code {exit_code})"
                                    )
                                    agent_system_error = usage_measurement_error
                                    break
                                try:
                                    final_cap_usage = read_token_usage(usage_path)
                                except BenchmarkToolError as error:
                                    usage_measurement_error = str(error)
                                    agent_system_error = str(error)
                                    break
                                final_error = exact_ultra_token_drain_error(
                                    final_cap_usage,
                                    token_limit=args.token_limit,
                                    first_crossing=first_crossing,
                                )
                                if final_error is not None:
                                    usage_measurement_error = final_error
                                    agent_system_error = final_error
                                else:
                                    assert final_cap_usage is not None
                                    if (
                                        exact_cap_usage is not None
                                        and final_cap_usage != exact_cap_usage
                                    ):
                                        usage_measurement_error = (
                                            "exact Ultra token-limit ledger changed "
                                            "before adapter exit"
                                        )
                                        agent_system_error = usage_measurement_error
                                    usage = final_cap_usage
                                break

                            try:
                                candidate_usage = read_token_usage(usage_path)
                            except BenchmarkToolError as error:
                                usage_measurement_error = str(error)
                                agent_system_error = str(error)
                                terminate_process(process)
                                break
                            if candidate_usage is None:
                                usage_measurement_error = (
                                    "Ultra token-limit ledger disappeared during cleanup"
                                )
                                agent_system_error = usage_measurement_error
                                terminate_process(process)
                                break
                            if candidate_usage.get("first_crossing") != dict(
                                first_crossing
                            ):
                                usage_measurement_error = (
                                    "Ultra token-limit first-crossing identity changed "
                                    "during cleanup"
                                )
                                agent_system_error = usage_measurement_error
                                terminate_process(process)
                                break
                            if (
                                candidate_usage["notification_sequence"]
                                < prior_cap_usage["notification_sequence"]
                                or candidate_usage["model_tokens"]
                                < prior_cap_usage["model_tokens"]
                            ):
                                usage_measurement_error = (
                                    "Ultra token-limit usage regressed during cleanup"
                                )
                                agent_system_error = usage_measurement_error
                                terminate_process(process)
                                break
                            if (
                                candidate_usage.get("interrupt_requested") is True
                                or candidate_usage.get("invalid_reasons")
                            ):
                                usage_measurement_error = (
                                    "Ultra token-limit cleanup became interrupted or invalid"
                                )
                                agent_system_error = usage_measurement_error
                                terminate_process(process)
                                break
                            candidate_error = exact_ultra_token_drain_error(
                                candidate_usage,
                                token_limit=args.token_limit,
                                first_crossing=first_crossing,
                            )
                            if candidate_error is None:
                                if (
                                    exact_cap_usage is not None
                                    and candidate_usage != exact_cap_usage
                                ):
                                    usage_measurement_error = (
                                        "exact Ultra token-limit ledger changed "
                                        "during adapter cleanup"
                                    )
                                    agent_system_error = usage_measurement_error
                                    terminate_process(process)
                                    break
                                exact_cap_usage = candidate_usage
                                usage = candidate_usage
                            elif exact_cap_usage is not None:
                                usage_measurement_error = (
                                    "exact Ultra token-limit ledger regressed before exit"
                                )
                                agent_system_error = usage_measurement_error
                                terminate_process(process)
                                break
                            else:
                                usage = candidate_usage
                            prior_cap_usage = candidate_usage

                            remaining_ns = cap_drain_deadline_ns - time.monotonic_ns()
                            if remaining_ns <= 0:
                                agent_system_error = (
                                    "Ultra adapter did not exit within the bounded "
                                    "token-limit cleanup grace"
                                )
                                usage_measurement_error = agent_system_error
                                terminate_process(process)
                                break
                            time.sleep(
                                min(
                                    args.poll_seconds,
                                    0.05,
                                    remaining_ns / 1_000_000_000,
                                )
                            )
                        break
                    if direct_submission_violation:
                        terminate_process(process)
                        break

                    request_path = barrier_paths["request"]
                    ack_path = barrier_paths["ack"]
                    if handled_request_sha256 is not None:
                        if request_path.exists() or request_path.is_symlink():
                            try:
                                still_pending = verify_authenticated_record(
                                    json.loads(
                                        _read_regular_bytes(
                                            request_path, "pending submission request"
                                        )
                                    ),
                                    "request_sha256",
                                )
                            except (RuntimeError, json.JSONDecodeError) as error:
                                agent_system_error = str(error)
                                terminate_process(process)
                                break
                            if (
                                still_pending.get("request_sha256")
                                != handled_request_sha256
                            ):
                                agent_system_error = (
                                    "pending submission request changed after rejection"
                                )
                                terminate_process(process)
                                break
                        else:
                            rejected_paths = submission_barrier_paths(
                                usage_path, expected_submission_sequence
                            )
                            if any(
                                path.exists() or path.is_symlink()
                                for path in (
                                    ack_path,
                                    rejected_paths["call"],
                                    rejected_paths["snapshot"],
                                )
                            ):
                                time.sleep(args.poll_seconds)
                                continue
                            handled_request_sha256 = None
                            expected_submission_sequence += 1
                        time.sleep(args.poll_seconds)
                        continue

                    if request_path.exists() or request_path.is_symlink():
                        try:
                            request, candidate_snapshot, _snapshot_path = (
                                _read_submission_request(
                                    usage_path,
                                    expected_sequence=expected_submission_sequence,
                                    prompt_released_monotonic_ns=(
                                        measurement_origin_monotonic_ns
                                    ),
                                    usage=usage,
                                )
                            )
                        except BenchmarkToolError as error:
                            agent_system_error = str(error)
                            terminate_process(process)
                            break
                        ultra_submission_attempted = True
                        request_elapsed = (
                            request["request_published_at_monotonic_ns"]
                            - measurement_origin_monotonic_ns
                        ) / 1_000_000_000
                        if request_elapsed < 0:
                            agent_system_error = (
                                "submission request publication predates prompt release"
                            )
                            terminate_process(process)
                            break
                        if request_elapsed >= args.time_limit_seconds:
                            timed_out = True
                            terminate_process(process)
                            break
                        frozen_workspace = workspace_parent / (
                            f"highambench-barrier-validation-{uuid.uuid4().hex}"
                        )
                        frozen_submission, frozen_inventory = (
                            _materialize_barrier_workspace(
                                ultra_baseline_workspace,
                                frozen_workspace,
                                request,
                                candidate_snapshot,
                                args.submission_relative,
                            )
                        )
                        validation_result = validate(
                            make_validation_config(
                                args,
                                frozen_workspace,
                                compile_command,
                                audit_command,
                                timeout_seconds=args.validation_timeout_seconds,
                            )
                        )
                        if request.get("validator_contract_sha256") != (
                            validator_contract_sha256
                        ):
                            raise BenchmarkToolError(
                                "submission request used the wrong validator contract"
                            )
                        validation_result = _authenticate_validation_result(
                            validation_result,
                            run_id=run_id,
                            task_id=args.task_id,
                            candidate_sha256=request["candidate_sha256"],
                            target_theorem=args.target_theorem,
                            controlled_manifest_sha256=controlled_manifest_sha256,
                            validator_contract_sha256=validator_contract_sha256,
                            submission_request_sha256=request["request_sha256"],
                            submission_sequence=request["sequence"],
                        )
                        validator_finished_elapsed = _elapsed_from_prompt_release(
                            measurement_origin_monotonic_ns
                        )
                        if _workspace_byte_inventory(frozen_workspace) != frozen_inventory:
                            raise BenchmarkToolError(
                                "immutable Ultra validation workspace changed"
                            )
                        direct_submission_violation = (
                            submission_monitor.poll(submission)
                            or direct_submission_violation
                        )
                        try:
                            repeated_request, repeated_snapshot, _ = (
                                _read_submission_request(
                                    usage_path,
                                    expected_sequence=expected_submission_sequence,
                                    prompt_released_monotonic_ns=(
                                        measurement_origin_monotonic_ns
                                    ),
                                    usage=usage,
                                )
                            )
                        except BenchmarkToolError as error:
                            agent_system_error = str(error)
                            terminate_process(process)
                            break
                        if repeated_request != request or repeated_snapshot != candidate_snapshot:
                            agent_system_error = "submission barrier changed during validation"
                            terminate_process(process)
                            break
                        if direct_submission_violation:
                            terminate_process(process)
                            break
                        if not validation_result.get("pass"):
                            last_rejected_validation = validation_result
                            if validator_finished_elapsed >= args.time_limit_seconds:
                                timed_out = True
                                terminate_process(process)
                                break
                            failure_label = str(
                                validation_result.get("failure_code") or "PROOF_ERROR"
                            )
                            ack = _write_submission_ack(
                                usage_path,
                                request,
                                decision="reject",
                                note=f"{failure_label}: candidate rejected",
                                validator_elapsed_seconds=validator_finished_elapsed,
                            )
                            del ack
                            handled_request_sha256 = request["request_sha256"]
                            shutil.rmtree(frozen_workspace, ignore_errors=True)
                            frozen_workspace = None
                            time.sleep(args.poll_seconds)
                            continue

                        accepted_boundary_ack = _write_submission_ack(
                            usage_path,
                            request,
                            decision="accept",
                            note="accepted",
                            validator_elapsed_seconds=validator_finished_elapsed,
                        )
                        accepted_boundary_request = request
                        try:
                            agent_exit_code = process.wait(
                                timeout=ACCEPTED_SUBMISSION_CLOSE_TIMEOUT_SECONDS
                            )
                        except subprocess.TimeoutExpired:
                            agent_system_error = (
                                "adapter did not close the accepted blocked tool boundary"
                            )
                            terminate_process(
                                process,
                                grace_seconds=FORCED_TERMINATION_GRACE_SECONDS,
                            )
                            agent_exit_code = process.poll()
                            break
                        if agent_exit_code != 0:
                            agent_system_error = (
                                "adapter exited with code "
                                f"{agent_exit_code} after the accepted submission "
                                "boundary; the accepted proof is not scoreable"
                            )
                            break
                        try:
                            usage = read_token_usage(usage_path)
                            if usage is None:
                                raise BenchmarkToolError(
                                    "accepted barrier has no final usage ledger"
                                )
                            _bind_final_submission_boundary(
                                usage, request, accepted_boundary_ack
                            )
                        except BenchmarkToolError as error:
                            usage_measurement_error = str(error)
                            agent_system_error = str(error)
                            break
                        accepted_barrier_artifacts = _seal_accepted_barrier_artifacts(
                            usage_path, request, accepted_boundary_ack
                        )
                        ultra_boundary_verified = True
                        first_valid_seconds = request_elapsed
                        accepted_submission_log = (
                            logs_dir / f"{run_id}.accepted.lean"
                        )
                        accepted_submission_log.write_bytes(candidate_snapshot)
                        submission_digest = sha256_file(accepted_submission_log)
                        final_submission_digest = submission_digest
                        submission.write_bytes(candidate_snapshot)
                        submission_monitor.poll(submission, runner_owned=True)
                        usage_capture = ultra_boundary_usage_capture(
                            args, usage, request
                        )
                        break
                    time.sleep(args.poll_seconds)
                    continue
                elapsed = _elapsed_from_prompt_release(
                    measurement_origin_monotonic_ns
                )
                if elapsed >= args.time_limit_seconds:
                    timed_out = True
                    terminate_process(process)
                    break
                try:
                    usage = read_token_usage(usage_path)
                except BenchmarkToolError as error:
                    usage_measurement_error = str(error)
                    agent_system_error = str(error)
                    terminate_process(process)
                    break
                if usage is not None and usage["model_tokens"] >= args.token_limit:
                    token_limited = True
                    limit_observed_tokens = _limit_observation(usage)
                    if usage.get("usage_scope") != ULTRA_USAGE_SCOPE:
                        terminate_process(process)
                        break
                if token_limited:
                    exit_code = process.poll()
                    if exit_code is not None:
                        agent_exit_code = exit_code
                        break
                    time.sleep(args.poll_seconds)
                    continue

                stamp = _submission_stamp(submission)
                if not ultra_attempt and stamp is not None and stamp != last_stamp:
                    last_stamp = stamp
                    submission_detected_at_unix_ns = time.time_ns()
                    # Live cumulative usage was polled above.  Submission
                    # validation must never run before this threshold check.
                    remaining = args.time_limit_seconds - elapsed
                    validated_candidate_sha256 = sha256_file(submission)
                    validation_result = validate(
                        make_validation_config(
                            args,
                            workspace,
                            compile_command,
                            audit_command,
                            timeout_seconds=remaining,
                        )
                    )
                    if (
                        not submission.is_file()
                        or sha256_file(submission) != validated_candidate_sha256
                    ):
                        raise BenchmarkToolError(
                            "non-Ultra candidate changed during validation"
                        )
                    validation_result = _authenticate_validation_result(
                        validation_result,
                        run_id=run_id,
                        task_id=args.task_id,
                        candidate_sha256=validated_candidate_sha256,
                        target_theorem=args.target_theorem,
                        controlled_manifest_sha256=controlled_manifest_sha256,
                        validator_contract_sha256=validator_contract_sha256,
                        submission_request_sha256=None,
                        submission_sequence=None,
                    )
                    accepted_at = _elapsed_from_prompt_release(
                        measurement_origin_monotonic_ns
                    )
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
                                submission_detected_at_unix_ns=(
                                    submission_detected_at_unix_ns
                                ),
                                grace_seconds=args.usage_grace_seconds,
                                poll_seconds=min(args.poll_seconds, 0.05),
                            )
                        except BenchmarkToolError as error:
                            usage_measurement_error = str(error)
                            agent_system_error = str(error)
                        if (
                            usage is not None
                            and usage["model_tokens"] >= args.token_limit
                        ):
                            token_limited = True
                            limit_observed_tokens = _limit_observation(usage)
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
            actual_stop_seconds = (
                _elapsed_from_prompt_release(measurement_origin_monotonic_ns)
                if measurement_origin_monotonic_ns is not None
                else 0.0
            )
            if (
                ultra_attempt
                and not ultra_boundary_verified
                and accepted_boundary_request is None
                and not token_limited
                and actual_stop_seconds >= args.time_limit_seconds
            ):
                timed_out = True

        if prompt_release_required and not prompt_release_timing_exact:
            raise BenchmarkToolError(
                prompt_release_error
                or "authenticated prompt release did not complete"
            )

        if prompt_release_required and prompt_released_record is not None:
            assert prompt_paths is not None
            assert prompt_ready_record is not None
            assert prompt_go_record is not None
            assert effective_prompt_text is not None
            try:
                reread_ready = read_authenticated_record_file(
                    prompt_paths["ready"], "ready_sha256"
                )
                reread_go = read_authenticated_record_file(
                    prompt_paths["go"], "go_sha256"
                )
                reread_release = _authenticate_prompt_release(
                    prompt_paths["release"],
                    args,
                    run_id=run_id,
                    nonce=prompt_handshake_nonce,
                    ready=prompt_ready_record,
                    go=prompt_go_record,
                    effective_prompt=effective_prompt_text,
                )
                if (
                    reread_ready != prompt_ready_record
                    or reread_go != prompt_go_record
                    or reread_release != prompt_released_record
                ):
                    raise BenchmarkToolError(
                        "prompt-handshake artifact changed after authentication"
                    )
                prompt_ready_descriptor = _prompt_artifact_descriptor(
                    prompt_paths["ready"], reread_ready, "ready_sha256"
                )
                prompt_go_descriptor = _prompt_artifact_descriptor(
                    prompt_paths["go"], reread_go, "go_sha256"
                )
                prompt_released_descriptor = _prompt_artifact_descriptor(
                    prompt_paths["release"], reread_release, "release_sha256"
                )
            except (OSError, RuntimeError, BenchmarkToolError) as error:
                prompt_release_status = "artifact_tamper_after_release"
                prompt_release_error = str(error)
                prompt_release_authenticated = False
                prompt_release_timing_exact = False
                agent_system_error = str(error)
                raise BenchmarkToolError(str(error)) from error

        try:
            final_usage = read_token_usage(usage_path)
        except BenchmarkToolError as error:
            usage_measurement_error = str(error)
            raise
        if final_usage is not None and (
            not token_limited or final_usage.get("usage_scope") == ULTRA_USAGE_SCOPE
        ):
            if (
                usage is None
                or final_usage["notification_sequence"]
                >= usage["notification_sequence"]
            ):
                usage = final_usage
        if (
            prompt_release_required
            and usage is not None
            and usage.get("root_thread_id") is not None
            and prompt_released_record is not None
            and usage.get("root_thread_id")
            != prompt_released_record.get("root_thread_id")
        ):
            raise BenchmarkToolError(
                "provider usage root disagrees with authenticated prompt release"
            )
        if ultra_attempt:
            # The live file only protects wall-clock ordering.  Recompute every
            # scoreability fact from the immutable final artifact after the
            # adapter has published its crossbound terminal ledger and exited.
            token_limited = False
            assert provider_gate_artifacts is not None
            assert provider_gate_source_sha256 is not None
            assert provider_gate_catalog is not None
            assert provider_gate_transport is not None
            try:
                if agent_exit_code != 0:
                    raise BenchmarkToolError(
                        "provider-gated Ultra adapter did not exit cleanly"
                    )
                if prompt_released_record is None or effective_prompt_sha256 is None:
                    raise BenchmarkToolError(
                        "provider gate cannot bind an unauthenticated prompt release"
                    )
                if usage is None:
                    raise BenchmarkToolError(
                        "provider gate has no final app-server usage ledger"
                    )
                provider_gate_final = authenticate_provider_gate_artifact(
                    provider_gate_artifacts["final"],
                    token_limit=args.token_limit,
                    run_id=run_id,
                    model=args.model,
                    reasoning_effort=args.reasoning_effort,
                    root_thread_id=str(prompt_released_record["root_thread_id"]),
                    prompt_release_sha256=_provider_gate_prompt_release_sha256(
                        prompt_released_record
                    ),
                    prompt_release_protocol=str(
                        prompt_released_record["protocol_version"]
                    ),
                    prompt_sha256=effective_prompt_sha256,
                    model_catalog_sha256=str(
                        provider_gate_catalog["catalog_sha256"]
                    ),
                    model_entry_sha256=str(provider_gate_catalog["entry_sha256"]),
                    expected_transport_provenance=provider_gate_transport,
                    usage=usage,
                    expected_source_sha256=provider_gate_source_sha256,
                )
                derived = provider_gate_final["derived"]
                crossing = derived["first_crossing"]
                if provider_gate_live_crossing is not None and (
                    crossing is None
                    or provider_gate_live_crossing.get("crossing") != crossing
                ):
                    raise BenchmarkToolError(
                        "sealed provider crossing differs from the first live crossing"
                    )
                if crossing is not None:
                    if prompt_released_monotonic_ns is None:
                        raise BenchmarkToolError(
                            "provider crossing lacks a prompt-release clock origin"
                        )
                    crossing_elapsed_ns = (
                        crossing["commit_monotonic_ns"]
                        - prompt_released_monotonic_ns
                    )
                    if crossing_elapsed_ns < 0:
                        raise BenchmarkToolError(
                            "provider crossing predates authenticated prompt release"
                        )
                    wall_ns = int(args.time_limit_seconds * 1_000_000_000)
                    if crossing_elapsed_ns < wall_ns:
                        # A committed, quarantined crossing wins even if final
                        # crossbinding/finalization completed after the wall.
                        token_limited = True
                        timed_out = False
                        limit_observed_tokens = crossing["completed_tokens"]
                    else:
                        # Equality belongs to the wall boundary, never TOKEN_LIMIT.
                        token_limited = False
                        timed_out = True
                        limit_observed_tokens = crossing["completed_tokens"]
                accepted_gate_boundary: Mapping[str, Any] | None = None
                if accepted_boundary_request is not None:
                    candidate_boundary = usage.get("submission_boundary")
                    if (
                        not isinstance(candidate_boundary, Mapping)
                        or candidate_boundary.get("request_sha256")
                        != accepted_boundary_request.get("request_sha256")
                    ):
                        raise BenchmarkToolError(
                            "accepted proof lacks its final gate-close boundary"
                        )
                    accepted_gate_boundary = candidate_boundary
                validate_provider_gate_outcome(
                    provider_gate_final,
                    token_limited=token_limited,
                    accepted_request=accepted_gate_boundary,
                    natural_end=bool(
                        crossing is None
                        and accepted_gate_boundary is None
                        and not timed_out
                        and agent_system_error is None
                    ),
                    timed_out=timed_out,
                )
                provider_gate_status = "final_artifact_authenticated"
            except (OSError, BenchmarkToolError) as error:
                provider_gate_error = str(error)
                provider_gate_status = "final_artifact_rejected"
                token_limited = False
                if usage_measurement_error is None:
                    usage_measurement_error = provider_gate_error
                else:
                    usage_measurement_error = (
                        f"{usage_measurement_error}; {provider_gate_error}"
                    )
                if agent_system_error is None:
                    agent_system_error = provider_gate_error
        if (
            usage is not None
            and usage["model_tokens"] >= args.token_limit
            and not token_limited
            and not ultra_attempt
        ):
            token_limited = True
            limit_observed_tokens = _limit_observation(usage)
        final_stamp = _submission_stamp(submission)
        if ultra_attempt:
            if submission_monitor is not None:
                direct_submission_violation = (
                    submission_monitor.poll(
                        submission, runner_owned=ultra_boundary_verified
                    )
                    or direct_submission_violation
                )
            if not ultra_boundary_verified and last_rejected_validation is not None:
                validation_result = last_rejected_validation
            if (
                not ultra_boundary_verified
                and usage is not None
                and usage.get("submission_boundary_exact") is True
                and agent_system_error is None
            ):
                agent_system_error = (
                    "accepted boundary appeared without runner authentication"
                )
        elif (
            not timed_out
            and not token_limited
            and agent_system_error is None
            and first_valid_seconds is None
            and final_stamp is not None
            and final_stamp != last_stamp
        ):
            submission_detected_at_unix_ns = time.time_ns()
            # The final live-usage read and cap check above deliberately precede
            # this last-chance validation too.
            remaining = max(0.1, args.time_limit_seconds - actual_stop_seconds)
            validated_candidate_sha256 = sha256_file(submission)
            validation_result = validate(
                make_validation_config(
                    args,
                    workspace,
                    compile_command,
                    audit_command,
                    timeout_seconds=remaining,
                )
            )
            if (
                not submission.is_file()
                or sha256_file(submission) != validated_candidate_sha256
            ):
                raise BenchmarkToolError(
                    "non-Ultra candidate changed during validation"
                )
            validation_result = _authenticate_validation_result(
                validation_result,
                run_id=run_id,
                task_id=args.task_id,
                candidate_sha256=validated_candidate_sha256,
                target_theorem=args.target_theorem,
                controlled_manifest_sha256=controlled_manifest_sha256,
                validator_contract_sha256=validator_contract_sha256,
                submission_request_sha256=None,
                submission_sequence=None,
            )
            if measurement_origin_monotonic_ns is None:
                raise BenchmarkToolError(
                    "cannot time final validation without prompt-release evidence"
                )
            validated_at = _elapsed_from_prompt_release(
                measurement_origin_monotonic_ns
            )
            if validation_result.get("pass"):
                if validated_at >= args.time_limit_seconds:
                    timed_out = True
                else:
                    first_valid_seconds = validated_at
                    accepted_submission_log = logs_dir / f"{run_id}.accepted.lean"
                    shutil.copy2(submission, accepted_submission_log)
                    submission_digest = sha256_file(accepted_submission_log)
                    if process is not None:
                        try:
                            usage, usage_capture = wait_for_usage_after_acceptance(
                                process,
                                usage_path,
                                usage,
                                submission_detected_at_unix_ns=(
                                    submission_detected_at_unix_ns
                                ),
                                grace_seconds=args.usage_grace_seconds,
                                poll_seconds=min(args.poll_seconds, 0.05),
                            )
                        except BenchmarkToolError as error:
                            usage_measurement_error = str(error)
                            agent_system_error = str(error)
                    if (
                        usage is not None
                        and usage["model_tokens"] >= args.token_limit
                    ):
                        token_limited = True
                        limit_observed_tokens = _limit_observation(usage)
            elif validated_at >= args.time_limit_seconds:
                timed_out = True

        final_submission_present = bool(
            submission is not None and submission.is_file()
        )
        if final_submission_present:
            assert submission is not None
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

        if ultra_attempt and timed_out and not ultra_boundary_verified:
            # In the frozen app-server protocol RawResponseCompleted.usage is
            # optional and is emitted only from ResponseEvent::Completed.
            # turn/interrupt (and terminating the adapter here) drops an active
            # provider stream, so both the raw-response and cumulative streams
            # can omit the same partial response.  A projection-consistent final
            # file would therefore still be only a completed-response lower
            # bound at the wall endpoint.  Preserve it as an incident, but never
            # present it as the exact §6 token measure of a scored TIME_LIMIT.
            usage_measurement_error = (
                ULTRA_WALL_TIMEOUT_USAGE_ERROR
                if usage_measurement_error is None
                else f"{usage_measurement_error}; {ULTRA_WALL_TIMEOUT_USAGE_ERROR}"
            )

        startup_agent_failure = (
            agent_exit_code not in (None, 0)
            and not submission.is_file()
            and usage is None
        )

        startup_error = agent_system_error
        if (
            ultra_attempt
            and not (
                type(agent_exit_code) is int and agent_exit_code == 0
            )
            and startup_error is None
        ):
            startup_error = (
                f"Ultra adapter exited with code {agent_exit_code}; "
                "the attempt did not reach a clean scoreable stop"
            )
        if startup_agent_failure and startup_error is None:
            startup_error = (
                f"agent adapter exited with code {agent_exit_code} before producing "
                "a submission or exact provider usage"
            )
        passed, failure_code, failure_note = classify_final_outcome(
            timed_out=timed_out,
            token_limited=token_limited,
            submission_present=submission.is_file(),
            ultra_submission_attempted=(
                ultra_attempt and ultra_submission_attempted
            ),
            direct_submission_violation=direct_submission_violation,
            startup_agent_failure=startup_agent_failure,
            useful_work_started=useful_work_started,
            network_violation=network_violation,
            first_valid_seconds=first_valid_seconds,
            validation_result=validation_result,
            agent_system_error=startup_error,
            usage=usage,
        )

        if validation_result is not None:
            write_json(validation_log, validation_result)
            validation_log_sha256 = sha256_file(validation_log)
            validation_record_sha256 = validation_result.get("record_sha256")
        library_use = False if args.condition == "N" else (
            validation_result.get("library_use") if validation_result else None
        )
        library_declarations = library_declaration_names(
            validation_result.get("library_declarations", []) if validation_result else []
        )
        token_measurement = token_measurement_record(
            args,
            usage,
            usage_capture,
            limit_triggered=token_limited,
            limit_observed_tokens=limit_observed_tokens,
            trusted_usage_path_outside_workspace=trusted_usage_path_ready,
            measurement_error=usage_measurement_error,
        )
        protocol = protocol_status(args, n_preflight=n_preflight)
        apply_token_protocol_status(
            protocol,
            args,
            usage,
            token_measurement,
            failure_code=failure_code,
            proof_accepted=first_valid_seconds is not None,
        )
        apply_ultra_boundary_deviation(
            protocol,
            args,
            authenticated_boundary_verified=ultra_boundary_verified,
            proof_accepted=first_valid_seconds is not None,
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
        protocol["verified"]["authenticated_prompt_release"] = bool(
            prompt_release_authenticated and prompt_release_timing_exact
        )
        gate_authenticated = bool(
            provider_gate_final is not None
            and provider_gate_final.get("authenticated") is True
        )
        gate_deliveries_reconciled = bool(
            gate_authenticated
            and provider_gate_final["derived"].get(
                "appserver_deliveries_reconciled"
            )
            is True
        )
        gate_state = (
            provider_gate_final["record"]["state"]
            if gate_authenticated
            else None
        )
        gate_endpoint_exact = bool(
            gate_authenticated
            and isinstance(gate_state, Mapping)
            and (
                (
                    failure_code == "TOKEN_LIMIT"
                    and token_limited
                    and gate_state.get("close_reason") == "token_limit"
                    and gate_state.get("crossing") is not None
                )
                or (
                    first_valid_seconds is not None
                    and gate_state.get("close_reason") == "accepted_submission"
                    and gate_state.get("crossing") is None
                )
                or (
                    failure_code not in ("TOKEN_LIMIT", "TIME_LIMIT")
                    and first_valid_seconds is None
                    and gate_state.get("close_reason") == "natural_end"
                    and gate_state.get("crossing") is None
                )
            )
        )
        protocol["verified"]["authenticated_provider_token_gate"] = (
            gate_authenticated if ultra_attempt else True
        )
        protocol["verified"]["provider_gate_appserver_deliveries_reconciled"] = (
            gate_deliveries_reconciled if ultra_attempt else True
        )
        protocol["verified"]["provider_gate_terminal_endpoint"] = (
            gate_endpoint_exact if ultra_attempt else True
        )
        if ultra_attempt and not gate_endpoint_exact:
            protocol["complete"] = False
            protocol["notes"].append(
                "Ultra outcome lacks an independently authenticated sealed provider-gate endpoint"
            )
        if prompt_release_required and not prompt_release_timing_exact:
            protocol["complete"] = False
            protocol["notes"].append(
                "exact prompt-release timing lacks an authenticated RELEASED record"
            )
        if not network_violation["integrity_ok"]:
            protocol["complete"] = False
            protocol["notes"].append(
                "the per-run network-violation marker failed its integrity check"
            )
        if (
            ultra_attempt
            and not (
                type(agent_exit_code) is int and agent_exit_code == 0
            )
        ):
            protocol["complete"] = False
            protocol["notes"].append(
                "the Ultra adapter did not exit cleanly, so the attempt is unscorable"
            )
        scored = protocol["complete"] and (
            failure_code != "SYSTEM_ERROR" or useful_work_started
        ) and (not prompt_release_required or prompt_release_timing_exact) and (
            not ultra_attempt or gate_endpoint_exact
        )
        prompt_release_record = _prompt_release_run_record(
            required=prompt_release_required,
            status=prompt_release_status,
            authenticated=prompt_release_authenticated,
            timing_exact=prompt_release_timing_exact,
            useful_work_basis=prompt_release_useful_basis,
            startup_timeout_seconds=prompt_startup_timeout_seconds,
            startup_timeout_triggered=prompt_startup_timeout_triggered,
            nonce=prompt_handshake_nonce,
            paths=prompt_paths,
            effective_prompt_sha256=effective_prompt_sha256,
            effective_prompt_bytes=effective_prompt_bytes,
            ready_descriptor=prompt_ready_descriptor,
            go_descriptor=prompt_go_descriptor,
            released_descriptor=prompt_released_descriptor,
            stale_artifacts_removed=prompt_stale_artifacts_removed,
            error=prompt_release_error,
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
                "time_measurement": (
                    "authenticated CLOCK_MONOTONIC turn/start write to authenticated "
                    "nested submission-boundary publication after outer "
                    "exec raw-response completion with inner submit_proof blocked; hidden "
                    "validation certifies "
                    "the immutable requested bytes"
                    if prompt_release_required and ultra_attempt
                    else "authenticated CLOCK_MONOTONIC turn/start write to validator acceptance"
                    if prompt_release_required
                    else "legacy adapter process start to authenticated nested submission-boundary publication after outer exec raw-response completion with inner submit_proof blocked"
                    if ultra_attempt
                    else "legacy adapter process start to validator acceptance"
                ),
                "token_usage": usage,
                "token_measurement": token_measurement,
                "library_use": library_use,
                "library_declarations": library_declarations,
                "network_violation": network_violation,
                "failure_precedence": ",".join(FAILURE_PRECEDENCE),
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
                "ultra_submission_boundary": (
                    {
                        "verified": ultra_boundary_verified,
                        "sequence": accepted_boundary_request.get("sequence"),
                        "request_sha256": accepted_boundary_request.get(
                            "request_sha256"
                        ),
                        "ack_sha256": accepted_boundary_ack.get("ack_sha256"),
                        "artifacts": accepted_barrier_artifacts,
                    }
                    if accepted_boundary_request is not None
                    and accepted_boundary_ack is not None
                    else {"verified": False}
                ),
                "agent_exit_code": agent_exit_code,
                "agent_system_error": startup_error,
                "agent_command": agent_command,
                "prompt_provenance": prompt_provenance,
                "prompt_release": prompt_release_record,
                "provider_token_gate": provider_gate_run_record(
                    required=ultra_attempt,
                    status=provider_gate_status,
                    paths=provider_gate_artifacts,
                    source_sha256=provider_gate_source_sha256,
                    catalog=provider_gate_catalog,
                    transport_provenance=provider_gate_transport,
                    live_crossing=provider_gate_live_crossing,
                    final=provider_gate_final,
                    error=provider_gate_error,
                ),
                "agent_log": str(agent_log),
                "validation_log": str(validation_log) if validation_result else None,
                "validation_log_sha256": validation_log_sha256,
                "validation_record_sha256": validation_record_sha256,
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
        if process is not None:
            agent_exit_code = process.poll()
        if prompt_released_monotonic_ns is not None:
            with contextlib.suppress(BenchmarkToolError):
                actual_stop_seconds = _elapsed_from_prompt_release(
                    prompt_released_monotonic_ns
                )
        if prompt_release_required and prompt_release_error is None:
            prompt_release_error = str(error)
        exception_network = (
            inspect_network_violation_marker(network_marker, network_monitor)
            if network_marker is not None and network_monitor is not None
            else network_violation
        )
        authenticated_exception_validation: dict[str, Any] | None = None
        for candidate_validation in (validation_result, last_rejected_validation):
            if (
                isinstance(candidate_validation, dict)
                and isinstance(candidate_validation.get("authentication"), Mapping)
                and isinstance(candidate_validation.get("record_sha256"), str)
                and re.fullmatch(
                    r"[0-9a-f]{64}", candidate_validation["record_sha256"]
                )
            ):
                authenticated_exception_validation = candidate_validation
                break
        exception_submission_present = bool(
            submission is not None and submission.is_file()
        )
        if exception_submission_present:
            assert submission is not None
            final_submission_digest = sha256_file(submission)
            if submission_digest is None:
                submission_digest = final_submission_digest
        exception_startup_failure = bool(not useful_work_started)
        _exception_passed, exception_failure_code, exception_failure_note = (
            classify_final_outcome(
                timed_out=timed_out,
                token_limited=token_limited,
                submission_present=exception_submission_present,
                ultra_submission_attempted=(
                    ultra_attempt and ultra_submission_attempted
                ),
                direct_submission_violation=direct_submission_violation,
                startup_agent_failure=exception_startup_failure,
                useful_work_started=useful_work_started,
                network_violation=exception_network,
                first_valid_seconds=first_valid_seconds,
                validation_result=authenticated_exception_validation,
                agent_system_error=str(error),
                usage=usage,
            )
        )
        assert exception_failure_code is not None
        if prompt_release_required and not prompt_release_timing_exact:
            exception_failure_code = "SYSTEM_ERROR"
            exception_failure_note = prompt_release_error or str(error)
        if authenticated_exception_validation is not None:
            write_json(validation_log, authenticated_exception_validation)
            validation_log_sha256 = sha256_file(validation_log)
            validation_record_sha256 = authenticated_exception_validation.get(
                "record_sha256"
            )
        if ultra_attempt and timed_out and not ultra_boundary_verified:
            usage_measurement_error = (
                ULTRA_WALL_TIMEOUT_USAGE_ERROR
                if usage_measurement_error is None
                else f"{usage_measurement_error}; {ULTRA_WALL_TIMEOUT_USAGE_ERROR}"
            )
        exception_protocol = protocol_status(args, n_preflight=n_preflight)
        exception_token_measurement = token_measurement_record(
            args,
            usage,
            usage_capture,
            limit_triggered=token_limited,
            limit_observed_tokens=limit_observed_tokens,
            trusted_usage_path_outside_workspace=trusted_usage_path_ready,
            measurement_error=usage_measurement_error,
        )
        apply_token_protocol_status(
            exception_protocol,
            args,
            usage,
            exception_token_measurement,
            failure_code=exception_failure_code,
            proof_accepted=first_valid_seconds is not None,
        )
        apply_ultra_boundary_deviation(
            exception_protocol,
            args,
            authenticated_boundary_verified=ultra_boundary_verified,
            proof_accepted=first_valid_seconds is not None,
        )
        exception_protocol["verified"]["network_violation_marker_integrity"] = (
            exception_network["integrity_ok"]
        )
        exception_protocol["verified"]["authenticated_prompt_release"] = bool(
            prompt_release_authenticated and prompt_release_timing_exact
        )
        exception_protocol["verified"]["authenticated_provider_token_gate"] = (
            not ultra_attempt
        )
        exception_protocol["verified"][
            "provider_gate_appserver_deliveries_reconciled"
        ] = not ultra_attempt
        exception_protocol["verified"]["provider_gate_terminal_endpoint"] = (
            not ultra_attempt
        )
        if ultra_attempt:
            exception_protocol["complete"] = False
            exception_protocol["notes"].append(
                "Ultra exception path did not authenticate a sealed provider-gate endpoint"
            )
        if prompt_release_required and not prompt_release_timing_exact:
            exception_protocol["complete"] = False
            exception_protocol["notes"].append(
                "exact prompt-release timing lacks an authenticated RELEASED record"
            )
        if not exception_network["integrity_ok"]:
            exception_protocol["complete"] = False
            exception_protocol["notes"].append(
                "the per-run network-violation marker failed its integrity check"
            )
        if (
            ultra_attempt
            and not (
                type(agent_exit_code) is int and agent_exit_code == 0
            )
        ):
            exception_protocol["complete"] = False
            exception_protocol["notes"].append(
                "the Ultra adapter did not exit cleanly, so the attempt is unscorable"
            )
        prompt_release_record = _prompt_release_run_record(
            required=prompt_release_required,
            status=prompt_release_status,
            authenticated=prompt_release_authenticated,
            timing_exact=prompt_release_timing_exact,
            useful_work_basis=prompt_release_useful_basis,
            startup_timeout_seconds=prompt_startup_timeout_seconds,
            startup_timeout_triggered=prompt_startup_timeout_triggered,
            nonce=prompt_handshake_nonce,
            paths=prompt_paths,
            effective_prompt_sha256=effective_prompt_sha256,
            effective_prompt_bytes=effective_prompt_bytes,
            ready_descriptor=prompt_ready_descriptor,
            go_descriptor=prompt_go_descriptor,
            released_descriptor=prompt_released_descriptor,
            stale_artifacts_removed=prompt_stale_artifacts_removed,
            error=prompt_release_error,
        )
        record.update(
            {
                "started_at_utc": started_at,
                "finished_at_utc": utc_now(),
                "pass": False,
                "useful_work_started": useful_work_started,
                "scored": (
                    useful_work_started
                    and exception_protocol["complete"]
                    and not ultra_attempt
                ),
                "failure_code": exception_failure_code,
                "failure_note": exception_failure_note,
                "actual_stop_seconds": round(actual_stop_seconds, 6),
                "scored_elapsed_seconds": args.time_limit_seconds,
                "time_measurement": (
                    "authenticated CLOCK_MONOTONIC turn/start write to authenticated "
                    "nested submission-boundary publication after outer "
                    "exec raw-response completion with inner submit_proof blocked; hidden "
                    "validation certifies "
                    "the immutable requested bytes"
                    if prompt_release_required and ultra_attempt
                    else "authenticated CLOCK_MONOTONIC turn/start write to validator acceptance"
                    if prompt_release_required
                    else "legacy adapter process start to authenticated nested submission-boundary publication after outer exec raw-response completion with inner submit_proof blocked"
                    if ultra_attempt
                    else "legacy adapter process start to validator acceptance"
                ),
                "token_usage": usage,
                "token_measurement": exception_token_measurement,
                "library_use": (
                    False
                    if args.condition == "N"
                    else authenticated_exception_validation.get("library_use")
                    if authenticated_exception_validation
                    else None
                ),
                "library_declarations": library_declaration_names(
                    authenticated_exception_validation.get(
                        "library_declarations", []
                    )
                    if authenticated_exception_validation
                    else []
                ),
                "network_violation": exception_network,
                "failure_precedence": ",".join(FAILURE_PRECEDENCE),
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
                "ultra_submission_boundary": {"verified": False},
                "agent_exit_code": agent_exit_code,
                "agent_system_error": str(error),
                "agent_command": locals().get("agent_command"),
                "prompt_provenance": prompt_provenance,
                "prompt_release": prompt_release_record,
                "provider_token_gate": provider_gate_run_record(
                    required=ultra_attempt,
                    status=provider_gate_status,
                    paths=provider_gate_artifacts,
                    source_sha256=provider_gate_source_sha256,
                    catalog=provider_gate_catalog,
                    transport_provenance=provider_gate_transport,
                    live_crossing=provider_gate_live_crossing,
                    final=provider_gate_final,
                    error=provider_gate_error or str(error),
                ),
                "agent_log": str(agent_log),
                "validation_log": (
                    str(validation_log)
                    if authenticated_exception_validation is not None
                    else None
                ),
                "validation_log_sha256": validation_log_sha256,
                "validation_record_sha256": validation_record_sha256,
                "n_preflight": n_preflight,
                "protocol": exception_protocol,
                "workspace_retained": args.keep_workspace,
                "workspace": str(workspace) if args.keep_workspace else None,
            }
        )
        return record
    finally:
        if process is not None and process.poll() is None:
            terminate_process(process)
        if network_monitor is not None:
            network_monitor.close()
        if submission_monitor is not None:
            submission_monitor.close()
        if workspace.exists() and not args.keep_workspace:
            shutil.rmtree(workspace, ignore_errors=True)
        if frozen_workspace is not None and frozen_workspace.exists():
            shutil.rmtree(frozen_workspace, ignore_errors=True)
        if ultra_baseline_workspace is not None and ultra_baseline_workspace.exists():
            shutil.rmtree(ultra_baseline_workspace, ignore_errors=True)
        if ultra_attempt and usage_path is not None and not ultra_boundary_verified:
            cleanup_paths = submission_barrier_paths(usage_path)
            for path in (
                cleanup_paths["request"],
                cleanup_paths["ack"],
                cleanup_paths["call"],
                cleanup_paths["challenge"],
                Path(str(cleanup_paths["request"]) + ".tmp"),
                Path(str(cleanup_paths["ack"]) + ".tmp"),
                Path(str(cleanup_paths["call"]) + ".tmp"),
                Path(str(cleanup_paths["challenge"]) + ".tmp"),
            ):
                with contextlib.suppress(OSError):
                    path.unlink()
            for path in usage_path.parent.glob(
                usage_path.name + ".submission-*.lean"
            ):
                with contextlib.suppress(OSError):
                    path.unlink()


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
    parser.add_argument(
        "--reject-workspace-local-module-imports",
        action="store_true",
        help="reject imports resolving to model-created workspace modules",
    )
    parser.add_argument("--prompt-relative")
    parser.add_argument(
        "--usage-output",
        type=Path,
        required=True,
        help="absolute trusted adapter output path below --logs-dir",
    )
    parser.add_argument("--usage-relative", help=argparse.SUPPRESS)

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
        default=MAX_USAGE_GRACE_SECONDS,
        help=(
            "bounded post-acceptance usage capture or post-token-limit adapter "
            "cleanup; neither changes the measured proof/token stop endpoint"
        ),
    )
    parser.add_argument(
        "--prompt-startup-timeout-seconds",
        type=float,
        default=120.0,
        help=(
            "unmeasured READY/GO/RELEASED startup deadline before the exact "
            "benchmark wall clock begins"
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
    if not 0 < args.prompt_startup_timeout_seconds < float("inf"):
        raise BenchmarkToolError("prompt startup timeout must be finite and positive")
    if args.token_limit <= 0:
        raise BenchmarkToolError("token limit must be positive")
    if args.poll_seconds <= 0:
        raise BenchmarkToolError("poll interval must be positive")
    if not 0 <= args.usage_grace_seconds <= MAX_USAGE_GRACE_SECONDS:
        raise BenchmarkToolError(
            f"usage grace must be between 0 and {MAX_USAGE_GRACE_SECONDS:g} seconds"
        )
    trusted_usage_output(args, args.logs_dir.resolve())
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
