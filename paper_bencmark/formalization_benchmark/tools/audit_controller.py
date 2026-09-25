from __future__ import annotations

import json
import os
import shutil
import stat
import time
from concurrent.futures import Future, ThreadPoolExecutor
from pathlib import Path
from typing import Any, Callable, Iterable

from codex_driver import CodexDriver, ProviderCapabilityError, TurnResult
from common import (
    BenchmarkError,
    load_json,
    make_repair_feedback,
    sha256_bytes,
    sha256_file,
    utc_now,
    write_bytes_atomic,
    write_json_atomic,
)


ROOT = Path(__file__).resolve().parents[1]
PROMPTS = ROOT / "audit" / "prompts"
SCHEMAS = ROOT / "audit" / "schemas"
SEMANTIC_CHECK_IDS = [f"S{index:02d}" for index in range(1, 17)]
FAITHFUL_CLASSIFICATIONS = {"faithful-equivalent", "faithful-stronger"}
UNFAITHFUL_CLASSIFICATIONS = {
    "unfaithful-weaker",
    "unfaithful-different",
}
AUDIT_EXECUTION_PLAN = {
    "schema_version": "formalization-audit-execution-plan-1",
    "maximum_concurrent_roles": 2,
    "initial_parallel_roles": ["blind-translation", "direct-judge"],
    "role_prerequisites": {
        "blind-translation": [],
        "direct-judge": [],
        "roundtrip-judge": ["blind-translation"],
        "adjudicator": [
            "blind-translation",
            "direct-judge",
            "roundtrip-judge",
        ],
    },
    "formalizers_tasks_and_conditions_sequential": True,
}


def audit_evidence_manifest(audit_root: Path) -> dict[str, Any]:
    """Hash the complete non-self-referential evidence closure of an audit."""

    if not audit_root.is_dir() or audit_root.is_symlink():
        raise BenchmarkError(f"audit root is missing or unsafe: {audit_root}")
    entries: list[dict[str, Any]] = []
    for path in sorted(
        audit_root.rglob("*"), key=lambda item: item.relative_to(audit_root).as_posix()
    ):
        relative = path.relative_to(audit_root).as_posix()
        metadata = path.lstat()
        if stat.S_ISLNK(metadata.st_mode):
            raise BenchmarkError(f"audit evidence contains a symlink: {relative}")
        if stat.S_ISDIR(metadata.st_mode):
            continue
        if not stat.S_ISREG(metadata.st_mode):
            raise BenchmarkError(f"audit evidence contains a special file: {relative}")
        if relative in {"decision.json", "incident.json"}:
            continue
        entries.append(
            {
                "relative_path": relative,
                "bytes": metadata.st_size,
                "sha256": sha256_file(path),
            }
        )
    payload = json.dumps(entries, sort_keys=True, separators=(",", ":")).encode("utf-8")
    return {
        "schema_version": "formalization-audit-evidence-manifest-1",
        "entries": entries,
        "tree_sha256": sha256_bytes(payload),
    }


def _copy_private(source: Path, destination: Path) -> None:
    if not source.is_file() or source.is_symlink():
        raise BenchmarkError(f"audit input is missing or unsafe: {source}")
    destination.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(source, destination)
    os.chmod(destination, 0o400)


def _parse_agent_json(result: TurnResult, artifact_dir: Path) -> dict[str, Any]:
    if result.timed_out or result.exit_code != 0:
        raise BenchmarkError(
            f"auditor failed (exit={result.exit_code}, timeout={result.timed_out})"
        )
    try:
        value = json.loads(result.final_message)
    except json.JSONDecodeError as error:
        raise BenchmarkError(f"auditor returned non-JSON output: {error}") from error
    if not isinstance(value, dict):
        raise BenchmarkError("auditor output is not a JSON object")
    write_json_atomic(artifact_dir / "output.json", value, mode=0o400)
    return value


def _nonempty_string_list(value: Any) -> bool:
    return isinstance(value, list) and all(
        isinstance(item, str) and bool(item.strip()) for item in value
    )


def _valid_mismatches(value: Any) -> bool:
    expected = {"paper_requirement", "candidate_mismatch", "severity"}
    return isinstance(value, list) and all(
        isinstance(item, dict)
        and set(item) == expected
        and isinstance(item["paper_requirement"], str)
        and bool(item["paper_requirement"].strip())
        and isinstance(item["candidate_mismatch"], str)
        and bool(item["candidate_mismatch"].strip())
        and item["severity"] in {"critical", "major", "minor"}
        for item in value
    )


def _dependency_identity(dossier: dict[str, Any]) -> list[tuple[str, str]]:
    dependencies = dossier.get("dependencies")
    if not isinstance(dependencies, list):
        raise BenchmarkError("semantic dossier has no dependency inventory")
    result: list[tuple[str, str]] = []
    for dependency in dependencies:
        if (
            not isinstance(dependency, dict)
            or not isinstance(dependency.get("id"), str)
            or not isinstance(dependency.get("name"), str)
        ):
            raise BenchmarkError("semantic dossier dependency inventory is malformed")
        result.append((dependency["id"], dependency["name"]))
    return result


def _validate_dependency_coverage(
    value: Any,
    expected: list[tuple[str, str]],
    *,
    direct: bool,
) -> None:
    fields = (
        {"id", "name", "interpretation", "effect_on_target", "paper_match", "status"}
        if direct
        else {"id", "name", "meaning", "effect_on_target", "status"}
    )
    statuses = (
        {"pass", "fail", "unclear", "not-applicable"}
        if direct
        else {"understood", "unclear"}
    )
    if not isinstance(value, list) or len(value) != len(expected):
        raise BenchmarkError("auditor dependency coverage is incomplete")
    for record, (dependency_id, _dependency_name) in zip(value, expected, strict=True):
        if (
            not isinstance(record, dict)
            or set(record) != fields
            or record.get("id") != dependency_id
            or record.get("status") not in statuses
            or any(
                not isinstance(record.get(field), str) or not record[field].strip()
                for field in fields - {"status"}
            )
        ):
            raise BenchmarkError(
                f"auditor dependency record does not match {dependency_id}"
            )


def _validate_translation(
    value: dict[str, Any],
    semantic_sha256: str,
    dependencies: list[tuple[str, str]],
) -> None:
    if (
        set(value)
        != {
            "role",
            "semantic_sha256",
            "dependency_coverage",
            "translation",
            "ambiguities",
            "vacuity_risks",
        }
        or value.get("role") != "blind-translation"
        or value.get("semantic_sha256") != semantic_sha256
        or not _nonempty_string_list(value.get("ambiguities"))
        or not _nonempty_string_list(value.get("vacuity_risks"))
    ):
        raise BenchmarkError("blind translation failed its semantic contract")
    _validate_dependency_coverage(
        value["dependency_coverage"], dependencies, direct=False
    )
    translation = value.get("translation")
    if (
        not isinstance(translation, dict)
        or set(translation)
        != {
            "binders",
            "hypotheses",
            "conclusions",
            "mathematical_definitions",
            "proposition_plain_english",
        }
        or not _nonempty_string_list(translation.get("binders"))
        or not _nonempty_string_list(translation.get("hypotheses"))
        or not _nonempty_string_list(translation.get("conclusions"))
        or not translation["conclusions"]
        or not _nonempty_string_list(translation.get("mathematical_definitions"))
        or not isinstance(translation.get("proposition_plain_english"), str)
        or not translation["proposition_plain_english"].strip()
    ):
        raise BenchmarkError("blind translation is incomplete")


def _validate_implications(value: Any, *, allow_unclear: bool) -> tuple[str, str]:
    if not isinstance(value, dict) or set(value) != {
        "candidate_implies_source",
        "source_implies_candidate",
    }:
        raise BenchmarkError("judge implication record is malformed")
    allowed = {"yes", "no", "unclear"} if allow_unclear else {"yes", "no"}
    verdicts: list[str] = []
    for direction in ("candidate_implies_source", "source_implies_candidate"):
        record = value.get(direction)
        if (
            not isinstance(record, dict)
            or set(record) != {"verdict", "reasoning"}
            or record.get("verdict") not in allowed
            or not isinstance(record.get("reasoning"), str)
            or not record["reasoning"].strip()
        ):
            raise BenchmarkError(f"judge implication direction is malformed: {direction}")
        verdicts.append(record["verdict"])
    return verdicts[0], verdicts[1]


def _classification_for_implications(
    candidate_implies_source: str, source_implies_candidate: str
) -> str:
    if "unclear" in {candidate_implies_source, source_implies_candidate}:
        return "undetermined"
    return {
        ("yes", "yes"): "faithful-equivalent",
        ("yes", "no"): "faithful-stronger",
        ("no", "yes"): "unfaithful-weaker",
        ("no", "no"): "unfaithful-different",
    }[(candidate_implies_source, source_implies_candidate)]


def _validate_semantic_checklist(value: Any, *, evidence_field: str) -> None:
    expected_fields = {
        "id",
        "status",
        "paper_evidence",
        evidence_field,
        "reasoning",
    }
    if not isinstance(value, list) or len(value) != len(SEMANTIC_CHECK_IDS):
        raise BenchmarkError("judge omitted one or more mandatory semantic checks")
    for record, check_id in zip(value, SEMANTIC_CHECK_IDS, strict=True):
        if (
            not isinstance(record, dict)
            or set(record) != expected_fields
            or record.get("id") != check_id
            or record.get("status")
            not in {"pass", "fail", "unclear", "not-applicable"}
            or any(
                not isinstance(record.get(field), str) or not record[field].strip()
                for field in expected_fields - {"id", "status"}
            )
        ):
            raise BenchmarkError(f"judge semantic check is malformed: {check_id}")


def _validate_judgment(
    value: dict[str, Any],
    *,
    role: str,
    paper_sha256: str,
    semantic_sha256: str,
    dependencies: list[tuple[str, str]],
) -> None:
    direct = role == "direct-judge"
    expected_fields = {
        "role",
        "paper_sha256",
        "candidate_semantic_sha256",
        "semantic_checklist",
        "implications",
        "classification",
        "accepted",
        "requires_adjudication",
        "mismatches",
        "uncertainties",
        "rationale",
    }
    if direct:
        expected_fields.add("dependency_coverage")
    if (
        set(value) != expected_fields
        or value.get("role") != role
        or value.get("paper_sha256") != paper_sha256
        or value.get("candidate_semantic_sha256") != semantic_sha256
        or value.get("classification")
        not in {
            *FAITHFUL_CLASSIFICATIONS,
            *UNFAITHFUL_CLASSIFICATIONS,
            "undetermined",
        }
        or not isinstance(value.get("accepted"), bool)
        or not isinstance(value.get("requires_adjudication"), bool)
        or not _valid_mismatches(value.get("mismatches"))
        or not _nonempty_string_list(value.get("uncertainties"))
        or not isinstance(value.get("rationale"), str)
        or not value["rationale"].strip()
    ):
        raise BenchmarkError(f"{role} failed its semantic contract")
    if direct:
        _validate_dependency_coverage(
            value["dependency_coverage"], dependencies, direct=True
        )
    _validate_semantic_checklist(
        value["semantic_checklist"],
        evidence_field="candidate_evidence" if direct else "translation_evidence",
    )
    implication_pair = _validate_implications(
        value["implications"], allow_unclear=True
    )
    expected_classification = _classification_for_implications(*implication_pair)
    # An inconsistent candidate can imply the source only in the vacuous,
    # material-implication sense. That is not faithful strengthening. Preserve
    # the judge's literal implication record while requiring an explicit S16
    # nonvacuity failure and an unfaithful-different classification.
    vacuous_stronger = (
        implication_pair == ("yes", "no")
        and value["classification"] == "unfaithful-different"
        and value["semantic_checklist"][-1]["id"] == "S16"
        and value["semantic_checklist"][-1]["status"] == "fail"
    )
    if value["classification"] != expected_classification and not vacuous_stronger:
        raise BenchmarkError(f"{role} classification contradicts its implications")
    expected_accepted = value["classification"] in FAITHFUL_CLASSIFICATIONS
    if value["accepted"] != expected_accepted:
        raise BenchmarkError(f"{role} accepted flag contradicts its classification")
    unresolved = (
        value["classification"] == "undetermined"
        or any(item["status"] == "unclear" for item in value["semantic_checklist"])
        or (
            direct
            and any(
                item["status"] == "unclear"
                for item in value["dependency_coverage"]
            )
        )
    )
    if unresolved and not value["requires_adjudication"]:
        raise BenchmarkError(f"{role} suppressed mandatory adjudication")
    recorded_failure = any(
        item["status"] == "fail" for item in value["semantic_checklist"]
    ) or (
        direct
        and any(
            item["status"] == "fail" for item in value["dependency_coverage"]
        )
    )
    if recorded_failure and value["classification"] in FAITHFUL_CLASSIFICATIONS:
        raise BenchmarkError(f"{role} accepted despite a failed semantic check")
    if value["accepted"] and (
        value["mismatches"] or value["uncertainties"]
    ):
        raise BenchmarkError(f"{role} returned a contradictory faithful judgment")
    if (
        value["classification"] in UNFAITHFUL_CLASSIFICATIONS
        and not value["mismatches"]
    ):
        raise BenchmarkError(f"{role} returned unfaithful without a concrete mismatch")
    if value["classification"] == "undetermined" and not value["uncertainties"]:
        raise BenchmarkError(f"{role} returned undetermined without an uncertainty")


def _validate_adjudication(
    value: dict[str, Any],
    *,
    paper_sha256: str,
    semantic_sha256: str,
    trigger: list[str],
) -> None:
    if (
        set(value)
        != {
            "role",
            "paper_sha256",
            "candidate_semantic_sha256",
            "trigger",
            "resolved_items",
            "implications",
            "classification",
            "verdict",
            "mismatches",
            "remaining_uncertainties",
            "rationale",
        }
        or value.get("role") != "adjudicator"
        or value.get("paper_sha256") != paper_sha256
        or value.get("candidate_semantic_sha256") != semantic_sha256
        or value.get("trigger") != trigger
        or not isinstance(value.get("resolved_items"), list)
        or not value["resolved_items"]
        or value.get("classification")
        not in {*FAITHFUL_CLASSIFICATIONS, *UNFAITHFUL_CLASSIFICATIONS}
        or value.get("verdict") not in ("faithful", "unfaithful")
        or not _valid_mismatches(value.get("mismatches"))
        or not _nonempty_string_list(value.get("remaining_uncertainties"))
        or not isinstance(value.get("rationale"), str)
        or not value["rationale"].strip()
    ):
        raise BenchmarkError("adjudicator failed its semantic contract")
    if len(value["resolved_items"]) != len(trigger):
        raise BenchmarkError("adjudicator omitted one or more trigger resolutions")
    for item, expected_trigger in zip(value["resolved_items"], trigger, strict=True):
        if (
            not isinstance(item, dict)
            or set(item) != {"item", "resolution", "primary_evidence"}
            or item.get("item") != expected_trigger
            or any(
                not isinstance(item.get(field), str) or not item[field].strip()
                for field in item
            )
        ):
            raise BenchmarkError("adjudicator resolution record is malformed")
    implication_pair = _validate_implications(
        value["implications"], allow_unclear=False
    )
    if value["classification"] != _classification_for_implications(*implication_pair):
        raise BenchmarkError("adjudicator classification contradicts its implications")
    if (value["verdict"] == "faithful") != (
        value["classification"] in FAITHFUL_CLASSIFICATIONS
    ):
        raise BenchmarkError("adjudicator verdict contradicts its classification")
    if value["verdict"] == "faithful" and (
        value["mismatches"] or value["remaining_uncertainties"]
    ):
        raise BenchmarkError("adjudicator returned a contradictory faithful judgment")
    if value["remaining_uncertainties"]:
        raise BenchmarkError("adjudicator left an unresolved uncertainty")
    if value["verdict"] == "unfaithful" and not value["mismatches"]:
        raise BenchmarkError("adjudicator returned unfaithful without a concrete mismatch")


class AuditController:
    def __init__(
        self,
        *,
        codex_binary: Path,
        code_mode_host_sha256: str | None = None,
        auth_file: Path,
        model: str,
        reasoning_effort: str,
        timeout_seconds: float,
        maximum_infrastructure_retries: int = 2,
        bwrap_binary: Path | None = None,
        offline_shell: Path | None = None,
        toolchain_root: Path | None = None,
        packages_root: Path | None = None,
        forbidden_feedback_identifiers: Iterable[str] = (),
    ) -> None:
        self.codex_binary = codex_binary
        self.code_mode_host_sha256 = code_mode_host_sha256
        self.auth_file = auth_file
        self.model = model
        self.reasoning_effort = reasoning_effort
        self.timeout_seconds = timeout_seconds
        self.maximum_infrastructure_retries = maximum_infrastructure_retries
        self.bwrap_binary = bwrap_binary
        self.offline_shell = offline_shell
        self.toolchain_root = toolchain_root
        self.packages_root = packages_root
        self.forbidden_feedback_identifiers = frozenset(forbidden_feedback_identifiers)

    def _fresh_role(
        self,
        *,
        role: str,
        prompt: str,
        workspace: Path,
        role_root: Path,
        schema: Path,
        validate: Callable[[dict[str, Any]], None],
    ) -> tuple[dict[str, Any], dict[str, Any]]:
        errors: list[str] = []
        tries: list[dict[str, Any]] = []
        role_root.mkdir(parents=True, exist_ok=True)

        def aggregate(selected_retry: int | None = None) -> dict[str, Any]:
            usage = {
                "input_tokens": 0,
                "cached_input_tokens": 0,
                "cache_write_input_tokens": 0,
                "output_tokens": 0,
                "reasoning_output_tokens": 0,
                "total_tokens": 0,
            }
            for item in tries:
                item_usage = item.get("usage")
                if isinstance(item_usage, dict):
                    for field in usage:
                        value = item_usage.get(field)
                        if isinstance(value, int) and not isinstance(value, bool) and value >= 0:
                            usage[field] += value
            return {
                "schema_version": "formalization-auditor-role-telemetry-1",
                "role": role,
                "selected_retry": selected_retry,
                "retry": selected_retry,
                "tries": tries,
                "wall_seconds": sum(float(item["wall_seconds"]) for item in tries),
                "usage": usage,
                "thread_id": (
                    tries[selected_retry - 1].get("thread_id")
                    if selected_retry is not None
                    else None
                ),
            }

        for retry in range(1, self.maximum_infrastructure_retries + 2):
            attempt_root = role_root / f"try-{retry:02d}"
            artifacts = attempt_root / "artifacts"
            driver = CodexDriver(
                codex_binary=self.codex_binary,
                code_mode_host_sha256=self.code_mode_host_sha256,
                model=self.model,
                reasoning_effort=self.reasoning_effort,
                # Auditor credentials likewise stay outside the archived audit
                # tree in a driver-owned private runtime directory.
                state_root=None,
                auth_file=self.auth_file,
                bwrap_binary=self.bwrap_binary,
                offline_shell=self.offline_shell,
                toolchain_root=self.toolchain_root,
                packages_root=self.packages_root,
                workspace_writable=False,
            )
            result: TurnResult | None = None
            value: dict[str, Any] | None = None
            retry_error: str | None = None
            capability_exception = False
            retry_started = time.perf_counter_ns()
            try:
                result = driver.run_turn(
                    prompt=prompt,
                    workspace=workspace,
                    artifact_dir=artifacts,
                    timeout_seconds=self.timeout_seconds,
                    output_schema=schema,
                    ephemeral=True,
                    sandbox="read-only",
                )
                value = _parse_agent_json(result, artifacts)
                validate(value)
            except ProviderCapabilityError as error:
                retry_error = str(error)
                capability_exception = True
            except BenchmarkError as error:
                retry_error = str(error)
            finally:
                try:
                    driver.close(artifact_dir=attempt_root / "session-close")
                except BenchmarkError as error:
                    close_error = f"app-server shutdown validation failed: {error}"
                    retry_error = (
                        f"{retry_error}; {close_error}" if retry_error else close_error
                    )
            accepted = retry_error is None and value is not None and result is not None
            tries.append(
                {
                    "retry": retry,
                    "status": (
                        "accepted" if accepted else "rejected-infrastructure-or-schema"
                    ),
                    "wall_seconds": (time.perf_counter_ns() - retry_started)
                    / 1_000_000_000,
                    "driver_wall_seconds": result.wall_seconds if result is not None else None,
                    "usage": result.usage if result is not None else None,
                    "usage_complete": bool(result is not None and result.usage_complete),
                    "thread_id": result.thread_id if result is not None else None,
                    "failure_kind": result.failure_kind if result is not None else None,
                    "error": retry_error,
                }
            )
            if accepted:
                telemetry = aggregate(retry)
                write_json_atomic(role_root / "telemetry.json", telemetry, mode=0o400)
                assert value is not None
                return value, telemetry
            errors.append(retry_error or "auditor retry failed without a diagnostic")
            write_json_atomic(role_root / "telemetry.json", aggregate(), mode=0o400)
            if capability_exception or (
                result is not None and result.failure_kind == "provider_capability_violation"
            ):
                raise ProviderCapabilityError(
                    f"fresh {role} encountered a release-blocking provider "
                    "capability incompatibility; no infrastructure retry permitted"
                )
        raise BenchmarkError(f"fresh {role} failed after retries: {' | '.join(errors)}")

    def _scheduled_role(
        self,
        *,
        audit_started_perf_ns: int,
        prerequisites: tuple[str, ...],
        role: str,
        prompt: str,
        workspace: Path,
        role_root: Path,
        schema: Path,
        validate: Callable[[dict[str, Any]], None],
    ) -> tuple[dict[str, Any], dict[str, Any]]:
        """Run one fresh role and durably record its critical-path interval."""

        role_started = time.perf_counter_ns()
        try:
            value, telemetry = self._fresh_role(
                role=role,
                prompt=prompt,
                workspace=workspace,
                role_root=role_root,
                schema=schema,
                validate=validate,
            )
        except BaseException:
            role_completed = time.perf_counter_ns()
            schedule = {
                "schema_version": "formalization-auditor-role-schedule-1",
                "role": role,
                "prerequisites": list(prerequisites),
                "started_offset_seconds": (
                    role_started - audit_started_perf_ns
                )
                / 1_000_000_000,
                "completed_offset_seconds": (
                    role_completed - audit_started_perf_ns
                )
                / 1_000_000_000,
                "wall_seconds": (role_completed - role_started) / 1_000_000_000,
                "completed": False,
            }
            role_root.mkdir(parents=True, exist_ok=True)
            write_json_atomic(role_root / "schedule.json", schedule, mode=0o400)
            telemetry_path = role_root / "telemetry.json"
            if telemetry_path.is_file() and not telemetry_path.is_symlink():
                partial = load_json(telemetry_path)
                if isinstance(partial, dict):
                    partial["schedule"] = schedule
                    write_json_atomic(telemetry_path, partial, mode=0o400)
            raise

        role_completed = time.perf_counter_ns()
        schedule = {
            "schema_version": "formalization-auditor-role-schedule-1",
            "role": role,
            "prerequisites": list(prerequisites),
            "started_offset_seconds": (role_started - audit_started_perf_ns)
            / 1_000_000_000,
            "completed_offset_seconds": (role_completed - audit_started_perf_ns)
            / 1_000_000_000,
            "wall_seconds": (role_completed - role_started) / 1_000_000_000,
            "completed": True,
        }
        role_root.mkdir(parents=True, exist_ok=True)
        write_json_atomic(role_root / "schedule.json", schedule, mode=0o400)
        enriched = dict(telemetry)
        enriched["schedule"] = schedule
        write_json_atomic(role_root / "telemetry.json", enriched, mode=0o400)
        return value, enriched

    def seal_incident(
        self,
        *,
        audit_root: Path,
        task_id: str,
        paper_sha256: str,
        semantic_sha256: str,
        error: str,
        wall_seconds: float,
        classification: str = "audit_system_infrastructure",
    ) -> dict[str, Any]:
        """Bind every completed role retry to a terminal audit-system incident."""

        telemetry: list[dict[str, Any]] = []
        usage = {
            "input_tokens": 0,
            "cached_input_tokens": 0,
            "cache_write_input_tokens": 0,
            "output_tokens": 0,
            "reasoning_output_tokens": 0,
            "total_tokens": 0,
        }
        usage_complete = True
        for path in sorted(audit_root.glob("roles/*/telemetry.json")):
            if not path.is_file() or path.is_symlink():
                raise BenchmarkError(f"unsafe partial audit telemetry: {path}")
            role = load_json(path)
            role_record = {
                "path": str(path),
                "sha256": sha256_file(path),
                "telemetry": role,
            }
            telemetry.append(role_record)
            role_usage = role.get("usage")
            if isinstance(role_usage, dict):
                for field in usage:
                    value = role_usage.get(field)
                    if isinstance(value, int) and not isinstance(value, bool) and value >= 0:
                        usage[field] += value
                    else:
                        usage_complete = False
            else:
                usage_complete = False
            tries = role.get("tries")
            if not isinstance(tries, list) or not tries:
                usage_complete = False
            else:
                for item in tries:
                    if not isinstance(item, dict) or not item.get("usage_complete", False):
                        usage_complete = False
        # A failure before the first durable role result has no complete usage
        # evidence; represent that explicitly rather than implying zero use.
        if not telemetry:
            usage_complete = False
        incident = {
            "schema_version": "formalization-audit-incident-1",
            "task_id": task_id,
            "paper_sha256": paper_sha256,
            "candidate_semantic_sha256": semantic_sha256,
            "status": "AUDIT_SYSTEM_INCIDENT",
            "classification": classification,
            "completed_at_utc": utc_now(),
            "error": error,
            "audit_wall_seconds": wall_seconds,
            "auditor_telemetry": telemetry,
            "usage": usage,
            "usage_complete": usage_complete,
            "auditor_tokens_excluded_from_benchmark": True,
            "execution_plan": AUDIT_EXECUTION_PLAN,
            "evidence_manifest": audit_evidence_manifest(audit_root),
        }
        path = audit_root / "incident.json"
        if path.exists() or path.is_symlink():
            if not path.is_file() or path.is_symlink():
                raise BenchmarkError("unsafe audit incident record")
            existing = load_json(path)
            if existing != incident:
                raise BenchmarkError("audit incident record changed")
            return existing
        write_json_atomic(path, incident, mode=0o400)
        return incident

    def run(
        self,
        *,
        task_id: str,
        paper_path: Path,
        paper_sha256: str,
        source_packet: Path,
        dossier_path: Path,
        semantic_sha256: str,
        audit_root: Path,
    ) -> dict[str, Any]:
        if audit_root.exists():
            decision_path = audit_root / "decision.json"
            if decision_path.is_file():
                decision = load_json(decision_path)
                if (
                    decision.get("candidate_semantic_sha256") == semantic_sha256
                    and decision.get("evidence_manifest")
                    == audit_evidence_manifest(audit_root)
                ):
                    reused = dict(decision)
                    reused["audit_reused"] = True
                    reused["incremental_audit_wall_seconds"] = 0.0
                    reused["incremental_auditor_telemetry"] = []
                    reused["reused_decision_sha256"] = sha256_file(decision_path)
                    return reused
            raise BenchmarkError(f"nonempty or incomplete audit root exists: {audit_root}")
        audit_root.mkdir(parents=True, mode=0o700)
        started = time.perf_counter_ns()
        telemetry: list[dict[str, Any]] = []

        blind_workspace = audit_root / "workspaces" / "blind"
        blind_workspace.mkdir(parents=True)
        dossier_text = dossier_path.read_text(encoding="utf-8")
        dossier = load_json(dossier_path)
        dependencies = _dependency_identity(dossier)
        blind_prompt = (
            (PROMPTS / "blind_translation.md").read_text(encoding="utf-8")
            + "\n\nSemantic SHA-256: `"
            + semantic_sha256
            + "`\n\n"
            + dossier_text
        )
        direct_workspace = audit_root / "workspaces" / "direct"
        direct_workspace.mkdir(parents=True)
        _copy_private(paper_path, direct_workspace / "paper.pdf")
        _copy_private(source_packet, direct_workspace / "source_packet.md")
        _copy_private(dossier_path, direct_workspace / "semantic_dossier.md")
        direct_prompt = (
            (PROMPTS / "direct_judge.md").read_text(encoding="utf-8")
            + f"\n\nTask: {task_id}\nPaper SHA-256: {paper_sha256}\n"
            + f"Candidate semantic SHA-256: {semantic_sha256}\n"
            + "Authoritative files: `paper.pdf`, `source_packet.md`, and "
            + "`semantic_dossier.md`.\n"
        )
        translation_path = audit_root / "blind_translation.json"
        direct_path = audit_root / "direct_judgment.json"
        roundtrip_path = audit_root / "roundtrip_judgment.json"
        direct_result: tuple[dict[str, Any], dict[str, Any]] | None = None
        # Only the two evidence-independent branches overlap.  The executor
        # context drains every started role before an exception can escape, so
        # incident sealing never races a background writer.
        with ThreadPoolExecutor(
            max_workers=2, thread_name_prefix="faithfulness-audit"
        ) as executor:
            blind_future: Future[tuple[dict[str, Any], dict[str, Any]]] = (
                executor.submit(
                    self._scheduled_role,
                    audit_started_perf_ns=started,
                    prerequisites=(),
                    role="blind-translation",
                    prompt=blind_prompt,
                    workspace=blind_workspace,
                    role_root=audit_root / "roles" / "blind-translation",
                    schema=SCHEMAS / "blind_translation.schema.json",
                    validate=lambda value: _validate_translation(
                        value, semantic_sha256, dependencies
                    ),
                )
            )
            direct_future: Future[tuple[dict[str, Any], dict[str, Any]]] = (
                executor.submit(
                    self._scheduled_role,
                    audit_started_perf_ns=started,
                    prerequisites=(),
                    role="direct-judge",
                    prompt=direct_prompt,
                    workspace=direct_workspace,
                    role_root=audit_root / "roles" / "direct-judge",
                    schema=SCHEMAS / "direct_judgment.schema.json",
                    validate=lambda value: _validate_judgment(
                        value,
                        role="direct-judge",
                        paper_sha256=paper_sha256,
                        semantic_sha256=semantic_sha256,
                        dependencies=dependencies,
                    ),
                )
            )

            translation, blind_telemetry = blind_future.result()
            write_json_atomic(translation_path, translation, mode=0o400)
            # Avoid spending a round-trip call after a direct branch that has
            # already failed, while still allowing the normal critical paths
            # to overlap.
            if direct_future.done():
                direct_result = direct_future.result()
                write_json_atomic(direct_path, direct_result[0], mode=0o400)

            roundtrip_workspace = audit_root / "workspaces" / "roundtrip"
            roundtrip_workspace.mkdir(parents=True)
            _copy_private(paper_path, roundtrip_workspace / "paper.pdf")
            _copy_private(source_packet, roundtrip_workspace / "source_packet.md")
            _copy_private(
                translation_path,
                roundtrip_workspace / "blind_translation.json",
            )
            roundtrip_prompt = (
                (PROMPTS / "roundtrip_judge.md").read_text(encoding="utf-8")
                + f"\n\nTask: {task_id}\nPaper SHA-256: {paper_sha256}\n"
                + f"Candidate semantic SHA-256: {semantic_sha256}\n"
                + "Authoritative files: `paper.pdf`, `source_packet.md`, and "
                + "`blind_translation.json`.\n"
            )
            roundtrip_future: Future[tuple[dict[str, Any], dict[str, Any]]] = (
                executor.submit(
                    self._scheduled_role,
                    audit_started_perf_ns=started,
                    prerequisites=("blind-translation",),
                    role="roundtrip-judge",
                    prompt=roundtrip_prompt,
                    workspace=roundtrip_workspace,
                    role_root=audit_root / "roles" / "roundtrip-judge",
                    schema=SCHEMAS / "roundtrip_judgment.schema.json",
                    validate=lambda value: _validate_judgment(
                        value,
                        role="roundtrip-judge",
                        paper_sha256=paper_sha256,
                        semantic_sha256=semantic_sha256,
                        dependencies=dependencies,
                    ),
                )
            )
            if direct_result is None:
                direct_result = direct_future.result()
                write_json_atomic(direct_path, direct_result[0], mode=0o400)
            roundtrip, roundtrip_telemetry = roundtrip_future.result()
            write_json_atomic(roundtrip_path, roundtrip, mode=0o400)

        direct, direct_telemetry = direct_result
        # Preserve a deterministic logical order independent of completion.
        telemetry.extend(
            [blind_telemetry, direct_telemetry, roundtrip_telemetry]
        )

        adjudicated = False
        adjudication: dict[str, Any] | None = None
        trigger: list[str] = []
        if direct["classification"] != roundtrip["classification"]:
            trigger.append("direct and round-trip classifications differ")
        if direct["requires_adjudication"]:
            trigger.append("direct judge requested adjudication")
        if roundtrip["requires_adjudication"]:
            trigger.append("round-trip judge requested adjudication")
        if any(
            item["status"] == "unclear"
            for item in translation["dependency_coverage"]
        ):
            trigger.append("blind dependency interpretation remains unclear")
        if any(
            item["status"] == "unclear"
            for item in direct["dependency_coverage"]
        ):
            trigger.append("direct dependency interpretation remains unclear")
        if any(
            item["status"] == "unclear"
            for item in direct["semantic_checklist"]
        ):
            trigger.append("direct semantic check remains unclear")
        if any(
            item["status"] == "unclear"
            for item in roundtrip["semantic_checklist"]
        ):
            trigger.append("round-trip semantic check remains unclear")

        if trigger:
            adjudicated = True
            adjudicator_workspace = audit_root / "workspaces" / "adjudicator"
            adjudicator_workspace.mkdir(parents=True)
            for source, name in (
                (paper_path, "paper.pdf"),
                (source_packet, "source_packet.md"),
                (dossier_path, "semantic_dossier.md"),
                (translation_path, "blind_translation.json"),
                (audit_root / "direct_judgment.json", "direct_judgment.json"),
                (audit_root / "roundtrip_judgment.json", "roundtrip_judgment.json"),
            ):
                _copy_private(source, adjudicator_workspace / name)
            adjudicator_prompt = (
                (PROMPTS / "adjudicator.md").read_text(encoding="utf-8")
                + f"\n\nTask: {task_id}\nPaper SHA-256: {paper_sha256}\n"
                + f"Candidate semantic SHA-256: {semantic_sha256}\n"
                + "All authoritative inputs are the files in this workspace.\n"
                + "Triggers requiring resolution: "
                + json.dumps(trigger, ensure_ascii=False)
                + "\n"
            )
            adjudication, role_telemetry = self._scheduled_role(
                audit_started_perf_ns=started,
                prerequisites=(
                    "blind-translation",
                    "direct-judge",
                    "roundtrip-judge",
                ),
                role="adjudicator",
                prompt=adjudicator_prompt,
                workspace=adjudicator_workspace,
                role_root=audit_root / "roles" / "adjudicator",
                schema=SCHEMAS / "adjudication.schema.json",
                validate=lambda value: _validate_adjudication(
                    value,
                    paper_sha256=paper_sha256,
                    semantic_sha256=semantic_sha256,
                    trigger=trigger,
                ),
            )
            telemetry.append(role_telemetry)
            write_json_atomic(audit_root / "adjudication.json", adjudication, mode=0o400)
            verdict = adjudication["verdict"]
            classification = adjudication["classification"]
            implications = adjudication["implications"]
            mismatches = list(adjudication["mismatches"])
            uncertainties = list(adjudication["remaining_uncertainties"])
            rationale = adjudication["rationale"]
        else:
            classification = direct["classification"]
            implications = direct["implications"]
            verdict = (
                "faithful"
                if classification in FAITHFUL_CLASSIFICATIONS
                else "unfaithful"
            )
            mismatches = []
            seen_mismatches: set[tuple[str, str, str]] = set()
            for mismatch in [*direct["mismatches"], *roundtrip["mismatches"]]:
                identity = (
                    mismatch["paper_requirement"],
                    mismatch["candidate_mismatch"],
                    mismatch["severity"],
                )
                if identity not in seen_mismatches:
                    seen_mismatches.add(identity)
                    mismatches.append(mismatch)
            uncertainties = [*direct["uncertainties"], *roundtrip["uncertainties"]]
            rationale = (
                "Independent direct and round-trip judges agreed on "
                f"{classification}; no adjudication trigger remained."
            )

        if verdict == "unfaithful" and not mismatches:
            raise BenchmarkError("unfaithful audit decision has no concrete mismatch")
        # A valid semantic decision is binary. Operational audit failures are
        # sealed separately as incidents, never as a third faithfulness verdict.
        audit_incident = False
        feedback = (
            make_repair_feedback(
                mismatches,
                forbidden_identifiers=self.forbidden_feedback_identifiers,
            )
            if verdict == "unfaithful"
            else None
        )
        if feedback is not None:
            write_json_atomic(audit_root / "repair_feedback.json", feedback, mode=0o400)
        stopped = time.perf_counter_ns()
        decision = {
            "schema_version": "source-first-formalization-1",
            "task_id": task_id,
            "paper_sha256": paper_sha256,
            "candidate_semantic_sha256": semantic_sha256,
            "completed_at_utc": utc_now(),
            "verdict": verdict,
            "accepted": verdict == "faithful",
            "audit_incident": audit_incident,
            "adjudicated": adjudicated,
            "classification": classification,
            "implications": implications,
            "direct_classification": direct["classification"],
            "roundtrip_classification": roundtrip["classification"],
            "direct_verdict": "faithful" if direct["accepted"] else "unfaithful",
            "roundtrip_verdict": "faithful" if roundtrip["accepted"] else "unfaithful",
            "mismatches": mismatches,
            "remaining_uncertainties": uncertainties,
            "rationale": rationale,
            "repair_feedback": feedback,
            "audit_wall_seconds": (stopped - started) / 1_000_000_000,
            "auditor_telemetry": telemetry,
            "audit_reused": False,
            "incremental_audit_wall_seconds": (stopped - started) / 1_000_000_000,
            "incremental_auditor_telemetry": telemetry,
            "auditor_tokens_excluded_from_benchmark": True,
            "condition_blind": True,
            "attempt_blind": True,
            "execution_plan": AUDIT_EXECUTION_PLAN,
            "evidence_manifest": audit_evidence_manifest(audit_root),
        }
        write_json_atomic(audit_root / "decision.json", decision, mode=0o400)
        return decision
