#!/usr/bin/env python3
"""Run one matched Design-16 proof or Design-17 statement pair.

R0 indexes Mathlib only and exposes only Mathlib OLean files. R1 runs the same
deterministic retriever over Mathlib plus the frozen NumStability atlas and
additionally exposes the frozen NumStability OLean tree. Each condition starts
a fresh, stateless formalizer. Conditions run sequentially so timed contestants
never contend on the same host.

Proof-inclusive mode freezes compiled candidates for later independent audit.
Statement-only mode runs the canonical binary audit inline and permits up to
three same-conversation repairs. Consumed tasks remain explicitly unscored
engineering evidence until a separate untouched campaign is predeclared.
"""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
from typing import Any, Mapping

from audit_controller import AuditController
from codex_driver import CodexDriver
from common import (
    BenchmarkError,
    assert_no_credentials_in_tree,
    freeze_candidate,
    load_json,
    make_repair_feedback,
    sha256_file,
    utc_now,
    verify_tree_manifest,
    write_bytes_atomic,
    write_json_atomic,
)
from composition_packets import build_composition_packet
from deployment import Deployment, load_deployment
from design16_smoke import _net_new, _routed_candidate_template
from formalization_validator import (
    _mask_noncode,
    compiled_candidate_workspace,
    run_bounded_command,
    validate_candidate,
)
from lean_sandbox import (
    compiler_command,
    extractor_command,
    signature_interface_command,
    signature_render_command,
)
from manifest_control import ROOT
from pair_controller import (
    _environment_note,
    _net_new_usage,
    _task_packet_markdown,
    _usage_add,
)
from prepare_candidate_audit import CandidateAuditError, prepare_candidate_audit
from statement_codex_driver import StatementCodexDriver
from hardware import snapshot_hardware


SCIENTIFIC_STATUS = "UNSCORED_ENGINEERING_EXPLORATORY"
SIGNATURE_INTERFACE_HELPER = Path(__file__).with_name("signature_interface.lean")
SIGNATURE_INTERFACE_SCHEMA = "formalization-design17-signature-interface-1"
SIGNATURE_INTERFACE_MAX_OUTPUT_BYTES = 8 * 1024 * 1024
SIGNATURE_RENDER_BEGIN = "HIGHAMBENCH_SIGNATURE_BEGIN"
SIGNATURE_RENDER_END = "HIGHAMBENCH_SIGNATURE_END"
CONDITIONS = ("R0", "R1")
INFRASTRUCTURE_CONDITION_STATUSES = frozenset(
    {
        "FORMALIZER_INCIDENT",
        "VALIDATION_INFRASTRUCTURE_INCIDENT",
        "AUDIT_PREPARATION_INCIDENT",
        "AUDIT_SYSTEM_INCIDENT",
    }
)


def _condition_faithfulness_status(result_status: str) -> str:
    if result_status == "ACCEPTED_FAITHFUL":
        return "FAITHFUL"
    if result_status in INFRASTRUCTURE_CONDITION_STATUSES:
        return "NOT_DECIDED_INFRASTRUCTURE"
    return "UNFAITHFUL_OR_FAILED"


def _statement_pair_status(r0_status: str, r1_status: str) -> tuple[str, str]:
    statuses = {r0_status, r1_status}
    if statuses & INFRASTRUCTURE_CONDITION_STATUSES:
        return "PAIR_INCIDENT", "NOT_DECIDED_INFRASTRUCTURE"
    if statuses == {"ACCEPTED_FAITHFUL"}:
        return "AUDITED_FAITHFUL_PAIR", "BOTH_FAITHFUL"
    return "AUDITED_PAIR_INELIGIBLE", "PAIR_NOT_BOTH_FAITHFUL"
ALLOWED_EXPLORATORY_TASKS = frozenset(
    {
        "H5-5",
        "H7-12",
        "H7-14",
        "H10-7",
        "H12-4",
        "H15-3",
        "H19-5",
        "H20-6",
        "H20-8",
        "H20-9",
        "H22-5",
        "H22-11",
        "H23-6",
    }
)


@dataclass(frozen=True)
class ConditionSpec:
    name: str
    corpus_id: str
    atlas_paths: tuple[Path, ...]
    compiler_condition: str
    library_olean: Path | None


def _atlas_declarations(atlas_root: Path, *, label: str) -> Path:
    expanded = atlas_root.expanduser()
    if expanded.is_symlink():
        raise BenchmarkError(f"{label} atlas may not be a symlink: {expanded}")
    root = expanded.resolve()
    declarations = root / "declarations.jsonl"
    metadata_path = root / "atlas.json"
    if (
        not root.is_dir()
        or root.is_symlink()
        or not declarations.is_file()
        or declarations.is_symlink()
        or not metadata_path.is_file()
        or metadata_path.is_symlink()
    ):
        raise BenchmarkError(f"{label} atlas is missing or unsafe: {root}")
    metadata = load_json(metadata_path)
    if (
        metadata.get("schema_version") != "numstability-library-atlas-3"
        or metadata.get("declarations_sha256") != sha256_file(declarations)
        or not isinstance(metadata.get("declaration_count"), int)
        or metadata["declaration_count"] < 1
    ):
        raise BenchmarkError(f"{label} atlas identity is malformed or stale")
    return declarations


def _classify_atlas(path: Path, *, expect_numstability: bool) -> None:
    """Reject accidental treatment leakage or a bogus treatment atlas."""

    records = 0
    numstability_modules = 0
    for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
        try:
            record = json.loads(line)
        except json.JSONDecodeError as error:
            raise BenchmarkError(f"malformed atlas JSON at {path}:{line_number}") from error
        module = record.get("module") if isinstance(record, dict) else None
        if not isinstance(module, str) or not module:
            raise BenchmarkError(f"malformed atlas module at {path}:{line_number}")
        records += 1
        if module == "NumStability" or module.startswith("NumStability."):
            numstability_modules += 1
    if records == 0:
        raise BenchmarkError(f"empty declaration atlas: {path}")
    if expect_numstability and numstability_modules == 0:
        raise BenchmarkError("treatment atlas contains no NumStability modules")
    if not expect_numstability and numstability_modules != 0:
        raise BenchmarkError("Mathlib-only atlas is contaminated by NumStability")


def condition_spec(
    condition: str,
    *,
    deployment: Deployment,
    mathlib_atlas: Path,
) -> ConditionSpec:
    if condition not in CONDITIONS:
        raise BenchmarkError(f"unknown Design-16 matched condition: {condition}")
    mathlib_declarations = _atlas_declarations(mathlib_atlas, label="Mathlib")
    _classify_atlas(mathlib_declarations, expect_numstability=False)
    if condition == "R0":
        return ConditionSpec(
            name="R0",
            corpus_id="mathlib-only",
            atlas_paths=(mathlib_declarations,),
            compiler_condition="N",
            library_olean=None,
        )
    treatment_declarations = _atlas_declarations(
        deployment.library_atlas, label="NumStability"
    )
    _classify_atlas(treatment_declarations, expect_numstability=True)
    if treatment_declarations == mathlib_declarations:
        raise BenchmarkError("control and treatment atlases resolve to the same file")
    return ConditionSpec(
        name="R1",
        corpus_id="mathlib-plus-numstability",
        atlas_paths=(mathlib_declarations, treatment_declarations),
        compiler_condition="L",
        library_olean=deployment.library_olean,
    )


def _condition_order(raw: str) -> tuple[str, str]:
    order = tuple(value.strip().upper() for value in raw.split(","))
    if len(order) != 2 or set(order) != set(CONDITIONS):
        raise BenchmarkError("condition order must be exactly R0,R1 or R1,R0")
    return order  # type: ignore[return-value]


def _contract_additions(task_id: str) -> tuple[list[str], str | None]:
    contract_path = ROOT / "design16" / "contracts" / f"{task_id}.json"
    if not contract_path.exists():
        return [], None
    if not contract_path.is_file() or contract_path.is_symlink():
        raise BenchmarkError("Design-16 faithfulness-contract overlay is unsafe")
    contract = load_json(contract_path)
    values = contract.get("faithfulness_contract")
    if (
        contract.get("task_id") != task_id
        or not isinstance(values, list)
        or not all(isinstance(value, str) and value for value in values)
    ):
        raise BenchmarkError("Design-16 faithfulness-contract overlay is malformed")
    return list(values), sha256_file(contract_path)


def _prompt_bytes(*, statement_only: bool) -> bytes:
    base_name = "statement_formalizer.md" if statement_only else "formalizer.md"
    addendum_name = (
        "design17_statement_addendum.md"
        if statement_only
        else "design16_matched_addendum.md"
    )
    base = (ROOT / "prompts" / base_name).read_text(encoding="utf-8").rstrip()
    addendum = (ROOT / "prompts" / addendum_name).read_text(
        encoding="utf-8"
    )
    return (base + "\n" + addendum).encode("utf-8")


def _candidate_template(composition: dict[str, Any], *, statement_only: bool) -> str:
    template = _routed_candidate_template(composition)
    if not statement_only:
        return template
    old = "theorem target : True := by\n  trivial"
    new = "theorem target : True := by\n  sorry"
    if template.count(old) != 1:
        raise BenchmarkError("statement-only template replacement contract changed")
    return template.replace(
        "/- Replace this placeholder with the faithful paper result and complete proof. -/",
        "/- Replace True with the faithful paper statement; keep the sole target sorry. -/",
    ).replace(old, new)


def _write_pair_report(output_root: Path, report: dict[str, Any]) -> None:
    write_json_atomic(output_root / "pair-report.json", report, mode=0o400)


def _ratio(numerator: int | float, denominator: int | float) -> float | None:
    return float(numerator) / float(denominator) if denominator else None


def _submission_clock(
    *,
    active_started_perf_ns: int,
    active_ended_perf_ns: int,
    freeze_started_perf_ns: int,
    freeze_completed_perf_ns: int,
) -> dict[str, float]:
    """Measure one attempt continuously through the immutable submission freeze."""

    boundaries = (
        active_started_perf_ns,
        active_ended_perf_ns,
        freeze_started_perf_ns,
        freeze_completed_perf_ns,
    )
    if any(not isinstance(value, int) or isinstance(value, bool) for value in boundaries):
        raise BenchmarkError("formalizer/freeze time boundaries are malformed")
    if boundaries != tuple(sorted(boundaries)):
        raise BenchmarkError("formalizer/freeze time boundaries are inconsistent")
    scale = 1_000_000_000
    return {
        "model_active_seconds": (
            active_ended_perf_ns - active_started_perf_ns
        )
        / scale,
        "post_turn_through_freeze_seconds": (
            freeze_completed_perf_ns - active_ended_perf_ns
        )
        / scale,
        "candidate_freeze_seconds": (
            freeze_completed_perf_ns - freeze_started_perf_ns
        )
        / scale,
        "contestant_active_seconds": (
            freeze_completed_perf_ns - active_started_perf_ns
        )
        / scale,
    }


def _packet_exposed_records(composition: Mapping[str, Any]) -> list[dict[str, str]]:
    records: dict[str, str] = {}
    for card in composition.get("retrieved_roots", []):
        if not isinstance(card, Mapping):
            raise BenchmarkError("composition packet card is malformed")
        for record in [card.get("declaration"), *card.get("dependencies", [])]:
            if not isinstance(record, Mapping):
                raise BenchmarkError("composition packet declaration is malformed")
            name = record.get("name")
            module = record.get("module")
            if not isinstance(name, str) or not name or not isinstance(module, str) or not module:
                raise BenchmarkError("composition packet declaration identity is malformed")
            prior = records.get(name)
            if prior is not None and prior != module:
                raise BenchmarkError(f"inconsistent packet declaration owner: {name}")
            records[name] = module
    return [{"name": name, "module": records[name]} for name in sorted(records)]


def _unescape_signature_field(value: str) -> str:
    output: list[str] = []
    index = 0
    while index < len(value):
        if value[index] != "\\" or index + 1 >= len(value):
            output.append(value[index])
            index += 1
            continue
        marker = value[index + 1]
        output.append({"n": "\n", "r": "\r", "t": "\t", "\\": "\\"}.get(marker, marker))
        index += 2
    return "".join(output)


def _parse_signature_interface_report(
    output: str, exposed_records: list[dict[str, str]]
) -> dict[str, Any]:
    expected_seeds = {record["name"]: record["module"] for record in exposed_records}
    format_version: str | None = None
    observed_seeds: dict[str, dict[str, str]] = {}
    edges: set[tuple[str, str, str, str]] = set()
    summary: tuple[int, int] | None = None
    for line_number, raw_line in enumerate(output.splitlines(), 1):
        if not raw_line:
            continue
        fields = [_unescape_signature_field(value) for value in raw_line.split("\t")]
        tag = fields[0]
        if tag == "format" and len(fields) == 2:
            if format_version is not None:
                raise BenchmarkError("duplicate signature-interface format row")
            format_version = fields[1]
        elif tag == "seed" and len(fields) == 4:
            name, module, kind = fields[1:]
            if name in observed_seeds or not kind:
                raise BenchmarkError("malformed signature-interface seed row")
            observed_seeds[name] = {
                "name": name,
                "module": module,
                "kind": kind,
            }
        elif tag == "direct" and len(fields) == 5:
            seed, name, module, kind = fields[1:]
            if seed not in expected_seeds or not name.startswith("NumStability."):
                raise BenchmarkError("malformed signature-interface direct row")
            if not (
                module == "NumStability" or module.startswith("NumStability.")
            ) or not kind:
                raise BenchmarkError("malformed signature-interface owner row")
            edges.add((seed, name, module, kind))
        elif tag == "summary" and len(fields) == 3:
            if summary is not None or not fields[1].isdigit() or not fields[2].isdigit():
                raise BenchmarkError("malformed signature-interface summary")
            summary = (int(fields[1]), int(fields[2]))
        else:
            raise BenchmarkError(
                f"unknown signature-interface report row at line {line_number}"
            )
    if format_version != "2" or summary is None:
        raise BenchmarkError("incomplete signature-interface report")
    if {
        name: record["module"] for name, record in observed_seeds.items()
    } != expected_seeds:
        raise BenchmarkError("signature-interface seed echo does not match the packet")
    if summary != (len(expected_seeds), len(edges)):
        raise BenchmarkError("signature-interface summary counts do not match")

    direct_by_name: dict[str, dict[str, Any]] = {}
    reference_edges: list[dict[str, str]] = []
    for seed, name, module, kind in sorted(edges):
        prior = direct_by_name.get(name)
        if prior is not None and (prior["module"], prior["kind"]) != (module, kind):
            raise BenchmarkError(f"inconsistent signature dependency identity: {name}")
        if prior is None:
            prior = {"name": name, "module": module, "kind": kind, "referenced_by": []}
            direct_by_name[name] = prior
        prior["referenced_by"].append(seed)
        reference_edges.append({"from": seed, "to": name})

    seed_rows = [observed_seeds[name] for name in sorted(observed_seeds)]
    direct_rows = [direct_by_name[name] for name in sorted(direct_by_name)]
    return {
        "schema_version": SIGNATURE_INTERFACE_SCHEMA,
        "closure_rule": (
            "packet records plus one-hop NumStability constants in each record's "
            "elaborated ConstantInfo.type; declaration bodies are never inspected"
        ),
        "seed_declarations": seed_rows,
        "direct_type_declarations": direct_rows,
        "reference_edges": reference_edges,
        "allowed_declarations": sorted(
            set(expected_seeds) | set(direct_by_name)
        ),
    }


def _signature_render_source(exposed_records: list[dict[str, str]]) -> bytes:
    modules = sorted({record["module"] for record in exposed_records})
    names = sorted(record["name"] for record in exposed_records)
    for value in [*modules, *names]:
        if re.fullmatch(r"[A-Za-z0-9_'.]+", value) is None:
            raise BenchmarkError("signature render identity is not a Lean name")
    lines = [*[f"import {module}" for module in modules], ""]
    for name in names:
        lines.extend(
            [
                f'#eval IO.println "{SIGNATURE_RENDER_BEGIN}\\t{name}"',
                f"#check {name}",
                f'#eval IO.println "{SIGNATURE_RENDER_END}\\t{name}"',
                "",
            ]
        )
    return ("\n".join(lines).rstrip() + "\n").encode("utf-8")


def _parse_signature_render_report(
    output: str, exposed_records: list[dict[str, str]]
) -> dict[str, str]:
    expected = {record["name"] for record in exposed_records}
    rendered: dict[str, str] = {}
    active_name: str | None = None
    active_lines: list[str] = []
    for line in output.splitlines():
        if line.startswith(SIGNATURE_RENDER_BEGIN + "\t"):
            if active_name is not None:
                raise BenchmarkError("nested signature render marker")
            active_name = line.split("\t", 1)[1]
            if active_name not in expected or active_name in rendered:
                raise BenchmarkError("unexpected signature render begin marker")
            active_lines = []
        elif line.startswith(SIGNATURE_RENDER_END + "\t"):
            name = line.split("\t", 1)[1]
            if active_name != name:
                raise BenchmarkError("mismatched signature render end marker")
            value = "\n".join(active_lines).strip()
            if not value:
                raise BenchmarkError("empty #check signature rendering")
            rendered[name] = value
            active_name = None
            active_lines = []
        elif active_name is not None:
            active_lines.append(line)
        elif line.strip():
            raise BenchmarkError("unframed output from signature render command")
    if active_name is not None or set(rendered) != expected:
        raise BenchmarkError("signature render report is incomplete")
    return rendered


def _render_signature_interface(
    *,
    deployment: Deployment,
    exposed_records: list[dict[str, str]],
    artifact_root: Path,
    timeout_seconds: float,
) -> tuple[dict[str, str], dict[str, Any]]:
    source_path = artifact_root / "signature-render.lean"
    write_bytes_atomic(
        source_path, _signature_render_source(exposed_records), mode=0o400
    )
    output_path = artifact_root / "signature-render-output.txt"
    if not exposed_records:
        write_bytes_atomic(output_path, b"", mode=0o400)
        return {}, {
            "source_sha256": sha256_file(source_path),
            "output_sha256": sha256_file(output_path),
            "execution": None,
        }
    command = tuple(
        value.format(workspace=str(artifact_root.resolve()))
        for value in signature_render_command(deployment)
    )
    execution = run_bounded_command(
        command,
        cwd=artifact_root,
        environment=os.environ,
        timeout_seconds=timeout_seconds,
        maximum_output_bytes=SIGNATURE_INTERFACE_MAX_OUTPUT_BYTES,
    )
    output = str(execution.get("output", ""))
    write_bytes_atomic(output_path, output.encode("utf-8"), mode=0o400)
    execution_record = {
        key: execution[key]
        for key in (
            "returncode",
            "output_sha256",
            "output_bytes_observed",
            "output_limit_bytes",
            "output_limit_exceeded",
            "timed_out",
            "resource_limit_event_delta",
            "resource_limit_exceeded",
            "resource_cgroup_join_failed",
        )
    }
    write_json_atomic(
        artifact_root / "signature-render-execution.json",
        execution_record,
        mode=0o400,
    )
    if (
        execution.get("returncode") != 0
        or execution.get("timed_out") is True
        or execution.get("output_limit_exceeded") is True
        or execution.get("resource_limit_exceeded") is True
        or execution.get("resource_cgroup_join_failed") is True
    ):
        raise BenchmarkError("trusted signature #check rendering failed")
    if sha256_file(output_path) != execution["output_sha256"]:
        raise BenchmarkError("signature render output encoding changed its identity")
    return _parse_signature_render_report(output, exposed_records), {
        "source_sha256": sha256_file(source_path),
        "output_sha256": execution["output_sha256"],
        "execution": execution_record,
    }


def _derive_signature_interface(
    *,
    deployment: Deployment,
    composition: Mapping[str, Any],
    output_root: Path,
    timeout_seconds: float,
) -> dict[str, Any]:
    exposed_records = _packet_exposed_records(composition)
    artifact_root = output_root / "signature-interface"
    artifact_root.mkdir(mode=0o700)
    seed_path = artifact_root / "signature-interface-seeds.tsv"
    seed_payload = "".join(
        f"{record['module']}\t{record['name']}\n" for record in exposed_records
    ).encode("utf-8")
    write_bytes_atomic(seed_path, seed_payload, mode=0o400)
    readable_signatures, signature_render = _render_signature_interface(
        deployment=deployment,
        exposed_records=exposed_records,
        artifact_root=artifact_root,
        timeout_seconds=timeout_seconds,
    )
    if not exposed_records:
        write_bytes_atomic(
            artifact_root / "extractor-output.tsv", b"", mode=0o400
        )
        interface = {
            "schema_version": SIGNATURE_INTERFACE_SCHEMA,
            "closure_rule": (
                "packet records plus one-hop NumStability constants in each record's "
                "elaborated ConstantInfo.type; declaration bodies are never inspected"
            ),
            "seed_declarations": [],
            "direct_type_declarations": [],
            "reference_edges": [],
            "allowed_declarations": [],
            "helper_sha256": sha256_file(SIGNATURE_INTERFACE_HELPER),
            "seed_input_sha256": sha256_file(seed_path),
            "extractor_output_sha256": __import__("hashlib").sha256(b"").hexdigest(),
            "extractor_execution": None,
            "signature_render": signature_render,
        }
        write_json_atomic(artifact_root / "interface.json", interface, mode=0o400)
        return interface

    command = tuple(
        value.format(workspace=str(artifact_root.resolve()))
        for value in signature_interface_command(
            deployment, SIGNATURE_INTERFACE_HELPER
        )
    )
    execution = run_bounded_command(
        command,
        cwd=artifact_root,
        environment=os.environ,
        timeout_seconds=timeout_seconds,
        maximum_output_bytes=SIGNATURE_INTERFACE_MAX_OUTPUT_BYTES,
    )
    output = str(execution.get("output", ""))
    output_path = artifact_root / "extractor-output.tsv"
    write_bytes_atomic(output_path, output.encode("utf-8"), mode=0o400)
    execution_record = {
        key: execution[key]
        for key in (
            "returncode",
            "output_sha256",
            "output_bytes_observed",
            "output_limit_bytes",
            "output_limit_exceeded",
            "timed_out",
            "resource_limit_event_delta",
            "resource_limit_exceeded",
            "resource_cgroup_join_failed",
        )
    }
    write_json_atomic(
        artifact_root / "extractor-execution.json", execution_record, mode=0o400
    )
    if (
        execution.get("returncode") != 0
        or execution.get("timed_out") is True
        or execution.get("output_limit_exceeded") is True
        or execution.get("resource_limit_exceeded") is True
        or execution.get("resource_cgroup_join_failed") is True
    ):
        raise BenchmarkError("trusted signature-interface extraction failed")
    if sha256_file(output_path) != execution["output_sha256"]:
        raise BenchmarkError("signature-interface output encoding changed its identity")
    interface = _parse_signature_interface_report(output, exposed_records)
    for record in interface["seed_declarations"]:
        record["readable_signature"] = readable_signatures[record["name"]]
    interface.update(
        {
            "helper_sha256": sha256_file(SIGNATURE_INTERFACE_HELPER),
            "seed_input_sha256": sha256_file(seed_path),
            "extractor_output_sha256": execution["output_sha256"],
            "extractor_execution": execution_record,
            "signature_render": signature_render,
        }
    )
    write_json_atomic(artifact_root / "interface.json", interface, mode=0o400)
    return interface


def _packet_treatment_surfaces(
    composition: Mapping[str, Any],
) -> tuple[set[str], set[str], set[str]]:
    """Return allowed declarations, explicit imports, and type-owner modules."""

    exposed_records = _packet_exposed_records(composition)
    names = {
        record["name"]
        for record in exposed_records
        if record["name"].startswith("NumStability.")
    }
    exposed_modules = {
        record["module"]
        for record in exposed_records
        if record["module"] == "NumStability"
        or record["module"].startswith("NumStability.")
    }
    signature_modules: set[str] = set()
    signature_interface = composition.get("signature_interface")
    if signature_interface is not None:
        if not isinstance(signature_interface, Mapping):
            raise BenchmarkError("packet signature interface is malformed")
        if signature_interface.get("schema_version") != SIGNATURE_INTERFACE_SCHEMA:
            raise BenchmarkError("packet signature interface schema is unsupported")
        seed_rows = signature_interface.get("seed_declarations")
        declarations = signature_interface.get("direct_type_declarations")
        allowed = signature_interface.get("allowed_declarations")
        if (
            not isinstance(seed_rows, list)
            or not isinstance(declarations, list)
            or not isinstance(allowed, list)
        ):
            raise BenchmarkError("packet signature interface lacks declarations")
        observed_seed_identity: list[dict[str, str]] = []
        for record in seed_rows:
            if not isinstance(record, Mapping):
                raise BenchmarkError("packet signature seed record is malformed")
            name = record.get("name")
            module = record.get("module")
            if not isinstance(name, str) or not isinstance(module, str):
                raise BenchmarkError("packet signature seed identity is malformed")
            observed_seed_identity.append({"name": name, "module": module})
        if observed_seed_identity != exposed_records:
            raise BenchmarkError("packet signature seeds do not match exposed records")
        for record in declarations:
            if not isinstance(record, Mapping):
                raise BenchmarkError("packet signature interface record is malformed")
            name = record.get("name")
            module = record.get("module")
            if not isinstance(name, str) or not name.startswith("NumStability."):
                raise BenchmarkError("packet signature declaration name is malformed")
            if not isinstance(module, str) or not (
                module == "NumStability" or module.startswith("NumStability.")
            ):
                raise BenchmarkError("packet signature declaration owner is malformed")
            names.add(name)
            signature_modules.add(module)
        expected_interface_names = {
            record["name"] for record in exposed_records
        } | {
            str(record["name"])
            for record in declarations
            if isinstance(record, Mapping)
        }
        if allowed != sorted(expected_interface_names):
            raise BenchmarkError("packet signature allowlist does not match its records")
    return names, exposed_modules, signature_modules


def _packet_treatment_allowlist(
    composition: Mapping[str, Any],
) -> tuple[set[str], set[str]]:
    names, exposed_modules, _signature_modules = _packet_treatment_surfaces(composition)
    # Signature-prerequisite modules must already be in the trusted import
    # closure of the visible card modules. They are never new import roots.
    return names, exposed_modules


def _numstability_source_path(source_root: Path, module: str) -> Path:
    if module == "NumStability":
        return source_root.parent / "NumStability.lean"
    prefix = "NumStability."
    if not module.startswith(prefix):
        raise BenchmarkError(f"not a NumStability module: {module}")
    return source_root / Path(*module[len(prefix) :].split(".")).with_suffix(".lean")


def _numstability_olean_path(olean_root: Path, module: str) -> Path:
    return olean_root / Path(*module.split(".")).with_suffix(".olean")


def _source_imports(path: Path) -> list[str]:
    if path.is_symlink() or not path.is_file():
        raise BenchmarkError(f"NumStability module source is missing or unsafe: {path}")
    imports: list[str] = []
    for line in path.read_text(encoding="utf-8").splitlines():
        match = re.match(r"^\s*(?:public\s+)?import\s+(.+?)\s*(?:--.*)?$", line)
        if match is None:
            continue
        for value in match.group(1).split():
            if value == "NumStability" or value.startswith("NumStability."):
                if re.fullmatch(r"[A-Za-z0-9_'.]+", value) is None:
                    raise BenchmarkError(f"malformed NumStability import in {path}")
                imports.append(value)
    return imports


def _build_packet_olean_runtime(
    *,
    composition: Mapping[str, Any],
    source_root: Path,
    olean_root: Path,
    destination: Path,
) -> dict[str, Any]:
    """Materialize only the packet modules and their trusted import closure."""

    _names, exposed_modules, signature_modules = _packet_treatment_surfaces(
        composition
    )
    selected_modules = exposed_modules
    if destination.exists() or destination.is_symlink():
        raise BenchmarkError("packet OLean runtime destination already exists")
    destination.mkdir(parents=True, mode=0o700)
    pending = sorted(selected_modules)
    closure: set[str] = set()
    source_hashes: dict[str, str] = {}
    while pending:
        module = pending.pop(0)
        if module in closure:
            continue
        source = _numstability_source_path(source_root, module)
        source_hashes[module] = sha256_file(source)
        closure.add(module)
        for dependency in _source_imports(source):
            if dependency not in closure and dependency not in pending:
                pending.append(dependency)
        pending.sort()
    missing_signature_modules = sorted(signature_modules - closure)
    if missing_signature_modules:
        raise BenchmarkError(
            "signature prerequisite owner modules are outside the exposed import "
            f"closure: {', '.join(missing_signature_modules)}"
        )
    files: list[dict[str, Any]] = []
    for module in sorted(closure):
        source_olean = _numstability_olean_path(olean_root, module)
        if source_olean.is_symlink() or not source_olean.is_file():
            raise BenchmarkError(
                f"compiled NumStability module is missing or unsafe: {source_olean}"
            )
        relative = Path(*module.split(".")).with_suffix(".olean")
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True, mode=0o700)
        write_bytes_atomic(target, source_olean.read_bytes(), mode=0o400)
        files.append(
            {
                "module": module,
                "relative_path": relative.as_posix(),
                "olean_sha256": sha256_file(target),
                "source_sha256": source_hashes[module],
                "packet_exposed": module in exposed_modules,
                "signature_interface": module in signature_modules,
                "packet_selected": module in selected_modules,
            }
        )
    manifest = {
        "schema_version": "formalization-design17-packet-olean-runtime-3",
        "exposed_modules": sorted(exposed_modules),
        "signature_interface_modules": sorted(signature_modules),
        "selected_modules": sorted(selected_modules),
        "closure_modules": sorted(closure),
        "files": files,
    }
    write_json_atomic(destination / "runtime-manifest.json", manifest, mode=0o400)
    return manifest


def _treatment_interface_check(
    *,
    candidate_text: str,
    composition: Mapping[str, Any],
    private_dossier: Mapping[str, Any],
) -> dict[str, Any]:
    """Verify that R1's target type uses only packet-exposed declarations.

    Transitive implementation dependencies of an exposed declaration are
    permitted.  A declaration is rejected only when candidate-owned statement
    code directly reaches an unlisted NumStability declaration.
    """

    allowed_names, exposed_modules, signature_modules = _packet_treatment_surfaces(
        composition
    )
    allowed_modules = exposed_modules
    imported_modules: set[str] = set()
    noncanonical_import_lines: list[int] = []
    masked_text = _mask_noncode(candidate_text)
    original_lines = candidate_text.splitlines()
    masked_lines = masked_text.splitlines()
    if len(original_lines) != len(masked_lines):
        raise BenchmarkError("candidate import scan lost line structure")
    for line_number, (line, masked_line) in enumerate(
        zip(original_lines, masked_lines, strict=True), 1
    ):
        command = re.match(
            r"^\s*(?:public\s+)?import\b", masked_line
        )
        if command is None:
            continue
        match = re.match(r"^\s*(?:public\s+)?import\s+(.+?)\s*(?:--.*)?$", line)
        if match is None or "/-" in line or "-/" in line:
            noncanonical_import_lines.append(line_number)
            continue
        for module in match.group(1).split():
            if re.fullmatch(r"[A-Za-z0-9_'.]+", module) is None:
                noncanonical_import_lines.append(line_number)
                continue
            if module == "NumStability" or module.startswith("NumStability."):
                imported_modules.add(module)
    forbidden_imports = sorted(imported_modules - allowed_modules)
    raw = private_dossier.get("raw_semantic_report")
    if not isinstance(raw, Mapping):
        raise BenchmarkError("private semantic dossier omitted its raw report")
    dependencies = raw.get("dependencies")
    edges = raw.get("edges")
    if not isinstance(dependencies, list) or not isinstance(edges, list):
        raise BenchmarkError("private semantic dossier dependency graph is malformed")
    owners = {
        item.get("name"): item.get("owner_module")
        for item in dependencies
        if isinstance(item, Mapping)
        and isinstance(item.get("name"), str)
        and isinstance(item.get("owner_module"), str)
    }
    forbidden_declarations: set[str] = set()
    for edge in edges:
        if not isinstance(edge, Mapping):
            raise BenchmarkError("private semantic dossier edge is malformed")
        parent = edge.get("parent")
        child = edge.get("child")
        if not isinstance(parent, str) or not isinstance(child, str):
            raise BenchmarkError("private semantic dossier edge names are malformed")
        parent_owner = (
            "Candidate" if parent == "HighamBenchCandidate.target" else owners.get(parent)
        )
        child_owner = owners.get(child)
        if (
            isinstance(parent_owner, str)
            and (parent_owner == "Candidate" or parent_owner.startswith("Candidate."))
            and isinstance(child_owner, str)
            and (
                child_owner == "NumStability"
                or child_owner.startswith("NumStability.")
            )
            and child not in allowed_names
        ):
            forbidden_declarations.add(child)
    result = {
        "schema_version": "formalization-design17-treatment-interface-3",
        "allowed_declarations": sorted(allowed_names),
        "packet_exposed_modules": sorted(exposed_modules),
        "signature_interface_modules": sorted(signature_modules),
        "allowed_modules": sorted(allowed_modules),
        "observed_numstability_imports": sorted(imported_modules),
        "noncanonical_import_lines": noncanonical_import_lines,
        "forbidden_imports": forbidden_imports,
        "forbidden_direct_declarations": sorted(forbidden_declarations),
    }
    result["pass"] = (
        not noncanonical_import_lines
        and not forbidden_imports
        and not forbidden_declarations
    )
    return result


def _statement_repair_feedback(validation: Mapping[str, Any]) -> dict[str, Any]:
    failure = validation.get("failure_code")
    mismatch = (
        "The submitted statement does not elaborate in the frozen Lean environment."
        if failure == "COMPILATION_FAILURE"
        else "The submission violates the fixed single-target statement integrity contract."
    )
    return make_repair_feedback(
        [
            {
                "paper_requirement": (
                    "The exact paper proposition and its supporting definitions must "
                    "elaborate, with exactly one proof hole as the entire proof of the "
                    "required final target."
                ),
                "candidate_mismatch": mismatch,
            }
        ]
    )


def _audit_usage(decision: Mapping[str, Any]) -> tuple[dict[str, int], bool]:
    total = {
        "input_tokens": 0,
        "cached_input_tokens": 0,
        "cache_write_input_tokens": 0,
        "output_tokens": 0,
        "reasoning_output_tokens": 0,
        "total_tokens": 0,
    }
    complete = True
    telemetry = decision.get(
        "incremental_auditor_telemetry", decision.get("auditor_telemetry", [])
    )
    if not isinstance(telemetry, list):
        raise BenchmarkError("audit telemetry is malformed")
    for role in telemetry:
        if not isinstance(role, Mapping):
            raise BenchmarkError("audit role telemetry is malformed")
        usage = role.get("usage")
        if isinstance(usage, Mapping):
            total = _usage_add(total, usage)
        tries = role.get("tries", [])
        if not isinstance(tries, list):
            raise BenchmarkError("audit try telemetry is malformed")
        if any(
            not isinstance(item, Mapping) or item.get("usage_complete") is not True
            for item in tries
        ):
            complete = False
    return total, complete


def _library_exploration_policy(events_path: Path) -> dict[str, Any]:
    """Reject commands that inspect package/library storage outside the packet."""

    if not events_path.is_file() or events_path.is_symlink():
        raise BenchmarkError("formalizer event trace is missing or unsafe")
    forbidden_fragments = (
        "/packages",
        "/library-olean",
        "/library-index",
        "/library/NumStability",
    )
    violations: list[dict[str, Any]] = []
    command_count = 0
    for line_number, line in enumerate(
        events_path.read_text(encoding="utf-8").splitlines(), 1
    ):
        try:
            event = json.loads(line)
        except json.JSONDecodeError as error:
            raise BenchmarkError("formalizer event trace is malformed") from error
        if not isinstance(event, Mapping):
            raise BenchmarkError("formalizer event trace item is malformed")
        params = event.get("params")
        item = params.get("item") if isinstance(params, Mapping) else None
        if not isinstance(item, Mapping) or item.get("type") != "commandExecution":
            continue
        command = item.get("command")
        if not isinstance(command, str):
            continue
        command_count += 1
        lowered = command.casefold()
        reasons = [
            f"forbidden mounted path {fragment}"
            for fragment in forbidden_fragments
            if fragment.casefold() in lowered
        ]
        if re.search(r"\bstrings(?:\s|$)", lowered):
            reasons.append("binary string-table inspection")
        if re.search(r"\bfind\s+/(?:\s|$)", lowered):
            reasons.append("root-filesystem search")
        if "lean_path" in lowered:
            reasons.append("compiler search-path inspection")
        lean_sources = {
            value
            for value in re.findall(r"(?<![A-Za-z0-9_./-])([A-Za-z0-9_./-]+\.lean)\b", command)
            if value != "Candidate.lean" and not value.endswith("/Candidate.lean")
        }
        if lean_sources:
            reasons.append("non-candidate Lean probe or source")
        if re.search(r"\b(?:env|printenv)\b", lowered):
            reasons.append("environment enumeration")
        lean_invocations = len(re.findall(r"(?<![A-Za-z0-9_./-])lean(?:\s|$)", command))
        exact_compile = re.search(
            r"(?<![A-Za-z0-9_./-])lean\s+--root\s+\.\s+-o\s+"
            r"Candidate\.olean\s+Candidate\.lean(?:\s|[;&|'\"]|$)",
            command,
        )
        if lean_invocations and (lean_invocations != 1 or exact_compile is None):
            reasons.append("noncanonical Lean invocation")
        if reasons:
            violations.append(
                {
                    "line": line_number,
                    "command_sha256": __import__("hashlib").sha256(
                        command.encode("utf-8")
                    ).hexdigest(),
                    "reasons": reasons,
                }
            )
    return {
        "schema_version": "formalization-design17-library-exploration-policy-1",
        "command_count": command_count,
        "violations": violations,
        "pass": not violations,
    }


def _prepare_warm_fork(
    *, args: argparse.Namespace, deployment: Deployment,
    spec: ConditionSpec, condition_root: Path,
) -> tuple[Path | None, dict[str, Any]]:
    """Copy and verify a task-private scout checkpoint before the task clock."""
    warm_fork: dict[str, Any] = {}
    state_root: Path | None = None
    warm_root_arg = getattr(args, "warm_root", None)
    if spec.name == "R1" and warm_root_arg is not None:
        scout_prompt_arg = getattr(args, "warm_scout_prompt_path", None)
        if scout_prompt_arg is None:
            raise BenchmarkError("Pilot 18 warm-root scout prompt identity is missing")
        warm_root = Path(warm_root_arg).expanduser().resolve()
        warm = load_json(warm_root / "warm-root.json")
        checkpoint = warm_root / "checkpoint"
        if (
            warm.get("schema_version") != "pilot-18-warm-root-1"
            or warm.get("status") != "READY"
            or warm.get("model") != args.model
            or warm.get("reasoning_effort") != args.reasoning_effort
            or warm.get("scout_prompt_sha256") != sha256_file(
                Path(scout_prompt_arg)
            )
            or warm.get("library_atlas_sha256") != sha256_file(
                deployment.library_atlas / "declarations.jsonl"
            )
            or warm.get("codex_binary_sha256") != sha256_file(deployment.codex_binary)
            or warm.get("code_mode_host_sha256") != deployment.code_mode_host_sha256
            or not isinstance(warm.get("source_thread_id"), str)
            or not isinstance(warm.get("source_last_turn_id"), str)
            or not isinstance(warm.get("source_cumulative_usage"), dict)
        ):
            raise BenchmarkError("Pilot 18 warm-root fork record is incompatible")
        verify_tree_manifest(
            checkpoint, warm.get("checkpoint_manifest"), label="Pilot 18 warm root"
        )
        assert_no_credentials_in_tree(checkpoint, deployment.auth_file)
        seed = condition_root / "warm-seed"
        if seed.exists() or seed.is_symlink():
            raise BenchmarkError("Pilot 18 private warm seed already exists")
        shutil.copytree(checkpoint, seed, symlinks=True)
        verify_tree_manifest(
            seed, warm["checkpoint_manifest"], label="Pilot 18 private warm seed"
        )
        state_root = seed / "state"
        warm_fork = {
            "fork_source_thread_id": warm["source_thread_id"],
            "fork_source_last_turn_id": warm["source_last_turn_id"],
            "fork_source_cumulative_usage": warm["source_cumulative_usage"],
        }
    return state_root, warm_fork


def _run_statement_condition_attempts(
    *,
    args: argparse.Namespace,
    deployment: Deployment,
    spec: ConditionSpec,
    packet: dict[str, Any],
    paper: Path,
    prompt: bytes,
    composition: dict[str, Any],
    workspace: Path,
    source: Path,
    candidate: Path,
    condition_root: Path,
    hardware_snapshot: dict[str, Any] | None,
    retrieval_seconds: float,
    packet_library_olean: Path | None,
    packet_runtime_manifest: Mapping[str, Any] | None,
) -> dict[str, Any]:
    """Run the statement-only audit/repair loop in one persisted conversation."""

    state_root, warm_fork = _prepare_warm_fork(
        args=args, deployment=deployment, spec=spec,
        condition_root=condition_root,
    )

    driver = StatementCodexDriver(
        codex_binary=deployment.codex_binary,
        code_mode_host_sha256=deployment.code_mode_host_sha256,
        model=args.model,
        reasoning_effort=args.reasoning_effort,
        state_root=state_root,
        auth_file=deployment.auth_file,
        bwrap_binary=deployment.bwrap_binary,
        offline_shell=deployment.offline_shell,
        toolchain_root=deployment.toolchain_root,
        packages_root=deployment.packages_root,
        library_olean=packet_library_olean,
        workspace_writable=True,
        protected_workspace_paths=[
            source,
            workspace / "ENVIRONMENT.md",
            workspace / "LIBRARY_API.md",
        ],
        **warm_fork,
    )
    attempts: list[dict[str, Any]] = []
    cumulative_usage = {
        "input_tokens": 0,
        "cached_input_tokens": 0,
        "cache_write_input_tokens": 0,
        "output_tokens": 0,
        "reasoning_output_tokens": 0,
        "total_tokens": 0,
    }
    cumulative_active_seconds = 0.0
    cumulative_formalizer_wall_seconds = 0.0
    cumulative_validation_seconds = 0.0
    cumulative_dossier_seconds = 0.0
    cumulative_audit_seconds = 0.0
    cumulative_audit_usage = dict(cumulative_usage)
    audit_usage_complete = True
    thread_id: str | None = None
    feedback: dict[str, Any] | None = None
    terminal_status = "ATTEMPT_LIMIT_UNFAITHFUL"
    final_frozen: dict[str, Any] | None = None
    final_text = ""
    try:
        for attempt_number in range(1, int(args.submission_limit) + 1):
            remaining = float(args.time_limit_seconds) - cumulative_active_seconds
            if remaining <= 0:
                terminal_status = "ACTIVE_TIME_LIMIT"
                break
            if attempt_number == 1:
                turn_prompt = prompt.decode("utf-8")
                prompt_kind = "initial"
            else:
                if feedback is None:
                    raise BenchmarkError("repair turn has no frozen neutral feedback")
                template = (ROOT / "prompts" / "statement_repair.md").read_text(
                    encoding="utf-8"
                )
                turn_prompt = template.replace(
                    "{{FEEDBACK_JSON}}", json.dumps(feedback, indent=2, sort_keys=True)
                )
                prompt_kind = "repair"
            attempt_root = condition_root / "submissions" / f"{attempt_number:02d}"
            attempt_root.mkdir(parents=True, mode=0o700)
            hardware_before = snapshot_hardware(strict=True)
            write_json_atomic(
                attempt_root / "hardware-before.json", hardware_before, mode=0o400
            )
            requested_thread_id = thread_id
            turn = driver.run_turn(
                prompt=turn_prompt,
                workspace=workspace,
                artifact_dir=attempt_root / "formalizer",
                timeout_seconds=remaining,
                thread_id=thread_id,
            )
            freeze_started = time.perf_counter_ns()
            frozen = freeze_candidate(
                candidate,
                attempt_root / "Candidate.lean",
                auth_file=deployment.auth_file,
            )
            freeze_completed = time.perf_counter_ns()
            freeze_seconds = (freeze_completed - freeze_started) / 1_000_000_000
            if (
                turn.active_started_perf_ns is None
                or turn.active_ended_perf_ns is None
            ):
                raise BenchmarkError("formalizer omitted measured active-time boundaries")
            clock = _submission_clock(
                active_started_perf_ns=turn.active_started_perf_ns,
                active_ended_perf_ns=turn.active_ended_perf_ns,
                freeze_started_perf_ns=freeze_started,
                freeze_completed_perf_ns=freeze_completed,
            )
            model_active_seconds = clock["model_active_seconds"]
            post_turn_through_freeze_seconds = clock[
                "post_turn_through_freeze_seconds"
            ]
            freeze_seconds = clock["candidate_freeze_seconds"]
            active_seconds = clock["contestant_active_seconds"]
            cumulative_active_seconds += active_seconds
            cumulative_formalizer_wall_seconds += float(turn.wall_seconds)
            cumulative_usage = _usage_add(cumulative_usage, turn.usage)
            final_frozen = frozen
            frozen_candidate = attempt_root / "Candidate.lean"
            final_text = frozen_candidate.read_text(encoding="utf-8")
            hardware_after = snapshot_hardware(strict=True)

            returned_thread_id = turn.thread_id
            thread_identity_valid = (
                isinstance(returned_thread_id, str)
                and bool(returned_thread_id)
                and (
                    requested_thread_id is None
                    or returned_thread_id == requested_thread_id
                )
            )
            if thread_identity_valid:
                thread_id = returned_thread_id
            exploration_policy = _library_exploration_policy(
                attempt_root / "formalizer" / "events.jsonl"
            )
            write_json_atomic(
                attempt_root / "library-exploration-policy.json",
                exploration_policy,
                mode=0o400,
            )
            driver.assert_safe_control_surfaces(
                workspace, scan_workspace=turn.failure_kind != "workspace_limit"
            )

            prevalidation_status: str | None = None
            prevalidation_reason: str | None = None
            if exploration_policy["pass"] is not True:
                prevalidation_status = "RETRIEVAL_INTERFACE_RULE_VIOLATION"
                prevalidation_reason = "retrieval interface policy violation"
            elif not thread_identity_valid:
                prevalidation_status = "FORMALIZER_INCIDENT"
                prevalidation_reason = (
                    "formalizer did not preserve one nonempty conversation identity"
                )
            elif cumulative_active_seconds > float(args.time_limit_seconds):
                prevalidation_status = "ACTIVE_TIME_LIMIT"
                prevalidation_reason = "inclusive post-freeze active-time cap exceeded"
            elif turn.timed_out:
                prevalidation_status = "ACTIVE_TIME_LIMIT"
                prevalidation_reason = "formalizer turn timed out"
            elif turn.exit_code != 0 or not turn.usage_complete:
                prevalidation_status = "FORMALIZER_INCIDENT"
                prevalidation_reason = "formalizer turn or usage telemetry was incomplete"

            if prevalidation_status is None:
                validation_started = time.perf_counter_ns()
                validation_scratch = attempt_root / "validation-scratch"
                validation_scratch.mkdir(mode=0o700)
                validation = validate_candidate(
                    frozen_candidate,
                    compiler_command=compiler_command(
                        deployment, spec.compiler_condition
                    ),
                    scratch_root=validation_scratch,
                    timeout_seconds=float(args.validation_timeout_seconds),
                    allow_single_target_sorry=True,
                )
                validation_seconds = (
                    time.perf_counter_ns() - validation_started
                ) / 1_000_000_000
                cumulative_validation_seconds += validation_seconds
            else:
                validation_seconds = 0.0
                validation = {
                    "schema_version": "formalization-validator-not-run-1",
                    "pass": False,
                    "failure_code": "NOT_RUN_PREVALIDATION_TERMINAL",
                    "reason": prevalidation_reason,
                    "candidate_sha256": frozen["sha256"],
                }
            write_json_atomic(attempt_root / "validation.json", validation, mode=0o400)
            attempt: dict[str, Any] = {
                "attempt": attempt_number,
                "prompt_kind": prompt_kind,
                "thread_id": thread_id,
                "requested_thread_id": requested_thread_id,
                "thread_identity_valid": thread_identity_valid,
                "formalizer_exit_code": turn.exit_code,
                "formalizer_timed_out": turn.timed_out,
                "formalizer_failure_kind": turn.failure_kind,
                "formalizer_wall_seconds": turn.wall_seconds,
                "model_active_seconds": model_active_seconds,
                "post_turn_through_freeze_seconds": post_turn_through_freeze_seconds,
                "candidate_freeze_seconds": freeze_seconds,
                "contestant_active_seconds": active_seconds,
                "contestant_active_seconds_cumulative": cumulative_active_seconds,
                "usage": turn.usage,
                "usage_complete": turn.usage_complete,
                "candidate": frozen,
                "hardware_before": hardware_before,
                "hardware_after": hardware_after,
                "validation_sha256": sha256_file(attempt_root / "validation.json"),
                "validation_seconds_excluded": validation_seconds,
                "validation_pass": validation.get("pass") is True,
                "library_exploration_policy_sha256": sha256_file(
                    attempt_root / "library-exploration-policy.json"
                ),
            }
            if prevalidation_status is not None:
                attempt["status"] = prevalidation_status
                attempt["terminal_reason"] = prevalidation_reason
                if prevalidation_status == "ACTIVE_TIME_LIMIT" and (
                    cumulative_active_seconds > float(args.time_limit_seconds)
                ):
                    attempt["active_time_limit_overshoot_seconds"] = (
                        cumulative_active_seconds - float(args.time_limit_seconds)
                    )
                attempts.append(attempt)
                terminal_status = prevalidation_status
                break
            if cumulative_active_seconds > float(args.time_limit_seconds):
                # The pre-validation gate above must make this branch unreachable.
                attempt["status"] = "FORMALIZER_INCIDENT"
                attempt["terminal_reason"] = "active-time cap gate was bypassed"
                attempt["active_time_limit_overshoot_seconds"] = (
                    cumulative_active_seconds - float(args.time_limit_seconds)
                )
                attempts.append(attempt)
                terminal_status = "FORMALIZER_INCIDENT"
                break
            if validation.get("pass") is not True:
                if validation.get("failure_code") == "INFRASTRUCTURE_FAILURE":
                    attempt["status"] = "VALIDATION_INFRASTRUCTURE_INCIDENT"
                    attempts.append(attempt)
                    terminal_status = "VALIDATION_INFRASTRUCTURE_INCIDENT"
                    break
                feedback = _statement_repair_feedback(validation)
                write_json_atomic(
                    attempt_root / "repair_feedback.json", feedback, mode=0o400
                )
                attempt["repair_feedback_sha256"] = sha256_file(
                    attempt_root / "repair_feedback.json"
                )
                attempt["status"] = "VALIDATION_REJECTED"
                attempts.append(attempt)
                continue

            dossier_root = attempt_root / "audit-preparation"
            dossier_root.mkdir(mode=0o700)
            dossier_scratch = dossier_root / "scratch"
            dossier_scratch.mkdir(mode=0o700)
            dossier_started = time.perf_counter_ns()
            try:
                blind, private = prepare_candidate_audit(
                    frozen_candidate,
                    compiler_command=compiler_command(
                        deployment, spec.compiler_condition
                    ),
                    extractor_command=extractor_command(
                        deployment,
                        spec.compiler_condition,
                        Path(__file__).with_name("declaration_dossier.lean"),
                    ),
                    compiler_environment={},
                    extractor_environment={},
                    scratch_root=dossier_scratch,
                    timeout_seconds=float(args.validation_timeout_seconds),
                    allow_single_target_sorry=True,
                )
            except CandidateAuditError as error:
                attempt["dossier_seconds_excluded"] = (
                    time.perf_counter_ns() - dossier_started
                ) / 1_000_000_000
                cumulative_dossier_seconds += attempt["dossier_seconds_excluded"]
                attempt["status"] = "AUDIT_PREPARATION_INCIDENT"
                attempt["audit_preparation_failure_code"] = error.failure_code
                attempt["audit_preparation_error"] = str(error)
                attempts.append(attempt)
                terminal_status = "AUDIT_PREPARATION_INCIDENT"
                break
            attempt["dossier_seconds_excluded"] = (
                time.perf_counter_ns() - dossier_started
            ) / 1_000_000_000
            cumulative_dossier_seconds += attempt["dossier_seconds_excluded"]
            blind_path = dossier_root / "blind_semantic_dossier.json"
            private_path = dossier_root / "private_semantic_manifest.json"
            write_json_atomic(blind_path, blind, mode=0o400)
            write_json_atomic(private_path, private, mode=0o400)
            interface = _treatment_interface_check(
                candidate_text=final_text,
                composition=composition,
                private_dossier=private,
            )
            write_json_atomic(
                attempt_root / "treatment-interface.json", interface, mode=0o400
            )
            attempt["treatment_interface_sha256"] = sha256_file(
                attempt_root / "treatment-interface.json"
            )
            if interface["pass"] is not True:
                feedback = make_repair_feedback(
                    [
                        {
                            "paper_requirement": (
                                "The statement must use only declarations exposed by the "
                                "frozen task-time retrieval packet."
                            ),
                            "candidate_mismatch": (
                                "The statement directly uses or imports a declaration outside "
                                "that bounded interface."
                            ),
                        }
                    ]
                )
                write_json_atomic(
                    attempt_root / "repair_feedback.json", feedback, mode=0o400
                )
                attempt["repair_feedback_sha256"] = sha256_file(
                    attempt_root / "repair_feedback.json"
                )
                attempt["status"] = "INTERFACE_REJECTED"
                attempts.append(attempt)
                continue

            semantic_sha256 = blind.get("semantic_sha256")
            if not isinstance(semantic_sha256, str) or not semantic_sha256:
                raise BenchmarkError("semantic dossier omitted its identity")
            audit_root = condition_root / "audits" / semantic_sha256
            audit = AuditController(
                codex_binary=deployment.codex_binary,
                code_mode_host_sha256=deployment.code_mode_host_sha256,
                auth_file=deployment.auth_file,
                model=args.audit_model,
                reasoning_effort=args.audit_reasoning_effort,
                timeout_seconds=float(args.audit_timeout_seconds),
                maximum_infrastructure_retries=int(args.audit_infrastructure_retries),
                bwrap_binary=deployment.bwrap_binary,
                offline_shell=deployment.offline_shell,
                toolchain_root=deployment.toolchain_root,
                packages_root=deployment.packages_root,
                forbidden_feedback_identifiers=interface["allowed_declarations"],
            )
            audit_started = time.perf_counter_ns()
            try:
                decision = audit.run(
                    task_id=packet["task_id"],
                    paper_path=paper,
                    paper_sha256=packet["paper_pdf"]["sha256"],
                    source_packet=source / "task.md",
                    dossier_path=blind_path,
                    semantic_sha256=semantic_sha256,
                    audit_root=audit_root,
                )
            except BenchmarkError as error:
                audit_seconds = (
                    time.perf_counter_ns() - audit_started
                ) / 1_000_000_000
                cumulative_audit_seconds += audit_seconds
                incident = audit.seal_incident(
                    audit_root=audit_root,
                    task_id=packet["task_id"],
                    paper_sha256=packet["paper_pdf"]["sha256"],
                    semantic_sha256=semantic_sha256,
                    error=str(error),
                    wall_seconds=audit_seconds,
                    classification="audit_system_infrastructure",
                )
                incident_usage = incident.get("usage")
                if isinstance(incident_usage, Mapping):
                    cumulative_audit_usage = _usage_add(
                        cumulative_audit_usage, incident_usage
                    )
                audit_usage_complete = (
                    audit_usage_complete
                    and incident.get("usage_complete") is True
                )
                attempt["audit"] = {
                    "verdict": "audit-system-incident",
                    "accepted": False,
                    "wall_seconds_excluded": audit_seconds,
                    "error": str(error),
                    "incident_sha256": sha256_file(audit_root / "incident.json"),
                    "usage_excluded": incident.get("usage"),
                    "usage_complete": incident.get("usage_complete") is True,
                }
                attempt["status"] = "AUDIT_SYSTEM_INCIDENT"
                attempts.append(attempt)
                terminal_status = "AUDIT_SYSTEM_INCIDENT"
                break
            audit_seconds = (time.perf_counter_ns() - audit_started) / 1_000_000_000
            cumulative_audit_seconds += audit_seconds
            role_usage, role_usage_complete = _audit_usage(decision)
            cumulative_audit_usage = _usage_add(cumulative_audit_usage, role_usage)
            audit_usage_complete = audit_usage_complete and role_usage_complete
            attempt["semantic_sha256"] = semantic_sha256
            attempt["blind_dossier_sha256"] = sha256_file(blind_path)
            attempt["private_dossier_sha256"] = sha256_file(private_path)
            attempt["audit"] = {
                "verdict": decision.get("verdict"),
                "accepted": decision.get("accepted") is True,
                "decision_sha256": sha256_file(audit_root / "decision.json"),
                "wall_seconds_excluded": audit_seconds,
                "usage_excluded": role_usage,
                "usage_complete": role_usage_complete,
            }
            if decision.get("accepted") is True:
                attempt["status"] = "ACCEPTED_FAITHFUL"
                attempts.append(attempt)
                terminal_status = "ACCEPTED_FAITHFUL"
                break
            feedback = decision.get("repair_feedback")
            if not isinstance(feedback, dict):
                attempt["status"] = "AUDIT_SYSTEM_INCIDENT"
                attempts.append(attempt)
                terminal_status = "AUDIT_SYSTEM_INCIDENT"
                break
            write_json_atomic(
                attempt_root / "repair_feedback.json", feedback, mode=0o400
            )
            attempt["repair_feedback_sha256"] = sha256_file(
                attempt_root / "repair_feedback.json"
            )
            attempt["status"] = "AUDIT_REJECTED"
            attempts.append(attempt)
    finally:
        driver.close(artifact_dir=condition_root / "session-close")

    if final_frozen is None:
        raise BenchmarkError("statement condition produced no frozen submission")
    report = {
        "schema_version": "formalization-design17-statement-condition-1",
        "scientific_status": SCIENTIFIC_STATUS,
        "benchmark_object": "FORMALIZED_STATEMENT_ONLY",
        "source_contract": "statement-only-single-target-sorry",
        "faithfulness_status": _condition_faithfulness_status(terminal_status),
        "result_status": terminal_status,
        "task_id": packet["task_id"],
        "condition": spec.name,
        "corpus_id": spec.corpus_id,
        "created_at_utc": utc_now(),
        "fresh_stateless_formalizer": not bool(warm_fork),
        "warm_or_forked_conversation": bool(warm_fork),
        "warm_source_thread_id": (
            warm_fork.get("fork_source_thread_id") if warm_fork else None
        ),
        "same_conversation_repairs": True,
        "submission_limit": int(args.submission_limit),
        "submission_count": len(attempts),
        "attempts": attempts,
        "hardware_envelope_required": True,
        "hardware_snapshot": hardware_snapshot,
        "model": args.model,
        "reasoning_effort": args.reasoning_effort,
        "audit_model": args.audit_model,
        "audit_reasoning_effort": args.audit_reasoning_effort,
        "route_status": composition["route_status"],
        "library_olean_visible": packet_library_olean is not None,
        "packet_olean_runtime": (
            dict(packet_runtime_manifest)
            if packet_runtime_manifest is not None
            else None
        ),
        "composition_packet_sha256": sha256_file(
            condition_root / "composition-packet.json"
        ),
        "library_api_sha256": sha256_file(workspace / "LIBRARY_API.md"),
        "staged_task_sha256": sha256_file(source / "task.md"),
        "source_pdf_sha256": sha256_file(source / "paper.pdf"),
        "candidate": final_frozen,
        "candidate_sha256": final_frozen["sha256"],
        "candidate_lines": len(final_text.splitlines()),
        "numstability_name_mentions": final_text.count("NumStability"),
        "retrieval_wall_seconds": retrieval_seconds,
        "formalizer_wall_seconds": cumulative_formalizer_wall_seconds,
        "contestant_active_seconds": cumulative_active_seconds,
        "contestant_system_wall_seconds": retrieval_seconds
        + cumulative_active_seconds,
        "validation_seconds_excluded_from_contestant": cumulative_validation_seconds,
        "dossier_seconds_excluded_from_contestant": cumulative_dossier_seconds,
        "audit_seconds_excluded_from_contestant": cumulative_audit_seconds,
        "usage": cumulative_usage,
        "net_new_tokens": _net_new_usage(cumulative_usage)["net_new_tokens"],
        "audit_usage_excluded": cumulative_audit_usage,
        "audit_usage_complete": audit_usage_complete,
        "validation_pass": bool(attempts and attempts[-1]["validation_pass"]),
        "output_root": str(condition_root),
    }
    write_json_atomic(condition_root / "report.json", report, mode=0o400)
    return report


def _run_condition(
    *,
    args: argparse.Namespace,
    deployment: Deployment,
    spec: ConditionSpec,
    packet_path: Path,
    packet: dict[str, Any],
    contract_additions: list[str],
    paper: Path,
    prompt: bytes,
    output_root: Path,
) -> dict[str, Any]:
    condition_root = output_root / spec.name
    condition_root.mkdir(mode=0o700)

    hardware_snapshot = (
        snapshot_hardware(strict=True) if args.require_titan_envelope else None
    )

    retrieval_started = time.monotonic()
    retrieval_composition, _source_signature_markdown = build_composition_packet(
        source_packet_path=packet_path,
        atlas_paths=list(spec.atlas_paths),
        corpus_id=spec.corpus_id,
        contract_additions=contract_additions,
        root_limit=int(args.root_limit),
        dependency_limit=int(args.dependency_limit),
        maximum_markdown_bytes=int(args.maximum_packet_bytes),
        selection_policy=getattr(args, "selection_policy", "legacy-coupled-title"),
    )
    signature_interface = _derive_signature_interface(
        deployment=deployment,
        composition=retrieval_composition,
        output_root=condition_root,
        timeout_seconds=float(args.validation_timeout_seconds),
    )
    if spec.name == "R0" and signature_interface["direct_type_declarations"]:
        raise BenchmarkError("Mathlib-only packet has NumStability type dependencies")
    canonical_signatures = {
        record["name"]: record["readable_signature"]
        for record in signature_interface["seed_declarations"]
    }
    composition, api_markdown = build_composition_packet(
        source_packet_path=packet_path,
        atlas_paths=list(spec.atlas_paths),
        corpus_id=spec.corpus_id,
        contract_additions=contract_additions,
        root_limit=int(args.root_limit),
        dependency_limit=int(args.dependency_limit),
        maximum_markdown_bytes=int(args.maximum_packet_bytes),
        exposed_signature_overrides=canonical_signatures,
        selection_policy=getattr(args, "selection_policy", "legacy-coupled-title"),
    )
    if (
        composition["route_status"] != retrieval_composition["route_status"]
        or _packet_exposed_records(composition)
        != _packet_exposed_records(retrieval_composition)
    ):
        raise BenchmarkError("canonical signature rendering changed packet retrieval")
    composition["retrieval_schema_version"] = composition["schema_version"]
    composition["schema_version"] = "formalization-composition-packet-2"
    composition["signature_interface"] = signature_interface
    composition["policy"]["type_interface_rule"] = "one-hop-elaborated-types-only"
    composition["policy"]["declaration_bodies_inspected"] = False
    write_json_atomic(
        condition_root / "composition-packet.json", composition, mode=0o400
    )
    packet_library_olean: Path | None = None
    packet_runtime_manifest: dict[str, Any] | None = None
    _allowed_names, selected_treatment_modules = _packet_treatment_allowlist(
        composition
    )
    if args.statement_only and spec.name == "R1" and selected_treatment_modules:
        if spec.library_olean is None:
            raise BenchmarkError("R1 packet selected NumStability without an OLean tree")
        packet_library_olean = condition_root / "packet-library-olean"
        packet_runtime_manifest = _build_packet_olean_runtime(
            composition=composition,
            source_root=deployment.library_source,
            olean_root=spec.library_olean,
            destination=packet_library_olean,
        )
    retrieval_seconds = time.monotonic() - retrieval_started

    workspace = condition_root / "workspace"
    source = workspace / "source"
    source.mkdir(parents=True, mode=0o700)
    shutil.copyfile(paper, source / "paper.pdf")
    (source / "paper.pdf").chmod(0o400)
    staged_packet = dict(packet)
    if contract_additions:
        staged_packet["scope_constraints"] = [
            *staged_packet["scope_constraints"],
            *contract_additions,
        ]
    write_bytes_atomic(
        source / "task.md", _task_packet_markdown(staged_packet).encode("utf-8"), mode=0o400
    )
    candidate = workspace / "Candidate.lean"
    write_bytes_atomic(
        candidate,
        _candidate_template(
            composition, statement_only=bool(args.statement_only)
        ).encode("utf-8"),
    )
    write_bytes_atomic(
        workspace / "ENVIRONMENT.md", _environment_note().encode("utf-8"), mode=0o400
    )
    write_bytes_atomic(workspace / "LIBRARY_API.md", api_markdown, mode=0o400)

    preflight_scratch = condition_root / "template-validation-scratch"
    preflight_scratch.mkdir(mode=0o700)
    with compiled_candidate_workspace(
        candidate.read_bytes(),
        compiler_command=compiler_command(deployment, spec.compiler_condition),
        scratch_root=preflight_scratch,
        timeout_seconds=float(args.validation_timeout_seconds),
    ) as (_, preflight_compile):
        preflight = {
            "schema_version": "formalization-design16-template-compile-1",
            "pass": preflight_compile.get("pass") is True,
            "compile": preflight_compile,
        }
    write_json_atomic(condition_root / "template-validation.json", preflight, mode=0o400)
    if preflight["pass"] is not True:
        raise BenchmarkError(f"{spec.name} controller-generated template did not compile")

    if args.statement_only:
        return _run_statement_condition_attempts(
            args=args,
            deployment=deployment,
            spec=spec,
            packet=packet,
            paper=paper,
            prompt=prompt,
            composition=composition,
            workspace=workspace,
            source=source,
            candidate=candidate,
            condition_root=condition_root,
            hardware_snapshot=hardware_snapshot,
            retrieval_seconds=retrieval_seconds,
            packet_library_olean=packet_library_olean,
            packet_runtime_manifest=packet_runtime_manifest,
        )

    driver = CodexDriver(
        codex_binary=deployment.codex_binary,
        code_mode_host_sha256=deployment.code_mode_host_sha256,
        model=args.model,
        reasoning_effort=args.reasoning_effort,
        state_root=None,
        auth_file=deployment.auth_file,
        bwrap_binary=deployment.bwrap_binary,
        offline_shell=deployment.offline_shell,
        toolchain_root=deployment.toolchain_root,
        packages_root=deployment.packages_root,
        library_olean=spec.library_olean,
        workspace_writable=True,
        protected_workspace_paths=[
            source,
            workspace / "ENVIRONMENT.md",
            workspace / "LIBRARY_API.md",
        ],
    )
    formalizer_started = time.monotonic()
    try:
        turn = driver.run_turn(
            prompt=prompt.decode("utf-8"),
            workspace=workspace,
            artifact_dir=condition_root / "formalizer",
            timeout_seconds=float(args.time_limit_seconds),
        )
    finally:
        driver.close(artifact_dir=condition_root / "session-close")
    formalizer_seconds = time.monotonic() - formalizer_started

    freeze_started = time.perf_counter_ns()
    submission_root = condition_root / "submissions" / "01"
    submission_root.mkdir(parents=True, mode=0o700)
    frozen = freeze_candidate(
        candidate,
        submission_root / "Candidate.lean",
        auth_file=deployment.auth_file,
    )
    freeze_seconds = (time.perf_counter_ns() - freeze_started) / 1_000_000_000
    frozen_candidate = submission_root / "Candidate.lean"

    hardware_snapshot_after = (
        snapshot_hardware(strict=True) if args.require_titan_envelope else None
    )

    validation_started = time.monotonic()
    validation_scratch = condition_root / "validation-scratch"
    validation_scratch.mkdir(mode=0o700)
    validation = validate_candidate(
        frozen_candidate,
        compiler_command=compiler_command(deployment, spec.compiler_condition),
        scratch_root=validation_scratch,
        timeout_seconds=float(args.validation_timeout_seconds),
        allow_single_target_sorry=bool(args.statement_only),
    )
    validation_seconds = time.monotonic() - validation_started
    write_json_atomic(condition_root / "validation.json", validation, mode=0o400)

    candidate_text = frozen_candidate.read_text(encoding="utf-8")
    usage = turn.usage
    condition_pass = (
        turn.exit_code == 0
        and not turn.timed_out
        and turn.usage_complete
        and validation.get("pass") is True
    )
    report: dict[str, Any] = {
        "schema_version": "formalization-design17-matched-condition-2",
        "scientific_status": SCIENTIFIC_STATUS,
        "benchmark_object": (
            "FORMALIZED_STATEMENT_ONLY"
            if args.statement_only
            else "FORMALIZED_STATEMENT_AND_COMPLETE_PROOF"
        ),
        "source_contract": (
            "statement-only-single-target-sorry"
            if args.statement_only
            else "complete-kernel-checked-proof"
        ),
        "faithfulness_status": "NOT_AUDITED",
        "result_status": (
            "COMPILED_AND_INTEGRITY_VALIDATED" if condition_pass else "CONDITION_INCIDENT"
        ),
        "task_id": packet["task_id"],
        "condition": spec.name,
        "corpus_id": spec.corpus_id,
        "created_at_utc": utc_now(),
        "fresh_stateless_formalizer": True,
        "warm_or_forked_conversation": False,
        "hardware_envelope_required": bool(args.require_titan_envelope),
        "hardware_snapshot": hardware_snapshot,
        "hardware_snapshot_after": hardware_snapshot_after,
        "model": args.model,
        "reasoning_effort": args.reasoning_effort,
        "route_status": composition["route_status"],
        "primary_route": (
            composition["retrieved_roots"][0]["declaration"]["name"]
            if composition["retrieved_roots"]
            else None
        ),
        "library_olean_visible": spec.library_olean is not None,
        "atlas_input_sha256": [sha256_file(path) for path in spec.atlas_paths],
        "source_packet_sha256": sha256_file(packet_path),
        "prompt_sha256": sha256_file(output_root / "prompt.txt"),
        "composition_packet_sha256": sha256_file(
            condition_root / "composition-packet.json"
        ),
        "library_api_sha256": sha256_file(workspace / "LIBRARY_API.md"),
        "candidate": frozen,
        "candidate_sha256": frozen["sha256"],
        "candidate_lines": len(candidate_text.splitlines()),
        "numstability_name_mentions": candidate_text.count("NumStability"),
        "retrieval_wall_seconds": retrieval_seconds,
        "formalizer_wall_seconds": formalizer_seconds,
        "formalizer_active_seconds": (
            (turn.active_ended_perf_ns - turn.active_started_perf_ns) / 1_000_000_000
            if turn.active_started_perf_ns is not None
            and turn.active_ended_perf_ns is not None
            else None
        ),
        "candidate_freeze_seconds": freeze_seconds,
        "contestant_active_seconds": (
            (
                (turn.active_ended_perf_ns - turn.active_started_perf_ns)
                / 1_000_000_000
            )
            + freeze_seconds
            if turn.active_started_perf_ns is not None
            and turn.active_ended_perf_ns is not None
            else None
        ),
        "contestant_system_wall_seconds": retrieval_seconds + formalizer_seconds,
        "validation_seconds_excluded_from_contestant": validation_seconds,
        "formalizer_exit_code": turn.exit_code,
        "formalizer_timed_out": turn.timed_out,
        "usage_complete": turn.usage_complete,
        "usage": usage,
        "net_new_tokens": _net_new(usage),
        "validation_pass": validation.get("pass") is True,
        "output_root": str(condition_root),
    }
    write_json_atomic(condition_root / "report.json", report, mode=0o400)
    if not condition_pass:
        raise BenchmarkError(f"{spec.name} failed closed after formalization")
    return report


def run(args: argparse.Namespace) -> dict[str, Any]:
    if args.statement_only and not args.require_titan_envelope:
        raise BenchmarkError(
            "statement-only scientific runs require the authenticated Titan envelope"
        )
    if args.statement_only and (
        args.model != "gpt-5.6-sol"
        or args.reasoning_effort != "xhigh"
        or args.audit_model != "gpt-6-astra"
        or args.audit_reasoning_effort != "high"
        or args.submission_limit != 4
    ):
        raise BenchmarkError(
            "statement-only runs freeze Sol xhigh, Astra high, and four submissions"
        )
    task_id = args.task_id.strip().upper().replace("_", "-")
    if task_id not in ALLOWED_EXPLORATORY_TASKS:
        raise BenchmarkError("task is not in the 13-task Design-16 exploratory set")
    order = _condition_order(args.condition_order)
    output_root = args.output_root.expanduser().resolve()
    if output_root.exists() or output_root.is_symlink():
        raise BenchmarkError("matched output root must not already exist")
    output_root.mkdir(parents=True, mode=0o700)

    deployment = load_deployment(args.deployment)
    specs = {
        condition: condition_spec(
            condition, deployment=deployment, mathlib_atlas=args.mathlib_atlas
        )
        for condition in CONDITIONS
    }
    packet_path = ROOT / "packets" / f"{task_id}.json"
    if not packet_path.is_file() or packet_path.is_symlink():
        raise BenchmarkError("source packet is missing or unsafe")
    packet = load_json(packet_path)
    if packet.get("task_id") != task_id:
        raise BenchmarkError("source packet task ID does not match request")
    contract_additions, contract_sha256 = _contract_additions(task_id)
    paper = deployment.pdf_root / str(packet["paper_pdf"]["path_basename"])
    if (
        not paper.is_file()
        or paper.is_symlink()
        or sha256_file(paper) != packet["paper_pdf"]["sha256"]
    ):
        raise BenchmarkError("source PDF does not match the frozen packet")

    prompt = _prompt_bytes(statement_only=bool(args.statement_only))
    write_bytes_atomic(output_root / "prompt.txt", prompt, mode=0o400)
    pair_report: dict[str, Any] = {
        "schema_version": "formalization-design17-matched-pair-2",
        "scientific_status": SCIENTIFIC_STATUS,
        "benchmark_object": (
            "FORMALIZED_STATEMENT_ONLY"
            if args.statement_only
            else "FORMALIZED_STATEMENT_AND_COMPLETE_PROOF"
        ),
        "source_contract": (
            "statement-only-single-target-sorry"
            if args.statement_only
            else "complete-kernel-checked-proof"
        ),
        "faithfulness_status": "NOT_AUDITED",
        "pair_status": "RUNNING",
        "task_id": task_id,
        "condition_order": list(order),
        "conditions_run_sequentially": True,
        "prompt_sha256": sha256_file(output_root / "prompt.txt"),
        "source_packet_sha256": sha256_file(packet_path),
        "source_pdf_sha256": sha256_file(paper),
        "contract_overlay_sha256": contract_sha256,
        "root_limit": int(args.root_limit),
        "dependency_limit": int(args.dependency_limit),
        "maximum_packet_bytes": int(args.maximum_packet_bytes),
        "created_at_utc": utc_now(),
        "condition_reports": {},
        "output_root": str(output_root),
    }
    _write_pair_report(output_root, pair_report)
    try:
        for condition in order:
            report = _run_condition(
                args=args,
                deployment=deployment,
                spec=specs[condition],
                packet_path=packet_path,
                packet=packet,
                contract_additions=contract_additions,
                paper=paper,
                prompt=prompt,
                output_root=output_root,
            )
            pair_report["condition_reports"][condition] = report
            _write_pair_report(output_root, pair_report)
    except Exception as error:
        pair_report["pair_status"] = "PAIR_INCIDENT"
        pair_report["incident"] = {
            "error_type": type(error).__name__,
            "message": str(error),
            "recorded_at_utc": utc_now(),
        }
        _write_pair_report(output_root, pair_report)
        raise

    r0 = pair_report["condition_reports"]["R0"]
    r1 = pair_report["condition_reports"]["R1"]
    if args.statement_only:
        pair_status, faithfulness_status = _statement_pair_status(
            r0["result_status"], r1["result_status"]
        )
        pair_report["pair_status"] = pair_status
        pair_report["faithfulness_status"] = faithfulness_status
    else:
        pair_report["pair_status"] = "FORMALIZATION_FROZEN_PENDING_AUDIT"
    effect_eligible = (
        not args.statement_only
        or pair_report["pair_status"] == "AUDITED_FAITHFUL_PAIR"
    )
    def comparison_ratio(field: str) -> float | None:
        return _ratio(r1[field], r0[field]) if effect_eligible else None

    pair_report["comparison"] = {
        "effect_analysis_eligible": effect_eligible,
        "r1_over_r0_contestant_system_wall": comparison_ratio(
            "contestant_system_wall_seconds"
        ),
        "r1_over_r0_contestant_active": comparison_ratio(
            "contestant_active_seconds"
        ),
        "r1_over_r0_formalizer_wall": comparison_ratio(
            "formalizer_wall_seconds"
        ),
        "r1_over_r0_net_new_tokens": comparison_ratio("net_new_tokens"),
        "r1_over_r0_candidate_lines": comparison_ratio("candidate_lines"),
        "r1_over_r0_submission_count": (
            comparison_ratio("submission_count") if args.statement_only else None
        ),
        "interpretation": (
            "audited faithful paired comparison"
            if args.statement_only and effect_eligible
            else "no effect ratio: one or both statement conditions were not faithful"
            if args.statement_only
            else "engineering comparison only; independent faithfulness audit required"
        ),
    }
    pair_report["completed_at_utc"] = utc_now()
    _write_pair_report(output_root, pair_report)
    return pair_report


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--deployment", type=Path, required=True)
    parser.add_argument("--mathlib-atlas", type=Path, required=True)
    parser.add_argument("--task-id", required=True)
    parser.add_argument("--condition-order", required=True, help="R0,R1 or R1,R0")
    parser.add_argument("--output-root", type=Path, required=True)
    parser.add_argument("--model", default="gpt-5.6-sol")
    parser.add_argument("--reasoning-effort", default="xhigh")
    parser.add_argument("--time-limit-seconds", type=int, default=18000)
    parser.add_argument("--validation-timeout-seconds", type=int, default=600)
    parser.add_argument("--root-limit", type=int, default=3)
    parser.add_argument("--dependency-limit", type=int, default=5)
    parser.add_argument("--maximum-packet-bytes", type=int, default=48 * 1024)
    parser.add_argument("--submission-limit", type=int, default=4)
    parser.add_argument("--audit-model", default="gpt-6-astra")
    parser.add_argument("--audit-reasoning-effort", default="high")
    parser.add_argument("--audit-timeout-seconds", type=float, default=7200)
    parser.add_argument("--audit-infrastructure-retries", type=int, default=2)
    parser.add_argument(
        "--require-titan-envelope",
        action="store_true",
        help="fail closed unless the exact 8-CPU/32-GiB/no-swap envelope is active",
    )
    parser.add_argument(
        "--statement-only",
        action="store_true",
        help="measure only statement formalization; require one final target sorry",
    )
    return parser


def main() -> int:
    result = run(make_parser().parse_args())
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (BenchmarkError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"Design-16 matched error: {error}", file=sys.stderr)
        raise SystemExit(2)
