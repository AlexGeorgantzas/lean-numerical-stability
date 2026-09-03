#!/usr/bin/env python3
"""Validate the source-presentation tags assigned to HighamBench tasks."""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys
from typing import Any, Mapping, Sequence

try:
    from .common import BenchmarkToolError, read_json
except ImportError:  # Direct script execution.
    from common import BenchmarkToolError, read_json  # type: ignore


ALLOWED_SOURCE_TAGS = ("THM", "LEM", "PROP", "COR", "EQN", "TXT", "UNL")
TASK_SCHEMA_VERSION = "highambench-task-0.3"
T4_TASK_SCHEMA_VERSION = "highambench-task-0.4"
NAMED_SOURCE_TAGS = {
    "THM": "Theorem",
    "LEM": "Lemma",
    "PROP": "Proposition",
    "COR": "Corollary",
}
T4_SOURCE_KINDS = (
    "named_result",
    "numbered_equation",
    "precise_unnumbered_claim",
    "algorithm",
    "symbolic_example",
    "problem",
    "definition",
    "conjecture",
    "question",
    "heuristic",
    "empirical_claim",
)
T4_DECLARATION_KINDS = (
    "theorem",
    "lemma",
    "definition",
    "abbrev",
    "structure",
    "inductive",
)
T4_RESULT_FORM_TAGS = ("BND", "EQ", "CMP", "EX")
T4_INVENTORY_DISPOSITIONS = ("included", "excluded")
T4_PASSING_REVIEW_TAGS = ("faithful-equivalent", "faithful-stronger")
T4_REVIEW_STATUSES = ("pending", "accepted")
T4_REVIEW_CAMPAIGN_STATUSES = (
    "not_started",
    "in_progress",
    "replacement_required",
    "accepted",
)
T4_CONSTRUCTION_INPUT_KEYS = frozenset(
    (
        "paper_definitions_sha256",
        "source_inventory_sha256",
        "target_sha256",
        "review_campaign_status",
    )
)
T4_SOURCE_INVENTORY_SCHEMA_VERSION = "highambench-t4-source-inventory-0.3"
T4_DECLARATION_MAPPING_ROLES = (
    "primary_carrier",
    "semantic_context",
    "duplicate_anchor",
)

_STABLE_ID_RE = re.compile(r"^[A-Za-z0-9][A-Za-z0-9_.:-]*$")
_LEAN_NAME_RE = re.compile(
    r"^[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)+$"
)
_SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
_PROOF_DECLARATION_KINDS = frozenset(("theorem", "lemma"))
_T4_FORBIDDEN_AGGREGATE_FIELDS = (
    "source_tags",
    "author_label",
    "source_locations",
    "result_form_tag",
    "formal_statement",
)


def _label(task: Mapping[str, Any], fallback: str) -> str:
    task_id = task.get("task_id")
    return task_id if isinstance(task_id, str) and task_id else fallback


def _require_mapping(value: Any, label: str) -> Mapping[str, Any]:
    if not isinstance(value, Mapping):
        raise BenchmarkToolError(f"{label} must be an object")
    return value


def _require_list(value: Any, label: str, *, nonempty: bool = False) -> list[Any]:
    if not isinstance(value, list) or (nonempty and not value):
        qualifier = "nonempty " if nonempty else ""
        raise BenchmarkToolError(f"{label} must be a {qualifier}list")
    return value


def _require_string(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise BenchmarkToolError(f"{label} must be a nonempty string")
    return value


def _require_stable_id(value: Any, label: str) -> str:
    identifier = _require_string(value, label)
    if _STABLE_ID_RE.fullmatch(identifier) is None:
        raise BenchmarkToolError(f"{label} must be a stable identifier")
    return identifier


def _require_lean_name(value: Any, label: str) -> str:
    name = _require_string(value, label)
    if _LEAN_NAME_RE.fullmatch(name) is None:
        raise BenchmarkToolError(f"{label} must be a fully qualified Lean name")
    return name


def _require_positive_int(value: Any, label: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 1:
        raise BenchmarkToolError(f"{label} must be a positive integer")
    return value


def _require_sha256(value: Any, label: str) -> str:
    digest = _require_string(value, label)
    if _SHA256_RE.fullmatch(digest) is None:
        raise BenchmarkToolError(f"{label} must be a lowercase SHA-256 digest")
    return digest


def _sha256_file(path: Path, label: str) -> str:
    if path.is_symlink() or not path.is_file():
        raise BenchmarkToolError(f"{label} must be a regular file: {path}")
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _validate_source_tag_fields(
    record: Mapping[str, Any], *, label: str
) -> tuple[list[str], str | None]:
    raw_tags = record.get("source_tags")
    if not isinstance(raw_tags, list) or not raw_tags:
        raise BenchmarkToolError(f"{label} source_tags must be a nonempty list")
    if any(not isinstance(tag, str) or not tag for tag in raw_tags):
        raise BenchmarkToolError(f"{label} source_tags must contain strings")
    tags = list(raw_tags)
    unknown = [tag for tag in tags if tag not in ALLOWED_SOURCE_TAGS]
    if unknown:
        raise BenchmarkToolError(f"{label} has unknown source tags: {', '.join(unknown)}")
    if len(set(tags)) != len(tags):
        raise BenchmarkToolError(f"{label} repeats a source tag")
    expected_order = sorted(tags, key=ALLOWED_SOURCE_TAGS.index)
    if tags != expected_order:
        raise BenchmarkToolError(
            f"{label} source_tags must use canonical order: {expected_order}"
        )

    named = [tag for tag in tags if tag in NAMED_SOURCE_TAGS]
    author_label = record.get("author_label")
    if named:
        if len(named) != 1 or len(tags) != 1:
            raise BenchmarkToolError(f"{label} must use exactly one named source tag")
        if not isinstance(author_label, str) or not author_label.strip():
            raise BenchmarkToolError(
                f"{label} {named[0]} tag requires an exact author_label"
            )
        printed_kind = NAMED_SOURCE_TAGS[named[0]]
        if (
            re.match(
                rf"^{re.escape(printed_kind)}(?:\s|$)",
                author_label,
                flags=re.IGNORECASE,
            )
            is None
        ):
            raise BenchmarkToolError(
                f"{label} author_label must begin with {printed_kind!r}"
            )
    elif author_label is not None:
        raise BenchmarkToolError(
            f"{label} author_label must be null for non-named source tags"
        )
    if "EQN" in tags and "UNL" in tags:
        raise BenchmarkToolError(
            f"{label} cannot be both a numbered equation and an unnumbered display"
        )
    return tags, author_label


def _validate_review_verdict(value: Any, label: str) -> dict[str, Any]:
    verdict = _require_mapping(value, label)
    score = verdict.get("score")
    if isinstance(score, bool) or not isinstance(score, int) or not 0 <= score <= 4:
        raise BenchmarkToolError(f"{label}.score must be an integer from 0 to 4")
    tag = _require_string(verdict.get("tag"), f"{label}.tag")
    passed = verdict.get("passed")
    if not isinstance(passed, bool):
        raise BenchmarkToolError(f"{label}.passed must be a boolean")
    if score == 4 and tag != "faithful-stronger":
        raise BenchmarkToolError(
            f"{label} score 4 is reserved for faithful-stronger"
        )
    if score == 3 and tag != "faithful-equivalent":
        raise BenchmarkToolError(
            f"{label} score 3 is reserved for faithful-equivalent"
        )
    if score < 3 and tag in T4_PASSING_REVIEW_TAGS:
        raise BenchmarkToolError(f"{label} a passing tag requires score 3 or 4")
    expected_passed = (score, tag) in (
        (3, "faithful-equivalent"),
        (4, "faithful-stronger"),
    )
    if passed != expected_passed:
        raise BenchmarkToolError(
            f"{label}.passed must equal the score-and-tag acceptance rule"
        )
    _require_string(verdict.get("evidence"), f"{label}.evidence")
    raw_discrepancies = _require_list(
        verdict.get("discrepancies"), f"{label}.discrepancies"
    )
    for index, discrepancy in enumerate(raw_discrepancies):
        _require_string(discrepancy, f"{label}.discrepancies[{index}]")
    # Deliberately return only the controlling semantic fields.  Evidence is
    # mandatory but need not be textually identical between a judge,
    # adjudicator, and the normalized final verdict.
    return {"score": score, "tag": tag, "passed": passed}


def _validate_role_execution(value: Any, label: str) -> dict[str, str]:
    execution = _require_mapping(value, label)
    agent_id = _require_stable_id(execution.get("agent_id"), f"{label}.agent_id")
    model_identifier = _require_string(
        execution.get("model_identifier"), f"{label}.model_identifier"
    )
    return {"agent_id": agent_id, "model_identifier": model_identifier}


def validate_t4_task_metadata(
    task: Mapping[str, Any], *, label: str = "task"
) -> dict[str, Any]:
    """Validate one multi-declaration Tier-4 task record."""

    task_label = _label(task, label)
    if task.get("schema_version") != T4_TASK_SCHEMA_VERSION:
        raise BenchmarkToolError(
            f"{task_label} schema_version must be {T4_TASK_SCHEMA_VERSION!r} for T4"
        )
    task_id = _require_string(task.get("task_id"), f"{task_label}.task_id")
    if re.fullmatch(r"P[0-9]+-T4", task_id) is None:
        raise BenchmarkToolError(f"{task_label}.task_id must have form P<digits>-T4")
    paper_id = _require_string(task.get("paper_id"), f"{task_label}.paper_id")
    if paper_id != task_id.removesuffix("-T4"):
        raise BenchmarkToolError(f"{task_label}.paper_id must agree with task_id")
    controlled_target_file = (
        f"paper_bencmark/highambench/tasks/{paper_id}/T4/Target.lean"
    )
    allowed_controlled_source_files = {
        (
            "paper_bencmark/highambench/shared/HighamBench/"
            f"{paper_id}Definitions.lean"
        ),
        controlled_target_file,
    }
    if task.get("tier") != "T4":
        raise BenchmarkToolError(f"{task_label}.tier must be 'T4'")
    for field in _T4_FORBIDDEN_AGGREGATE_FIELDS:
        if field in task:
            raise BenchmarkToolError(
                f"{task_label}.{field} is invalid aggregate metadata for T4"
            )
    measurement_ready = task.get("classification_frozen_before_runs")
    if not isinstance(measurement_ready, bool):
        raise BenchmarkToolError(
            f"{task_label} classification_frozen_before_runs must be a boolean"
        )

    expected_context_file = (
        f"paper_bencmark/highambench/tasks/{paper_id}/T4/context.md"
    )
    if task.get("context_file") != expected_context_file:
        raise BenchmarkToolError(
            f"{task_label}.context_file must be {expected_context_file!r}"
        )
    expected_source_inventory_file = (
        f"paper_bencmark/highambench/tasks/{paper_id}/T4/source_inventory.json"
    )
    if task.get("source_inventory_file") != expected_source_inventory_file:
        raise BenchmarkToolError(
            f"{task_label}.source_inventory_file must be "
            f"{expected_source_inventory_file!r}"
        )
    limits = _require_mapping(task.get("limits"), f"{task_label}.limits")
    _require_positive_int(
        limits.get("total_model_tokens"),
        f"{task_label}.limits.total_model_tokens",
    )
    _require_positive_int(
        limits.get("wall_clock_seconds"),
        f"{task_label}.limits.wall_clock_seconds",
    )
    paper_source = _require_mapping(
        task.get("paper_source"), f"{task_label}.paper_source"
    )
    _require_string(
        paper_source.get("local_path"), f"{task_label}.paper_source.local_path"
    )
    _require_sha256(
        paper_source.get("sha256"), f"{task_label}.paper_source.sha256"
    )
    construction_inputs = _require_mapping(
        task.get("construction_inputs"), f"{task_label}.construction_inputs"
    )
    if set(construction_inputs) != T4_CONSTRUCTION_INPUT_KEYS:
        raise BenchmarkToolError(
            f"{task_label}.construction_inputs must contain exactly the "
            "paper-neutral definitions, inventory, target, and campaign bindings"
        )
    for field in (
        "paper_definitions_sha256",
        "source_inventory_sha256",
        "target_sha256",
    ):
        _require_sha256(
            construction_inputs.get(field),
            f"{task_label}.construction_inputs.{field}",
        )
    review_campaign_status = construction_inputs.get("review_campaign_status")
    if review_campaign_status not in T4_REVIEW_CAMPAIGN_STATUSES:
        raise BenchmarkToolError(
            f"{task_label}.construction_inputs.review_campaign_status must be one "
            f"of {T4_REVIEW_CAMPAIGN_STATUSES}"
        )

    raw_inventory = _require_list(
        task.get("source_inventory"), f"{task_label}.source_inventory", nonempty=True
    )
    inventory_ids: list[str] = []
    inventory_carrier_declarations: dict[str, list[str]] = {}
    inventory_mapped_declarations: dict[str, list[str]] = {}
    inventory_dispositions: dict[str, str] = {}
    for index, raw_item in enumerate(raw_inventory, start=1):
        item_label = f"{task_label}.source_inventory[{index - 1}]"
        item = _require_mapping(raw_item, item_label)
        if item.get("source_order") != index:
            raise BenchmarkToolError(f"{item_label}.source_order must be {index}")
        inventory_id = _require_stable_id(
            item.get("inventory_id"), f"{item_label}.inventory_id"
        )
        if inventory_id in inventory_ids:
            raise BenchmarkToolError(f"{task_label} repeats inventory_id {inventory_id!r}")
        inventory_ids.append(inventory_id)
        source_kind = item.get("source_kind")
        if source_kind not in T4_SOURCE_KINDS:
            raise BenchmarkToolError(
                f"{item_label}.source_kind must be one of {T4_SOURCE_KINDS}"
            )
        _require_string(item.get("scope"), f"{item_label}.scope")
        assumptions = _require_list(
            item.get("assumptions"), f"{item_label}.assumptions"
        )
        for assumption_index, assumption in enumerate(assumptions):
            _require_string(
                assumption, f"{item_label}.assumptions[{assumption_index}]"
            )
        _require_string(item.get("source_status"), f"{item_label}.source_status")
        issue_notes = _require_list(
            item.get("source_issue_notes"), f"{item_label}.source_issue_notes"
        )
        for note_index, note in enumerate(issue_notes):
            _require_string(note, f"{item_label}.source_issue_notes[{note_index}]")
        if item.get("source_tags") == []:
            if item.get("disposition") != "excluded" or item.get("author_label") is not None:
                raise BenchmarkToolError(
                    f"{item_label} may omit source tags only for an excluded nonclaim"
                )
            item_tags: list[str] = []
        else:
            item_tags, _ = _validate_source_tag_fields(item, label=item_label)
        if source_kind == "named_result" and not any(
            tag in NAMED_SOURCE_TAGS for tag in item_tags
        ):
            raise BenchmarkToolError(
                f"{item_label} named_result requires a named source tag"
            )
        if source_kind != "named_result" and any(
            tag in NAMED_SOURCE_TAGS for tag in item_tags
        ):
            raise BenchmarkToolError(
                f"{item_label} named source tag requires source_kind 'named_result'"
            )
        if source_kind == "numbered_equation" and "EQN" not in item_tags:
            raise BenchmarkToolError(
                f"{item_label} numbered_equation requires the EQN tag"
            )
        raw_locations = _require_list(
            item.get("source_locations"),
            f"{item_label}.source_locations",
            nonempty=True,
        )
        for location_index, raw_location in enumerate(raw_locations):
            location_label = f"{item_label}.source_locations[{location_index}]"
            location = _require_mapping(raw_location, location_label)
            _require_positive_int(location.get("pdf_page"), f"{location_label}.pdf_page")
            if "printed_page" in location and location.get("printed_page") is not None:
                _require_positive_int(
                    location.get("printed_page"), f"{location_label}.printed_page"
                )
            _require_string(location.get("section"), f"{location_label}.section")
            _require_string(location.get("anchor"), f"{location_label}.anchor")
        disposition = item.get("disposition")
        if disposition not in T4_INVENTORY_DISPOSITIONS:
            raise BenchmarkToolError(
                f"{item_label}.disposition must be one of {T4_INVENTORY_DISPOSITIONS}"
            )
        raw_declaration_ids = _require_list(
            item.get("declaration_ids"), f"{item_label}.declaration_ids"
        )
        declaration_ids_for_item = [
            _require_stable_id(value, f"{item_label}.declaration_ids[{position}]")
            for position, value in enumerate(raw_declaration_ids)
        ]
        if len(set(declaration_ids_for_item)) != len(declaration_ids_for_item):
            raise BenchmarkToolError(f"{item_label}.declaration_ids must be unique")
        raw_mappings = _require_list(
            item.get("declaration_mappings"),
            f"{item_label}.declaration_mappings",
        )
        mapped_declaration_ids: list[str] = []
        carrier_declaration_ids: list[str] = []
        for mapping_index, raw_mapping in enumerate(raw_mappings):
            mapping_label = (
                f"{item_label}.declaration_mappings[{mapping_index}]"
            )
            mapping = _require_mapping(raw_mapping, mapping_label)
            mapped_declaration_id = _require_stable_id(
                mapping.get("declaration_id"),
                f"{mapping_label}.declaration_id",
            )
            if mapped_declaration_id in mapped_declaration_ids:
                raise BenchmarkToolError(
                    f"{item_label}.declaration_mappings repeats declaration "
                    f"{mapped_declaration_id!r}"
                )
            mapped_declaration_ids.append(mapped_declaration_id)
            role = mapping.get("role")
            if role not in T4_DECLARATION_MAPPING_ROLES:
                raise BenchmarkToolError(
                    f"{mapping_label}.role must be one of "
                    f"{T4_DECLARATION_MAPPING_ROLES}"
                )
            _require_string(mapping.get("notes"), f"{mapping_label}.notes")
            if role in ("primary_carrier", "duplicate_anchor"):
                carrier_declaration_ids.append(mapped_declaration_id)
        if declaration_ids_for_item != carrier_declaration_ids:
            raise BenchmarkToolError(
                f"{item_label}.declaration_ids must equal its ordered "
                "primary-carrier and duplicate-anchor mappings"
            )
        exclusion_reason = item.get("exclusion_reason")
        if disposition == "included":
            if not declaration_ids_for_item:
                raise BenchmarkToolError(
                    f"{item_label} included source must map to a declaration"
                )
            if exclusion_reason is not None:
                raise BenchmarkToolError(
                    f"{item_label}.exclusion_reason must be null when included"
                )
        else:
            if declaration_ids_for_item:
                raise BenchmarkToolError(
                    f"{item_label} excluded source cannot map to a declaration"
                )
            if mapped_declaration_ids:
                raise BenchmarkToolError(
                    f"{item_label} excluded source cannot have declaration_mappings"
                )
            _require_string(exclusion_reason, f"{item_label}.exclusion_reason")
        inventory_carrier_declarations[inventory_id] = declaration_ids_for_item
        inventory_mapped_declarations[inventory_id] = mapped_declaration_ids
        inventory_dispositions[inventory_id] = disposition

    raw_declarations = _require_list(
        task.get("declarations"), f"{task_label}.declarations", nonempty=True
    )
    declaration_ids: list[str] = []
    lean_names: list[str] = []
    declaration_sources: dict[str, list[str]] = {}
    declaration_placeholders: dict[str, str | None] = {}
    declaration_kinds: dict[str, str] = {}
    controlled_source_positions: set[tuple[str, int]] = set()
    for index, raw_declaration in enumerate(raw_declarations, start=1):
        declaration_label = f"{task_label}.declarations[{index - 1}]"
        declaration = _require_mapping(raw_declaration, declaration_label)
        if declaration.get("declaration_order") != index:
            raise BenchmarkToolError(f"{declaration_label}.declaration_order must be {index}")
        declaration_id = _require_stable_id(
            declaration.get("declaration_id"), f"{declaration_label}.declaration_id"
        )
        if declaration_id in declaration_ids:
            raise BenchmarkToolError(
                f"{task_label} repeats declaration_id {declaration_id!r}"
            )
        declaration_ids.append(declaration_id)
        lean_name = _require_lean_name(
            declaration.get("lean_name"), f"{declaration_label}.lean_name"
        )
        if lean_name in lean_names:
            raise BenchmarkToolError(f"{task_label} repeats lean_name {lean_name!r}")
        lean_names.append(lean_name)
        declaration_kind = declaration.get("declaration_kind")
        if declaration_kind not in T4_DECLARATION_KINDS:
            raise BenchmarkToolError(
                f"{declaration_label}.declaration_kind must be one of "
                f"{T4_DECLARATION_KINDS}"
            )
        controlled_source_file = _require_string(
            declaration.get("controlled_source_file"),
            f"{declaration_label}.controlled_source_file",
        )
        controlled_source_path = PurePosixPath(controlled_source_file)
        if (
            controlled_source_path.is_absolute()
            or controlled_source_path.as_posix() != controlled_source_file
            or any(part in ("", ".", "..") for part in controlled_source_path.parts)
            or controlled_source_file not in allowed_controlled_source_files
        ):
            raise BenchmarkToolError(
                f"{declaration_label}.controlled_source_file is outside the "
                f"controlled {paper_id} semantic surface"
            )
        if (
            declaration_kind in _PROOF_DECLARATION_KINDS
            and controlled_source_file != controlled_target_file
        ):
            raise BenchmarkToolError(
                f"{declaration_label} proof declaration must be owned by "
                f"{controlled_target_file}"
            )
        controlled_source_line = _require_positive_int(
            declaration.get("controlled_source_line"),
            f"{declaration_label}.controlled_source_line",
        )
        controlled_source_position = (
            controlled_source_file,
            controlled_source_line,
        )
        if controlled_source_position in controlled_source_positions:
            raise BenchmarkToolError(
                f"{task_label} repeats controlled declaration source position "
                f"{controlled_source_position!r}"
            )
        controlled_source_positions.add(controlled_source_position)
        source_kind = declaration.get("source_kind")
        if source_kind not in T4_SOURCE_KINDS:
            raise BenchmarkToolError(
                f"{declaration_label}.source_kind must be one of {T4_SOURCE_KINDS}"
            )
        tags, _ = _validate_source_tag_fields(declaration, label=declaration_label)
        if source_kind == "named_result" and not any(
            tag in NAMED_SOURCE_TAGS for tag in tags
        ):
            raise BenchmarkToolError(
                f"{declaration_label} named_result requires a named source tag"
            )
        if source_kind != "named_result" and any(
            tag in NAMED_SOURCE_TAGS for tag in tags
        ):
            raise BenchmarkToolError(
                f"{declaration_label} named source tag requires source_kind 'named_result'"
            )
        if source_kind == "numbered_equation" and "EQN" not in tags:
            raise BenchmarkToolError(
                f"{declaration_label} numbered_equation requires the EQN tag"
            )
        result_form_tag = declaration.get("result_form_tag")
        if result_form_tag is not None and result_form_tag not in T4_RESULT_FORM_TAGS:
            raise BenchmarkToolError(
                f"{declaration_label}.result_form_tag must be null or one of "
                f"{T4_RESULT_FORM_TAGS}"
            )
        raw_source_item_ids = _require_list(
            declaration.get("source_item_ids"),
            f"{declaration_label}.source_item_ids",
            nonempty=True,
        )
        source_item_ids = [
            _require_stable_id(value, f"{declaration_label}.source_item_ids[{position}]")
            for position, value in enumerate(raw_source_item_ids)
        ]
        if len(set(source_item_ids)) != len(source_item_ids):
            raise BenchmarkToolError(f"{declaration_label}.source_item_ids must be unique")
        raw_dependency_hashes = _require_list(
            declaration.get("semantic_dependency_hashes"),
            f"{declaration_label}.semantic_dependency_hashes",
        )
        dependency_names: set[str] = set()
        for dependency_index, raw_dependency in enumerate(raw_dependency_hashes):
            dependency_label = (
                f"{declaration_label}.semantic_dependency_hashes[{dependency_index}]"
            )
            dependency = _require_mapping(raw_dependency, dependency_label)
            dependency_name = _require_lean_name(
                dependency.get("declaration"), f"{dependency_label}.declaration"
            )
            if dependency_name in dependency_names:
                raise BenchmarkToolError(
                    f"{declaration_label} repeats semantic dependency {dependency_name!r}"
                )
            dependency_names.add(dependency_name)
            _require_sha256(dependency.get("sha256"), f"{dependency_label}.sha256")
        placeholder_id = declaration.get("placeholder_id")
        if declaration_kind in _PROOF_DECLARATION_KINDS:
            placeholder_id = _require_stable_id(
                placeholder_id, f"{declaration_label}.placeholder_id"
            )
        elif placeholder_id is not None:
            raise BenchmarkToolError(
                f"{declaration_label}.placeholder_id must be null for a definition"
            )
        for review_field in ("review_id", "review_status", "review_unit_id"):
            if review_field in declaration:
                raise BenchmarkToolError(
                    f"{declaration_label}.{review_field} belongs in review_units"
                )
        declaration_sources[declaration_id] = source_item_ids
        declaration_placeholders[declaration_id] = placeholder_id
        declaration_kinds[declaration_id] = declaration_kind

    known_inventory_ids = set(inventory_ids)
    known_declaration_ids = set(declaration_ids)
    for inventory_id, mapped_declarations in inventory_mapped_declarations.items():
        for declaration_id in mapped_declarations:
            if declaration_id not in known_declaration_ids:
                raise BenchmarkToolError(
                    f"{task_label} inventory {inventory_id!r} maps unknown declaration "
                    f"{declaration_id!r}"
                )
            if inventory_id not in declaration_sources[declaration_id]:
                raise BenchmarkToolError(
                    f"{task_label} mapping {inventory_id!r} -> {declaration_id!r} "
                    "is not bidirectional"
                )
    for declaration_id, mapped_inventory in declaration_sources.items():
        for inventory_id in mapped_inventory:
            if inventory_id not in known_inventory_ids:
                raise BenchmarkToolError(
                    f"{task_label} declaration {declaration_id!r} maps unknown inventory "
                    f"{inventory_id!r}"
                )
            if inventory_dispositions[inventory_id] != "included":
                raise BenchmarkToolError(
                    f"{task_label} declaration {declaration_id!r} maps excluded inventory "
                    f"{inventory_id!r}"
                )
            if declaration_id not in inventory_mapped_declarations[inventory_id]:
                raise BenchmarkToolError(
                    f"{task_label} mapping {declaration_id!r} -> {inventory_id!r} "
                    "is not bidirectional"
                )

    raw_review_units = _require_list(
        task.get("review_units"), f"{task_label}.review_units", nonempty=True
    )
    review_unit_ids: list[str] = []
    review_unit_source_items: dict[str, list[str]] = {}
    review_unit_declarations: dict[str, list[str]] = {}
    review_unit_reused_declarations: dict[str, list[str]] = {}
    review_unit_labels: dict[str, str] = {}
    review_unit_review_ids: dict[str, str] = {}
    review_unit_statuses: dict[str, str] = {}
    source_review_units: dict[str, str] = {}
    declaration_review_units: dict[str, list[str]] = {
        declaration_id: [] for declaration_id in declaration_ids
    }
    review_unit_signatures: dict[
        tuple[frozenset[str], frozenset[str]], str
    ] = {}
    review_ids: set[str] = set()
    inventory_order_by_id = {
        inventory_id: index for index, inventory_id in enumerate(inventory_ids)
    }
    declaration_order_by_id = {
        declaration_id: index
        for index, declaration_id in enumerate(declaration_ids)
    }
    previous_earliest_source_order: int | None = None
    for index, raw_unit in enumerate(raw_review_units, start=1):
        unit_label = f"{task_label}.review_units[{index - 1}]"
        unit = _require_mapping(raw_unit, unit_label)
        if unit.get("review_unit_order") != index:
            raise BenchmarkToolError(
                f"{unit_label}.review_unit_order must be {index}"
            )
        review_unit_id = _require_stable_id(
            unit.get("review_unit_id"), f"{unit_label}.review_unit_id"
        )
        if review_unit_id in review_unit_ids:
            raise BenchmarkToolError(
                f"{task_label} repeats review_unit_id {review_unit_id!r}"
            )
        review_unit_ids.append(review_unit_id)

        raw_unit_source_item_ids = _require_list(
            unit.get("source_item_ids"),
            f"{unit_label}.source_item_ids",
            nonempty=True,
        )
        unit_source_item_ids = [
            _require_stable_id(value, f"{unit_label}.source_item_ids[{position}]")
            for position, value in enumerate(raw_unit_source_item_ids)
        ]
        if len(set(unit_source_item_ids)) != len(unit_source_item_ids):
            raise BenchmarkToolError(f"{unit_label}.source_item_ids must be unique")
        unknown_source_item_ids = [
            source_item_id
            for source_item_id in unit_source_item_ids
            if source_item_id not in known_inventory_ids
        ]
        if unknown_source_item_ids:
            raise BenchmarkToolError(
                f"{unit_label} maps unknown source items {unknown_source_item_ids!r}"
            )
        excluded_source_item_ids = [
            source_item_id
            for source_item_id in unit_source_item_ids
            if inventory_dispositions[source_item_id] == "excluded"
        ]
        if excluded_source_item_ids:
            raise BenchmarkToolError(
                f"{unit_label} maps excluded source items {excluded_source_item_ids!r}"
            )
        source_positions = [
            inventory_order_by_id[source_item_id]
            for source_item_id in unit_source_item_ids
        ]
        if source_positions != sorted(source_positions):
            raise BenchmarkToolError(
                f"{unit_label}.source_item_ids must follow source_order"
            )
        earliest_source_order = source_positions[0]
        _require_string(
            unit.get("smallest_group_reason"),
            f"{unit_label}.smallest_group_reason",
        )

        raw_unit_declaration_ids = _require_list(
            unit.get("declaration_ids"),
            f"{unit_label}.declaration_ids",
            nonempty=True,
        )
        unit_declaration_ids = [
            _require_stable_id(value, f"{unit_label}.declaration_ids[{position}]")
            for position, value in enumerate(raw_unit_declaration_ids)
        ]
        if len(set(unit_declaration_ids)) != len(unit_declaration_ids):
            raise BenchmarkToolError(f"{unit_label}.declaration_ids must be unique")
        unknown_declaration_ids = [
            declaration_id
            for declaration_id in unit_declaration_ids
            if declaration_id not in known_declaration_ids
        ]
        if unknown_declaration_ids:
            raise BenchmarkToolError(
                f"{unit_label} maps unknown declarations {unknown_declaration_ids!r}"
            )
        declaration_positions = [
            declaration_order_by_id[declaration_id]
            for declaration_id in unit_declaration_ids
        ]
        if declaration_positions != sorted(declaration_positions):
            raise BenchmarkToolError(
                f"{unit_label}.declaration_ids must follow declaration_order"
            )
        mapped_declaration_ids = {
            declaration_id
            for source_item_id in unit_source_item_ids
            for declaration_id in inventory_carrier_declarations[source_item_id]
        }
        expected_unit_declaration_ids = [
            declaration_id
            for declaration_id in declaration_ids
            if declaration_id in mapped_declaration_ids
        ]
        if unit_declaration_ids != expected_unit_declaration_ids:
            raise BenchmarkToolError(
                f"{unit_label}.declaration_ids must be the declaration-order union "
                "mapped by source_item_ids"
            )

        raw_reused_declaration_ids = _require_list(
            unit.get("reused_declaration_ids"),
            f"{unit_label}.reused_declaration_ids",
        )
        reused_declaration_ids = [
            _require_stable_id(
                value, f"{unit_label}.reused_declaration_ids[{position}]"
            )
            for position, value in enumerate(raw_reused_declaration_ids)
        ]
        if len(set(reused_declaration_ids)) != len(reused_declaration_ids):
            raise BenchmarkToolError(
                f"{unit_label}.reused_declaration_ids must be unique"
            )
        unknown_reused_declaration_ids = [
            declaration_id
            for declaration_id in reused_declaration_ids
            if declaration_id not in known_declaration_ids
        ]
        if unknown_reused_declaration_ids:
            raise BenchmarkToolError(
                f"{unit_label}.reused_declaration_ids contains unknown declarations "
                f"{unknown_reused_declaration_ids!r}"
            )
        reused_positions = [
            declaration_order_by_id[declaration_id]
            for declaration_id in reused_declaration_ids
        ]
        if reused_positions != sorted(reused_positions):
            raise BenchmarkToolError(
                f"{unit_label}.reused_declaration_ids must follow declaration_order"
            )

        signature = (
            frozenset(unit_source_item_ids),
            frozenset(unit_declaration_ids),
        )
        duplicate_unit = review_unit_signatures.get(signature)
        if duplicate_unit is not None:
            raise BenchmarkToolError(
                f"{unit_label} duplicates the source-item/declaration sets of "
                f"review unit {duplicate_unit!r}"
            )
        review_unit_signatures[signature] = review_unit_id
        repeated_source_item_ids = [
            source_item_id
            for source_item_id in unit_source_item_ids
            if source_item_id in source_review_units
        ]
        if repeated_source_item_ids:
            raise BenchmarkToolError(
                f"{task_label} source items {repeated_source_item_ids!r} occur in "
                "more than one review unit"
            )
        if (
            previous_earliest_source_order is not None
            and earliest_source_order <= previous_earliest_source_order
        ):
            raise BenchmarkToolError(
                f"{task_label}.review_units must follow the earliest source_order "
                "of each unit"
            )
        previous_earliest_source_order = earliest_source_order
        for source_item_id in unit_source_item_ids:
            source_review_units[source_item_id] = review_unit_id
        for declaration_id in unit_declaration_ids:
            declaration_review_units[declaration_id].append(review_unit_id)

        review_id = _require_stable_id(
            unit.get("review_id"), f"{unit_label}.review_id"
        )
        if review_id in review_ids:
            raise BenchmarkToolError(f"{task_label} repeats review_id {review_id!r}")
        review_ids.add(review_id)
        review_status = unit.get("review_status")
        if review_status not in T4_REVIEW_STATUSES:
            raise BenchmarkToolError(
                f"{unit_label}.review_status must be one of {T4_REVIEW_STATUSES}"
            )
        review_unit_source_items[review_unit_id] = unit_source_item_ids
        review_unit_declarations[review_unit_id] = unit_declaration_ids
        review_unit_reused_declarations[review_unit_id] = reused_declaration_ids
        review_unit_labels[review_unit_id] = unit_label
        review_unit_review_ids[review_unit_id] = review_id
        review_unit_statuses[review_unit_id] = review_status

    missing_source_review_units = [
        inventory_id
        for inventory_id in inventory_ids
        if inventory_dispositions[inventory_id] == "included"
        and inventory_id not in source_review_units
    ]
    if missing_source_review_units:
        raise BenchmarkToolError(
            f"{task_label}.review_units do not cover included source items "
            f"{missing_source_review_units!r}"
        )

    carrier_declaration_ids = {
        declaration_id
        for mapped_declarations in inventory_carrier_declarations.values()
        for declaration_id in mapped_declarations
    }
    missing_declaration_review_units = [
        declaration_id
        for declaration_id in declaration_ids
        if declaration_id in carrier_declaration_ids
        and not declaration_review_units[declaration_id]
    ]
    if missing_declaration_review_units:
        raise BenchmarkToolError(
            f"{task_label}.review_units do not cover declarations "
            f"{missing_declaration_review_units!r}"
        )

    for review_unit_id in review_unit_ids:
        expected_reused_declaration_ids = [
            declaration_id
            for declaration_id in review_unit_declarations[review_unit_id]
            if len(declaration_review_units[declaration_id]) > 1
        ]
        if (
            review_unit_reused_declarations[review_unit_id]
            != expected_reused_declaration_ids
        ):
            unit_label = review_unit_labels[review_unit_id]
            raise BenchmarkToolError(
                f"{unit_label}.reused_declaration_ids must exactly list this unit's "
                "declarations reused by another review unit in declaration_order"
            )

    review_status_set = set(review_unit_statuses.values())
    if len(review_status_set) != 1:
        raise BenchmarkToolError(
            f"{task_label}.review_units must be uniformly pending or accepted"
        )
    review_status = next(iter(review_status_set))
    if measurement_ready and review_status != "accepted":
        raise BenchmarkToolError(
            f"{task_label} cannot freeze classification while reviews are pending"
        )
    if review_status == "accepted" and review_campaign_status != "accepted":
        raise BenchmarkToolError(
            f"{task_label} accepted review units require an accepted review campaign"
        )
    if review_status == "pending" and review_campaign_status == "accepted":
        raise BenchmarkToolError(
            f"{task_label} pending review units cannot claim an accepted campaign"
        )

    validation = _require_mapping(task.get("validation"), f"{task_label}.validation")
    if "required_declaration" in validation:
        raise BenchmarkToolError(
            f"{task_label}.validation.required_declaration is invalid for T4; "
            "use required_declarations"
        )
    recorded_controlled_target = _require_string(
        validation.get("controlled_target_file"),
        f"{task_label}.validation.controlled_target_file",
    )
    if recorded_controlled_target != controlled_target_file:
        raise BenchmarkToolError(
            f"{task_label}.validation.controlled_target_file must be "
            f"{controlled_target_file!r}"
        )
    raw_required = _require_list(
        validation.get("required_declarations"),
        f"{task_label}.validation.required_declarations",
        nonempty=True,
    )
    required_declarations = [
        _require_lean_name(value, f"{task_label}.validation.required_declarations[{index}]")
        for index, value in enumerate(raw_required)
    ]
    if required_declarations != lean_names:
        raise BenchmarkToolError(
            f"{task_label}.validation.required_declarations must exactly match "
            "declarations in declaration_order"
        )
    raw_sorries = _require_list(
        validation.get("controlled_sorries"),
        f"{task_label}.validation.controlled_sorries",
    )
    expected_proof_ids = [
        declaration_id
        for declaration_id in declaration_ids
        if declaration_kinds[declaration_id] in _PROOF_DECLARATION_KINDS
    ]
    if len(raw_sorries) != len(expected_proof_ids):
        raise BenchmarkToolError(
            f"{task_label}.validation.controlled_sorries must contain exactly one "
            "entry per theorem or lemma"
        )
    placeholder_ids: set[str] = set()
    placeholder_locations: set[tuple[int, int]] = set()
    previous_location: tuple[int, int] | None = None
    lean_name_by_id = dict(zip(declaration_ids, lean_names, strict=True))
    for index, (raw_sorry, expected_declaration_id) in enumerate(
        zip(raw_sorries, expected_proof_ids, strict=True), start=1
    ):
        sorry_label = f"{task_label}.validation.controlled_sorries[{index - 1}]"
        sorry = _require_mapping(raw_sorry, sorry_label)
        if sorry.get("placeholder_order") != index:
            raise BenchmarkToolError(f"{sorry_label}.placeholder_order must be {index}")
        declaration_id = _require_stable_id(
            sorry.get("declaration_id"), f"{sorry_label}.declaration_id"
        )
        if declaration_id != expected_declaration_id:
            raise BenchmarkToolError(
                f"{sorry_label}.declaration_id must follow declaration_order"
            )
        placeholder_id = _require_stable_id(
            sorry.get("placeholder_id"), f"{sorry_label}.placeholder_id"
        )
        if placeholder_id != declaration_placeholders[declaration_id]:
            raise BenchmarkToolError(
                f"{sorry_label}.placeholder_id must match its declaration"
            )
        if placeholder_id in placeholder_ids:
            raise BenchmarkToolError(f"{task_label} repeats placeholder_id {placeholder_id!r}")
        placeholder_ids.add(placeholder_id)
        lean_name = _require_lean_name(sorry.get("lean_name"), f"{sorry_label}.lean_name")
        if lean_name != lean_name_by_id[declaration_id]:
            raise BenchmarkToolError(f"{sorry_label}.lean_name must match its declaration")
        expected_marker = f"-- PROOF_START {placeholder_id}"
        if sorry.get("marker") != expected_marker:
            raise BenchmarkToolError(f"{sorry_label}.marker must be {expected_marker!r}")
        line = _require_positive_int(sorry.get("line"), f"{sorry_label}.line")
        column = _require_positive_int(sorry.get("column"), f"{sorry_label}.column")
        location = (line, column)
        if location in placeholder_locations:
            raise BenchmarkToolError(f"{task_label} repeats a controlled sorry location")
        if previous_location is not None and location <= previous_location:
            raise BenchmarkToolError(
                f"{task_label}.validation.controlled_sorries must follow file order"
            )
        placeholder_locations.add(location)
        previous_location = location

    raw_reviews = _require_list(
        task.get("faithfulness_reviews"),
        f"{task_label}.faithfulness_reviews",
    )
    if review_status == "pending" and raw_reviews:
        raise BenchmarkToolError(
            f"{task_label}.faithfulness_reviews must be empty while review units are pending"
        )
    if review_status == "accepted" and len(raw_reviews) != len(review_unit_ids):
        raise BenchmarkToolError(
            f"{task_label}.faithfulness_reviews must contain one review per review unit"
        )
    used_execution_agents: dict[str, str] = {}
    reviewed_unit_ids = review_unit_ids if review_status == "accepted" else []
    for index, (raw_review, review_unit_id) in enumerate(
        zip(raw_reviews, reviewed_unit_ids, strict=True), start=1
    ):
        review_label = f"{task_label}.faithfulness_reviews[{index - 1}]"
        review = _require_mapping(raw_review, review_label)
        if review.get("review_order") != index:
            raise BenchmarkToolError(f"{review_label}.review_order must be {index}")
        review_id = _require_stable_id(review.get("review_id"), f"{review_label}.review_id")
        if review_id != review_unit_review_ids[review_unit_id]:
            raise BenchmarkToolError(f"{review_label}.review_id must match its review unit")
        if review.get("review_unit_id") != review_unit_id:
            raise BenchmarkToolError(
                f"{review_label}.review_unit_id must follow review_unit_order"
            )
        for singular_field in ("source_item_id", "declaration_id", "lean_name"):
            if singular_field in review:
                raise BenchmarkToolError(
                    f"{review_label}.{singular_field} is invalid for a review unit"
                )
        raw_review_source_item_ids = _require_list(
            review.get("source_item_ids"),
            f"{review_label}.source_item_ids",
            nonempty=True,
        )
        review_source_item_ids = [
            _require_stable_id(
                value, f"{review_label}.source_item_ids[{position}]"
            )
            for position, value in enumerate(raw_review_source_item_ids)
        ]
        expected_source_item_ids = review_unit_source_items[review_unit_id]
        if review_source_item_ids != expected_source_item_ids:
            raise BenchmarkToolError(
                f"{review_label}.source_item_ids must match its review unit"
            )
        raw_review_declaration_ids = _require_list(
            review.get("declaration_ids"),
            f"{review_label}.declaration_ids",
            nonempty=True,
        )
        review_declaration_ids = [
            _require_stable_id(
                value, f"{review_label}.declaration_ids[{position}]"
            )
            for position, value in enumerate(raw_review_declaration_ids)
        ]
        expected_declaration_ids = review_unit_declarations[review_unit_id]
        if review_declaration_ids != expected_declaration_ids:
            raise BenchmarkToolError(
                f"{review_label}.declaration_ids must match its review unit"
            )
        raw_review_lean_names = _require_list(
            review.get("lean_names"), f"{review_label}.lean_names", nonempty=True
        )
        review_lean_names = [
            _require_lean_name(value, f"{review_label}.lean_names[{position}]")
            for position, value in enumerate(raw_review_lean_names)
        ]
        expected_lean_names = [
            lean_name_by_id[declaration_id]
            for declaration_id in expected_declaration_ids
        ]
        if review_lean_names != expected_lean_names:
            raise BenchmarkToolError(
                f"{review_label}.lean_names must match its review unit declarations"
            )
        _require_positive_int(review.get("revision"), f"{review_label}.revision")
        if review.get("status") != "accepted":
            raise BenchmarkToolError(f"{review_label}.status must be 'accepted'")
        for hash_field in (
            "source_packet_sha256",
            "lean_packet_sha256",
            "locked_translation_sha256",
            "direct_judge_output_sha256",
            "round_trip_judge_output_sha256",
        ):
            _require_sha256(review.get(hash_field), f"{review_label}.{hash_field}")
        _require_string(
            review.get("role_prompt_version"),
            f"{review_label}.role_prompt_version",
        )
        role_executions = _require_mapping(
            review.get("role_executions"), f"{review_label}.role_executions"
        )
        for role in ("direct_judge", "blind_translator", "round_trip_judge"):
            execution = _validate_role_execution(
                role_executions.get(role),
                f"{review_label}.role_executions.{role}",
            )
            agent_id = execution["agent_id"]
            previous_role = used_execution_agents.get(agent_id)
            if previous_role is not None:
                raise BenchmarkToolError(
                    f"{review_label}.role_executions.{role}.agent_id reuses "
                    f"agent {agent_id!r} from {previous_role}"
                )
            used_execution_agents[agent_id] = (
                f"{review_label}.role_executions.{role}"
            )
        if "adjudicator" not in role_executions:
            raise BenchmarkToolError(
                f"{review_label}.role_executions.adjudicator must be recorded"
            )
        adjudicator_execution_value = role_executions.get("adjudicator")
        fresh = _require_mapping(review.get("fresh_context"), f"{review_label}.fresh_context")
        for role in ("direct_judge", "blind_translator", "round_trip_judge"):
            if fresh.get(role) is not True:
                raise BenchmarkToolError(f"{review_label}.fresh_context.{role} must be true")
        if not isinstance(fresh.get("adjudicator"), bool):
            raise BenchmarkToolError(
                f"{review_label}.fresh_context.adjudicator must be a boolean"
            )
        blindness = _require_mapping(review.get("blindness"), f"{review_label}.blindness")
        for attestation in (
            "direct_judge_received_only_packets",
            "translator_did_not_see_source",
            "round_trip_judge_did_not_see_lean",
            "roles_used_distinct_agents",
        ):
            if blindness.get(attestation) is not True:
                raise BenchmarkToolError(f"{review_label}.blindness.{attestation} must be true")
        direct = _validate_review_verdict(
            review.get("direct_judge"), f"{review_label}.direct_judge"
        )
        round_trip = _validate_review_verdict(
            review.get("round_trip_judge"), f"{review_label}.round_trip_judge"
        )
        final = _validate_review_verdict(
            review.get("final_verdict"), f"{review_label}.final_verdict"
        )
        disagreement = (
            direct["passed"] != round_trip["passed"]
            or direct["tag"] != round_trip["tag"]
        )
        adjudicator_value = review.get("adjudicator")
        adjudicator_hash = review.get("adjudicator_output_sha256")
        if disagreement:
            adjudicator_execution = _validate_role_execution(
                adjudicator_execution_value,
                f"{review_label}.role_executions.adjudicator",
            )
            adjudicator_agent_id = adjudicator_execution["agent_id"]
            previous_role = used_execution_agents.get(adjudicator_agent_id)
            if previous_role is not None:
                raise BenchmarkToolError(
                    f"{review_label}.role_executions.adjudicator.agent_id reuses "
                    f"agent {adjudicator_agent_id!r} from {previous_role}"
                )
            used_execution_agents[adjudicator_agent_id] = (
                f"{review_label}.role_executions.adjudicator"
            )
            adjudicator = _validate_review_verdict(
                adjudicator_value, f"{review_label}.adjudicator"
            )
            _require_sha256(
                adjudicator_hash, f"{review_label}.adjudicator_output_sha256"
            )
            if fresh.get("adjudicator") is not True:
                raise BenchmarkToolError(
                    f"{review_label}.fresh_context.adjudicator must be true after disagreement"
                )
            if final != adjudicator:
                raise BenchmarkToolError(
                    f"{review_label}.final_verdict must equal the adjudicator verdict"
                )
        else:
            if (
                adjudicator_value is not None
                or adjudicator_hash is not None
                or adjudicator_execution_value is not None
            ):
                raise BenchmarkToolError(
                    f"{review_label} must not record adjudication without disagreement"
                )
            if fresh.get("adjudicator") is not False:
                raise BenchmarkToolError(
                    f"{review_label}.fresh_context.adjudicator must be false without disagreement"
                )
            if not direct["passed"] or not round_trip["passed"]:
                raise BenchmarkToolError(
                    f"{review_label} agreed failing verdicts cannot be accepted"
                )
            expected_final = {
                "score": min(direct["score"], round_trip["score"]),
                "tag": direct["tag"],
                "passed": True,
            }
            if final != expected_final:
                raise BenchmarkToolError(
                    f"{review_label}.final_verdict must be the conservative agreed verdict"
                )
        if not final["passed"]:
            raise BenchmarkToolError(f"{review_label} final verdict must pass when accepted")

    return {
        "task_id": task_id,
        "tier": "T4",
        "schema_version": T4_TASK_SCHEMA_VERSION,
        "source_inventory_count": len(raw_inventory),
        "included_source_count": sum(
            disposition == "included" for disposition in inventory_dispositions.values()
        ),
        "excluded_source_count": sum(
            disposition == "excluded" for disposition in inventory_dispositions.values()
        ),
        "declaration_count": len(declaration_ids),
        "review_unit_count": len(raw_review_units),
        "controlled_sorry_count": len(raw_sorries),
        "review_count": len(raw_reviews),
        "review_status": review_status,
        "measurement_ready": measurement_ready,
        "review_campaign_status": review_campaign_status,
    }


def _validate_t4_external_inventory(
    inventory_path: Path, task: Mapping[str, Any], *, task_id: str
) -> None:
    """Require exact external/embedded equality for the paper-neutral 0.3 ledger."""

    value = read_json(inventory_path)
    inventory = _require_mapping(value, f"{task_id} external source inventory")
    schema_version = inventory.get("schema_version")
    if schema_version != T4_SOURCE_INVENTORY_SCHEMA_VERSION:
        raise BenchmarkToolError(
            f"{task_id} external source inventory must use "
            f"{T4_SOURCE_INVENTORY_SCHEMA_VERSION!r}"
        )
    paper_id = str(task["paper_id"])
    if inventory.get("paper_id") != paper_id:
        raise BenchmarkToolError(
            f"{task_id} external source inventory has the wrong paper_id"
        )
    source = _require_mapping(
        inventory.get("source"), f"{task_id} external source inventory source"
    )
    paper_source = _require_mapping(task.get("paper_source"), f"{task_id}.paper_source")
    for field in ("local_path", "sha256"):
        if source.get(field) != paper_source.get(field):
            raise BenchmarkToolError(
                f"{task_id} external source inventory source.{field} disagrees "
                "with task.json"
            )
    external_items = _require_list(
        inventory.get("items"), f"{task_id} external source inventory items", nonempty=True
    )
    embedded_items = _require_list(
        task.get("source_inventory"), f"{task_id}.source_inventory", nonempty=True
    )
    if external_items != embedded_items:
        raise BenchmarkToolError(
            f"{task_id} external items must exactly equal task.json.source_inventory"
        )

    declarations = _require_list(
        task.get("declarations"), f"{task_id}.declarations", nonempty=True
    )
    known_declaration_ids = {
        _require_stable_id(
            _require_mapping(value, f"{task_id}.declarations[{index}]").get(
                "declaration_id"
            ),
            f"{task_id}.declarations[{index}].declaration_id",
        )
        for index, value in enumerate(declarations)
    }
    review_units = _require_list(
        task.get("review_units"), f"{task_id}.review_units", nonempty=True
    )
    unit_by_source_item: dict[str, Mapping[str, Any]] = {}
    for unit_index, raw_unit in enumerate(review_units):
        unit = _require_mapping(raw_unit, f"{task_id}.review_units[{unit_index}]")
        for source_item_id in _require_list(
            unit.get("source_item_ids"),
            f"{task_id}.review_units[{unit_index}].source_item_ids",
            nonempty=True,
        ):
            unit_by_source_item[str(source_item_id)] = unit

    known_inventory_ids = {
        str(_require_mapping(item, f"{task_id}.source_inventory[{index}]").get("inventory_id"))
        for index, item in enumerate(embedded_items)
    }
    for item_index, raw_item in enumerate(external_items):
        item_label = f"{task_id} external source inventory items[{item_index}]"
        item = _require_mapping(raw_item, item_label)
        inventory_id = _require_stable_id(
            item.get("inventory_id"), f"{item_label}.inventory_id"
        )
        raw_mappings = _require_list(
            item.get("declaration_mappings"), f"{item_label}.declaration_mappings"
        )
        carrier_ids: list[str] = []
        for mapping_index, raw_mapping in enumerate(raw_mappings):
            mapping_label = f"{item_label}.declaration_mappings[{mapping_index}]"
            mapping = _require_mapping(raw_mapping, mapping_label)
            declaration_id = _require_stable_id(
                mapping.get("declaration_id"), f"{mapping_label}.declaration_id"
            )
            if declaration_id not in known_declaration_ids:
                raise BenchmarkToolError(
                    f"{mapping_label} references unknown declaration {declaration_id!r}"
                )
            role = mapping.get("role")
            if role not in T4_DECLARATION_MAPPING_ROLES:
                raise BenchmarkToolError(
                    f"{mapping_label}.role must be one of {T4_DECLARATION_MAPPING_ROLES}"
                )
            _require_string(mapping.get("notes"), f"{mapping_label}.notes")
            if role in ("primary_carrier", "duplicate_anchor"):
                carrier_ids.append(declaration_id)
        if carrier_ids != item.get("declaration_ids"):
            raise BenchmarkToolError(
                f"{item_label}.declaration_ids must equal its ordered primary-carrier "
                "and duplicate-anchor mappings"
            )
        duplicate_ids = _require_list(
            item.get("duplicate_of_source_item_ids"),
            f"{item_label}.duplicate_of_source_item_ids",
        )
        if any(value not in known_inventory_ids for value in duplicate_ids):
            raise BenchmarkToolError(
                f"{item_label}.duplicate_of_source_item_ids references an unknown item"
            )
        if item.get("disposition") == "included":
            unit = unit_by_source_item.get(inventory_id)
            if unit is None or item.get("review_unit_id") != unit.get("review_unit_id"):
                raise BenchmarkToolError(
                    f"{item_label}.review_unit_id must match its unique review unit"
                )
            if item.get("smallest_group_reason") != unit.get("smallest_group_reason"):
                raise BenchmarkToolError(
                    f"{item_label}.smallest_group_reason must match its review unit"
                )
        elif (
            item.get("review_unit_id") is not None
            or item.get("smallest_group_reason") is not None
        ):
            raise BenchmarkToolError(
                f"{item_label} excluded item cannot name a review unit"
            )


def validate_t4_file_bindings(
    benchmark_root: Path, task: Mapping[str, Any], *, task_id: str
) -> None:
    """Authenticate the three paper-local files named by construction_inputs."""

    paper_id = str(task["paper_id"])
    construction_inputs = _require_mapping(
        task.get("construction_inputs"), f"{task_id}.construction_inputs"
    )
    expected = {
        "paper_definitions_sha256": (
            benchmark_root / "shared" / "HighamBench" / f"{paper_id}Definitions.lean"
        ),
        "source_inventory_sha256": (
            benchmark_root / "tasks" / paper_id / "T4" / "source_inventory.json"
        ),
        "target_sha256": benchmark_root / "tasks" / paper_id / "T4" / "Target.lean",
    }
    for field, file_path in expected.items():
        observed = _sha256_file(file_path, f"{task_id} {field}")
        if construction_inputs.get(field) != observed:
            raise BenchmarkToolError(
                f"{task_id}.construction_inputs.{field} does not match {file_path}"
            )
    _validate_t4_external_inventory(
        expected["source_inventory_sha256"], task, task_id=task_id
    )


def validate_task_source_tags(
    task: Mapping[str, Any], *, label: str = "task"
) -> dict[str, Any]:
    """Validate one task record and return its normalized tag summary."""

    if (
        task.get("schema_version") == T4_TASK_SCHEMA_VERSION
        or task.get("tier") == "T4"
        or (
            isinstance(task.get("task_id"), str)
            and str(task.get("task_id")).endswith("-T4")
        )
    ):
        return validate_t4_task_metadata(task, label=label)

    task_label = _label(task, label)
    if task.get("schema_version") != TASK_SCHEMA_VERSION:
        raise BenchmarkToolError(
            f"{task_label} schema_version must be {TASK_SCHEMA_VERSION!r}"
        )
    raw_tags = task.get("source_tags")
    if not isinstance(raw_tags, list) or not raw_tags:
        raise BenchmarkToolError(f"{task_label} source_tags must be a nonempty list")
    if any(not isinstance(tag, str) or not tag for tag in raw_tags):
        raise BenchmarkToolError(f"{task_label} source_tags must contain strings")
    tags = list(raw_tags)
    unknown = [tag for tag in tags if tag not in ALLOWED_SOURCE_TAGS]
    if unknown:
        raise BenchmarkToolError(
            f"{task_label} has unknown source tags: {', '.join(unknown)}"
        )
    if len(set(tags)) != len(tags):
        raise BenchmarkToolError(f"{task_label} repeats a source tag")
    expected_order = sorted(tags, key=ALLOWED_SOURCE_TAGS.index)
    if tags != expected_order:
        raise BenchmarkToolError(
            f"{task_label} source_tags must use canonical order: {expected_order}"
        )

    named = [tag for tag in tags if tag in NAMED_SOURCE_TAGS]
    author_label = task.get("author_label")
    if named:
        if len(named) != 1 or len(tags) != 1:
            raise BenchmarkToolError(
                f"{task_label} must use exactly one named source tag"
            )
        if not isinstance(author_label, str) or not author_label.strip():
            raise BenchmarkToolError(
                f"{task_label} {named[0]} tag requires an exact author_label"
            )
        printed_kind = NAMED_SOURCE_TAGS[named[0]]
        if (
            re.match(
                rf"^{re.escape(printed_kind)}(?:\s|$)",
                author_label,
                flags=re.IGNORECASE,
            )
            is None
        ):
            raise BenchmarkToolError(
                f"{task_label} author_label must begin with {printed_kind!r}"
            )
    elif author_label is not None:
        raise BenchmarkToolError(
            f"{task_label} author_label must be null for non-named source tags"
        )

    if "EQN" in tags and "UNL" in tags:
        raise BenchmarkToolError(
            f"{task_label} cannot be both a numbered equation and an unnumbered display"
        )
    measurement_ready = task.get("classification_frozen_before_runs")
    if not isinstance(measurement_ready, bool):
        raise BenchmarkToolError(
            f"{task_label} classification_frozen_before_runs must be a boolean"
        )
    locations = task.get("source_locations")
    if not isinstance(locations, list) or not locations:
        raise BenchmarkToolError(f"{task_label} must record source_locations evidence")

    return {
        "task_id": task.get("task_id"),
        "source_tags": tags,
        "author_label": author_label,
        "measurement_ready": measurement_ready,
    }


def task_record_paths(
    benchmark_root: Path, *, paper_id: str | None = None
) -> list[Path]:
    """Return canonical task records, optionally for exactly one paper."""

    root = benchmark_root.resolve()
    if paper_id is not None and re.fullmatch(r"P[0-9]+", paper_id) is None:
        raise BenchmarkToolError(f"invalid paper_id: {paper_id!r}")
    pattern = f"{paper_id}/T*/task.json" if paper_id is not None else "P*/T*/task.json"
    paths: list[Path] = []
    for path in sorted((root / "tasks").glob(pattern)):
        relative = path.relative_to(root)
        if len(relative.parts) != 4:
            continue
        paper_id, tier = relative.parts[1:3]
        if re.fullmatch(r"P[0-9]+", paper_id) is None:
            continue
        if re.fullmatch(r"T[0-9]+", tier) is None:
            continue
        paths.append(path)
    return paths


def validate_task_catalog(
    benchmark_root: Path, *, paper_id: str | None = None
) -> dict[str, Any]:
    """Validate task records below a benchmark root or one paper shard."""

    root = benchmark_root.resolve()
    paths = task_record_paths(root, paper_id=paper_id)
    if not paths:
        scope = root / "tasks" if paper_id is None else root / "tasks" / paper_id
        raise BenchmarkToolError(f"no task records found below {scope}")
    records: list[dict[str, Any]] = []
    errors: list[str] = []
    for path in paths:
        relative = path.relative_to(root)
        expected_task_id = f"{relative.parts[1]}-{relative.parts[2]}"
        try:
            value = read_json(path)
            if not isinstance(value, Mapping):
                raise BenchmarkToolError(f"{expected_task_id} task record must be an object")
            if value.get("task_id") != expected_task_id:
                raise BenchmarkToolError(
                    f"{relative.as_posix()} has task_id={value.get('task_id')!r}, "
                    f"expected {expected_task_id!r}"
                )
            records.append(
                {
                    **validate_task_source_tags(value, label=expected_task_id),
                    "path": relative.as_posix(),
                }
            )
            if value.get("tier") == "T4":
                validate_t4_file_bindings(root, value, task_id=expected_task_id)
        except BenchmarkToolError as error:
            errors.append(str(error))
    if errors:
        raise BenchmarkToolError("task source-tag validation failed:\n- " + "\n- ".join(errors))
    return {
        "ok": True,
        "allowed_source_tags": list(ALLOWED_SOURCE_TAGS),
        "paper_id": paper_id,
        "task_count": len(records),
        "tasks": records,
    }


def make_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--benchmark-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
    )
    parser.add_argument(
        "--paper-id",
        help="validate exactly one paper shard (for example P06)",
    )
    parser.add_argument("--json", action="store_true", help="print the full JSON result")
    return parser


def main(argv: Sequence[str] | None = None) -> int:
    args = make_parser().parse_args(argv)
    try:
        result = validate_task_catalog(args.benchmark_root, paper_id=args.paper_id)
    except BenchmarkToolError as error:
        print(f"task-tags error: {error}", file=sys.stderr)
        return 1
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        print(f"task source tags valid: {result['task_count']} tasks")
        for task in result["tasks"]:
            state = "measurement-ready" if task["measurement_ready"] else "construction"
            if task.get("tier") == "T4":
                print(
                    f"  {task['task_id']}: T4 corpus "
                    f"({task['source_inventory_count']} inventory items; "
                    f"{task['declaration_count']} declarations; "
                    f"{task['controlled_sorry_count']} controlled sorries; {state})"
                )
            else:
                tags = "+".join(task["source_tags"])
                author = task["author_label"] or "no author label"
                print(f"  {task['task_id']}: {tags} ({author}; {state})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
