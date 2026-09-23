#!/usr/bin/env python3
"""Build deterministic, bounded declaration packets for a formalization task.

The packet is the whole task-time retrieval interface.  It is generated before
the contestant clock from the frozen source packet and a frozen declaration
atlas.  The same algorithm can therefore be run over a Mathlib-only corpus and
over Mathlib plus NumStability without asking the formalizer to explore either
codebase during the measured turn.
"""

from __future__ import annotations

import argparse
from collections import Counter, defaultdict
import json
import math
from pathlib import Path
import re
from typing import Any, Iterable, Mapping

from common import (
    BenchmarkError,
    canonical_json_bytes,
    load_json,
    sha256_file,
    write_bytes_atomic,
    write_json_atomic,
)


SCHEMA_VERSION = "formalization-composition-packet-1"
TOKEN_RE = re.compile(r"[A-Za-z][A-Za-z0-9]*")
CAMEL_BOUNDARY_RE = re.compile(r"(?<=[a-z0-9])(?=[A-Z])")
IDENTIFIER_RE = re.compile(r"\b[A-Za-z_][A-Za-z0-9_'.]*\b")
ALLOWED_KINDS = {"theorem", "lemma", "def", "abbrev", "structure", "class", "inductive"}

# These words occur in almost every mathematical task and make lexical
# retrieval noisier without expressing the numerical-analysis concept.
STOP_WORDS = {
    "a", "all", "also", "an", "and", "are", "as", "assume", "be", "by",
    "case", "claim", "consider", "define", "defined", "each", "equation",
    "exact", "explicit", "for", "form", "formalize", "from", "given", "has",
    "have", "if", "in", "into", "is", "it", "its", "let", "must", "no",
    "not", "of", "on", "only", "or", "paper", "problem", "represent",
    "result", "source", "state", "stated", "statement", "such", "than",
    "that", "the", "their", "then", "this", "to", "under", "use", "used",
    "where", "which", "with", "without", "zero", "one", "two", "three",
    "real", "number", "value", "values", "function", "functions",
}
GENERIC_TITLE_PAIR_TERMS = {"analysis", "bound", "error", "property", "result"}

NORMAL_FORMS = {
    "analysis": "analysis",
    "analyses": "analysis",
    "matrices": "matrix",
    "matrixes": "matrix",
    "entries": "entry",
    "diagonal": "diag",
    "diagonals": "diag",
    "multiplications": "multiply",
    "multiplication": "multiply",
    "multiplier": "multiply",
    "products": "product",
    "polynomials": "polynomial",
    "rounded": "round",
    "rounding": "round",
    "eval": "evaluation",
    "evaluate": "evaluation",
    "evaluated": "evaluation",
    "evaluating": "evaluation",
    "computed": "compute",
    "computing": "compute",
    "computation": "compute",
    "subtractions": "subtract",
    "subtraction": "subtract",
    "perturbations": "perturbation",
    "inequalities": "inequality",
    "coefficients": "coefficient",
    "bounds": "bound",
    "roots": "root",
    "symmetric": "symmetry",
    "symmetry": "symmetry",
    "pivoted": "pivot",
    "pivoting": "pivot",
    "pivots": "pivot",
    "ordered": "order",
    "ordering": "order",
    "semidefinite": "psd",
    "cholesky": "cholesky",
}

CONTRACT_PROBES: tuple[tuple[str, tuple[str, ...]], ...] = (
    ("algorithm/output represented", ("algorithm", "computation", "computed", "output", "evaluation", "executor", "trace")),
    ("pivot/choice rule represented", ("argmax", "choice", "pivot")),
    ("deterministic tie-breaking represented", ("tie", "least", "min index")),
    ("existence structure represented", ("exists", "existence", "there exists")),
    ("rounding model represented", ("round", "rounding", "floating", "unit roundoff", "fpmodel", "gamma")),
    ("norm specified", ("norm", "frobenius", "infinity norm", "opnorm", "inf norm")),
    ("limit/supremum represented", ("limit", "supremum", "lim", "sup")),
    ("index ranges represented", ("index", "indices", "range", "for j", "for k")),
)


def _normal_form(token: str) -> str:
    lowered = token.casefold()
    if lowered in NORMAL_FORMS:
        return NORMAL_FORMS[lowered]
    if len(lowered) > 5 and lowered.endswith("ies"):
        lowered = lowered[:-3] + "y"
    elif len(lowered) > 5 and lowered.endswith("ing"):
        lowered = lowered[:-3]
    elif len(lowered) > 4 and lowered.endswith("ed"):
        lowered = lowered[:-2]
    elif len(lowered) > 4 and lowered.endswith("s"):
        lowered = lowered[:-1]
    return NORMAL_FORMS.get(lowered, lowered)


def _tokens(text: str) -> list[str]:
    expanded = CAMEL_BOUNDARY_RE.sub(" ", text.replace("_", " ").replace(".", " "))
    result: list[str] = []
    for raw in TOKEN_RE.findall(expanded):
        token = _normal_form(raw)
        if len(token) < 3 or token in STOP_WORDS or token.isdigit():
            continue
        result.append(token)
    lowered = text.casefold()
    if "ispossemidef" in lowered or "positive semidefinite" in lowered:
        result.append("psd")
    concepts = set(result)
    # Task-neutral API aliases.  These describe library representations, not
    # benchmark answers, and close common notation gaps in identifier search.
    if {"root", "product", "evaluation"} <= concepts:
        result.append("polynomial")
    if {"pivot", "cholesky"} <= concepts:
        result.extend(["complete", "factor"])
    if "tail" in concepts:
        result.extend(["order", "range", "inequality", "bound"])
    if "∃" in text or re.search(r"\bexists\b", lowered):
        result.append("existence")
    if any(symbol in text for symbol in ("≤", "≥", "<", ">")):
        result.append("inequality")
    return result


def task_text(packet: Mapping[str, Any]) -> str:
    fields: list[str] = [str(packet.get("selected_result", ""))]
    for key in ("task_clarification", "scope_constraints", "faithfulness_contract"):
        values = packet.get(key, [])
        if isinstance(values, list):
            fields.extend(str(value) for value in values)
    return "\n".join(fields)


def query_terms(packet: Mapping[str, Any], *, maximum: int = 32) -> list[str]:
    counts = Counter(_tokens(task_text(packet)))
    # Frequency first, then lexical order makes the result deterministic while
    # retaining repeated concepts such as pivot, gamma, norm, and product.
    ordered = sorted(counts, key=lambda token: (-counts[token], token))
    return ordered[:maximum]


def _term_importance(packet: Mapping[str, Any]) -> tuple[dict[str, float], set[str]]:
    importance: dict[str, float] = defaultdict(float)
    title_terms = set(_tokens(str(packet.get("selected_result", ""))))
    for term in title_terms:
        importance[term] += 5.0
    for value in packet.get("task_clarification", []):
        for term in set(_tokens(str(value))):
            importance[term] += 1.5
    for key in ("scope_constraints", "faithfulness_contract"):
        for value in packet.get(key, []):
            for term in set(_tokens(str(value))):
                importance[term] += 0.75
    return dict(importance), title_terms


def _title_anchor_pairs(packet: Mapping[str, Any]) -> list[tuple[str, str]]:
    ordered = _tokens(str(packet.get("selected_result", "")))
    pairs: list[tuple[str, str]] = []
    for left, right in zip(ordered, ordered[1:]):
        if left in GENERIC_TITLE_PAIR_TERMS or right in GENERIC_TITLE_PAIR_TERMS:
            continue
        pair = (left, right)
        if pair not in pairs:
            pairs.append(pair)
    return pairs


def load_records(paths: Iterable[Path]) -> list[dict[str, Any]]:
    records: list[dict[str, Any]] = []
    for path in paths:
        if not path.is_file() or path.is_symlink():
            raise BenchmarkError(f"composition atlas is missing or unsafe: {path}")
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            try:
                record = json.loads(line)
            except json.JSONDecodeError as error:
                raise BenchmarkError(
                    f"malformed atlas JSON at {path}:{line_number}"
                ) from error
            if not isinstance(record, dict) or not isinstance(record.get("name"), str):
                raise BenchmarkError(f"malformed atlas record at {path}:{line_number}")
            records.append(record)
    records.sort(key=lambda item: (str(item.get("module", "")), str(item["name"])))
    return records


def _field_tokens(record: Mapping[str, Any]) -> dict[str, set[str]]:
    return {
        field: set(_tokens(str(record.get(field, ""))))
        for field in ("name", "module", "documentation", "signature")
    }


def rank_records(
    packet: Mapping[str, Any],
    records: list[dict[str, Any]],
) -> list[dict[str, Any]]:
    terms = query_terms(packet)
    if not terms:
        raise BenchmarkError("source packet produced no retrieval terms")
    term_set = set(terms)
    importance, title_terms = _term_importance(packet)
    tokenized = [_field_tokens(record) for record in records]
    document_frequency: Counter[str] = Counter()
    for fields in tokenized:
        present = set().union(*fields.values()) & term_set
        document_frequency.update(present)
    population = max(1, len(records))
    ranked: list[dict[str, Any]] = []
    for record, fields in zip(records, tokenized, strict=True):
        if str(record.get("kind", "")) not in ALLOWED_KINDS:
            continue
        matched = set().union(*fields.values()) & term_set
        if not matched:
            continue
        score = 0.0
        contributions: dict[str, list[str]] = {}
        for field, weight in (
            ("name", 9.0),
            ("documentation", 6.0),
            ("signature", 3.0),
            ("module", 2.0),
        ):
            overlap = sorted(fields[field] & term_set)
            if overlap:
                contributions[field] = overlap
            for term in overlap:
                inverse_frequency = math.log((population + 1) / (document_frequency[term] + 1)) + 1
                score += weight * inverse_frequency * importance.get(term, 0.5)
        coverage = len(matched) / len(term_set)
        score += 40.0 * coverage * coverage
        kind = str(record.get("kind", ""))
        if kind in {"theorem", "lemma"}:
            score += 200.0
        elif kind in {"structure", "class"}:
            score -= 50.0
        title_overlap = set().union(*fields.values()) & title_terms
        title_coverage = len(title_overlap) / max(1, len(title_terms))
        score += 220.0 * title_coverage * title_coverage
        if len(title_overlap) >= 2:
            score += 25.0 * (len(title_overlap) - 1)
        elif title_terms:
            score -= 45.0
        # Closely coupled concepts are more useful than declarations matching
        # many generic words independently.
        for left, right in (
            ("root", "product"),
            ("polynomial", "evaluation"),
            ("cholesky", "pivot"),
            ("pivot", "psd"),
            ("symmetry", "perturbation"),
            ("strassen", "error"),
        ):
            if left in title_terms and right in title_terms and {left, right} <= matched:
                score += 300.0
        signature_bytes = len(str(record.get("signature", "")).encode("utf-8"))
        if signature_bytes > 4096:
            score -= min(25.0, (signature_bytes - 4096) / 512)
        if str(record.get("signature", "")).lstrip().startswith("private "):
            score -= 100.0
        ranked.append(
            {
                "score": round(score, 6),
                "matched_terms": sorted(matched),
                "field_matches": contributions,
                "record": record,
            }
        )
    ranked.sort(
        key=lambda item: (
            -float(item["score"]),
            str(item["record"].get("module", "")),
            str(item["record"]["name"]),
        )
    )
    return ranked


def _select_roots(ranked: list[dict[str, Any]], *, limit: int) -> list[dict[str, Any]]:
    module_best: dict[str, float] = {}
    for item in ranked:
        module = str(item["record"].get("module", ""))
        module_best.setdefault(module, float(item["score"]))
    reordered = sorted(
        ranked,
        key=lambda item: (
            -(
                float(item["score"])
                + (
                    500.0
                    if item["record"].get("kind") in {"theorem", "lemma"}
                    and float(item["score"])
                    >= 0.75 * module_best[str(item["record"].get("module", ""))]
                    else 0.0
                )
            ),
            str(item["record"].get("module", "")),
            str(item["record"]["name"]),
        ),
    )
    selected: list[dict[str, Any]] = []
    per_module: Counter[str] = Counter()
    for item in reordered:
        module = str(item["record"].get("module", ""))
        if per_module[module] >= 2:
            continue
        selected.append(item)
        per_module[module] += 1
        if len(selected) == limit:
            break
    return selected


def _dependency_records(
    root: Mapping[str, Any],
    records: list[dict[str, Any]],
    *,
    limit: int,
) -> list[dict[str, Any]]:
    by_display: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for record in records:
        display = str(record.get("display_name") or str(record["name"]).rsplit(".", 1)[-1])
        by_display[display].append(record)
    signature = str(root.get("signature", ""))
    candidates: list[tuple[int, str, dict[str, Any]]] = []
    root_name = str(root["name"])
    root_module = str(root.get("module", ""))
    seen: set[str] = set()
    for identifier in IDENTIFIER_RE.findall(signature):
        short = identifier.rsplit(".", 1)[-1]
        if short in seen or len(short) < 4:
            continue
        seen.add(short)
        matches = by_display.get(short, [])
        if len(matches) != 1:
            exact = [
                record
                for record in matches
                if str(record["name"]) == f"NumStability.{short}"
            ]
            if len(exact) != 1:
                continue
            candidate = exact[0]
        else:
            candidate = matches[0]
        if candidate["name"] == root_name or candidate.get("kind") not in ALLOWED_KINDS:
            continue
        priority = 0 if str(candidate.get("module", "")) == root_module else 2
        candidates.append((priority, str(candidate["name"]), candidate))
        # Common library API bridge conventions.  These are inferred from the
        # selected signature, never from a task ID or hand-authored mapping.
        for suffix in ("_mono", "_nonneg"):
            bridge_matches = by_display.get(short + suffix, [])
            if len(bridge_matches) == 1:
                bridge = bridge_matches[0]
                if bridge.get("kind") in {"theorem", "lemma"}:
                    candidates.append((1, str(bridge["name"]), bridge))
    candidates.sort(key=lambda value: (value[0], value[1]))
    selected: list[dict[str, Any]] = []
    selected_names: set[str] = set()
    for _, name, record in candidates:
        if name in selected_names:
            continue
        selected.append(record)
        selected_names.add(name)
        if len(selected) == limit:
            break
    return selected


def _contract_alignment(packet: Mapping[str, Any], root: Mapping[str, Any]) -> list[dict[str, Any]]:
    source = task_text(packet).casefold()
    candidate = "\n".join(
        str(root.get(field, ""))
        for field in ("name", "module", "documentation", "signature")
    ).casefold()
    rows: list[dict[str, Any]] = []
    for label, probes in CONTRACT_PROBES:
        required = any(probe in source for probe in probes)
        if label == "rounding model represented" and (
            "no floating-point model is required" in source
            or "not a rounding-error bound" in source
        ):
            required = False
        if not required:
            continue
        evidence = sorted(probe for probe in probes if probe in candidate)
        rows.append(
            {
                "requirement": label,
                "lexical_evidence": evidence,
                "status": "surface-evidence" if evidence else "not-visible-in-signature",
            }
        )
    return rows


def _compact_record(record: Mapping[str, Any]) -> dict[str, Any]:
    result = {
        key: record[key]
        for key in ("name", "kind", "module", "source_file", "source_line", "signature")
        if key in record
    }
    if record.get("documentation"):
        result["documentation"] = record["documentation"]
    return result


def build_composition_packet(
    *,
    source_packet_path: Path,
    atlas_paths: list[Path],
    corpus_id: str,
    contract_additions: list[str] | None = None,
    root_limit: int = 6,
    dependency_limit: int = 5,
    maximum_markdown_bytes: int = 48 * 1024,
    exposed_signature_overrides: Mapping[str, str] | None = None,
    selection_policy: str = "legacy-coupled-title",
    open_library_access: bool = False,
) -> tuple[dict[str, Any], bytes]:
    if selection_policy == "no-automatic-retrieval":
        if not open_library_access or root_limit != 0 or dependency_limit != 0:
            raise BenchmarkError(
                "no-automatic-retrieval requires open access and zero packet limits"
            )
        if exposed_signature_overrides not in (None, {}):
            raise BenchmarkError("unrouted interface cannot expose signatures")
        packet = load_json(source_packet_path)
        atlas_identity = [
            {"path_basename": path.name, "sha256": sha256_file(path)}
            for path in atlas_paths
        ]
        markdown = (
            "# Library access\n\n"
            "No task-specific declarations have been selected or supplied by the "
            "controller. You may inspect the complete read-only library source "
            "and compiled declarations mounted in your condition, using ordinary "
            "file search and Lean type probes. All task-time exploration counts "
            "in the contestant clock. The paper statement, not a library result, "
            "determines the target.\n"
        ).encode("utf-8")
        if len(markdown) > maximum_markdown_bytes:
            raise BenchmarkError("unrouted access note exceeds byte budget")
        result = {
            "schema_version": SCHEMA_VERSION,
            "task_id": packet["task_id"],
            "corpus_id": corpus_id,
            "source_packet_sha256": sha256_file(source_packet_path),
            "atlas_inputs": atlas_identity,
            "query_terms": [],
            "title_anchor_pairs": [],
            "route_status": "NO_ROUTE",
            "selection_policy": selection_policy,
            "root_limit": 0,
            "dependency_limit_per_root": 0,
            "retrieved_roots": [],
            "diagnostic_ranked_candidates": [],
            "retrieval_candidate_count": 0,
            "policy": {
                "automatic": False,
                "human_edits": False,
                "task_time_search_permitted": True,
                "packet_is_exhaustive_interface": False,
                "exposed_signature_source": "none",
            },
            "markdown_bytes": len(markdown),
            "markdown_sha256": __import__("hashlib").sha256(markdown).hexdigest(),
        }
        return result, markdown
    if not (1 <= root_limit <= 12):
        raise BenchmarkError("composition root limit must be between 1 and 12")
    if not (0 <= dependency_limit <= 8):
        raise BenchmarkError("composition dependency limit must be between 0 and 8")
    packet = load_json(source_packet_path)
    if contract_additions:
        packet = dict(packet)
        packet["faithfulness_contract"] = [
            *packet.get("faithfulness_contract", []),
            *contract_additions,
        ]
    records = load_records(atlas_paths)
    ranked = rank_records(packet, records)
    if selection_policy == "legacy-coupled-title":
        roots = _select_roots(ranked, limit=root_limit)
    elif selection_policy in {"component-roles-1", "component-roles-contextual-2"}:
        from component_router import routing_anchor_text, select_component_roots

        roots = select_component_roots(
            ranked, records=records, source_text=routing_anchor_text(packet),
            limit=root_limit,
            strict_stochastic_roles=selection_policy == "component-roles-contextual-2",
        )
    else:
        raise BenchmarkError(f"unknown composition selection policy: {selection_policy}")
    if not roots and selection_policy == "legacy-coupled-title":
        raise BenchmarkError("composition retrieval found no declaration candidates")
    cards: list[dict[str, Any]] = []
    for ranked_root in roots:
        root = ranked_root["record"]
        cards.append(
            {
                "rank": len(cards) + 1,
                "component_role": ranked_root.get("component_role"),
                "api_anchor": ranked_root.get("api_anchor", False),
                "score": ranked_root["score"],
                "matched_terms": ranked_root["matched_terms"],
                "field_matches": ranked_root["field_matches"],
                "declaration": _compact_record(root),
                "dependencies": [
                    _compact_record(item)
                    for item in _dependency_records(
                        root, records, limit=dependency_limit
                    )
                ],
                "contract_alignment": _contract_alignment(packet, root),
            }
        )
    title_anchor_pairs = _title_anchor_pairs(packet)
    anchor_counts = [
        sum(
            1
            for left, right in title_anchor_pairs
            if {left, right} <= set(card["matched_terms"])
        )
        for card in cards
    ]
    route_status = (
        "DIRECT_OR_COMPOSITION"
        if (
            (selection_policy in {"component-roles-1", "component-roles-contextual-2"} and bool(cards))
            or (title_anchor_pairs and max(anchor_counts, default=0) >= 2)
        )
        else "NO_ROUTE"
    )
    exposed_cards = cards if route_status != "NO_ROUTE" else []
    if exposed_signature_overrides is not None:
        exposed_names = {
            str(record["name"])
            for card in exposed_cards
            for record in [card["declaration"], *card["dependencies"]]
        }
        if set(exposed_signature_overrides) != exposed_names:
            raise BenchmarkError(
                "canonical signature overrides do not match the exposed packet records"
            )
        for card in exposed_cards:
            for record in [card["declaration"], *card["dependencies"]]:
                replacement = exposed_signature_overrides[str(record["name"])]
                if not isinstance(replacement, str) or not replacement.strip():
                    raise BenchmarkError("canonical signature override is empty")
                record["signature"] = replacement
    atlas_identity = [
        {"path_basename": path.name, "sha256": sha256_file(path)}
        for path in atlas_paths
    ]
    result: dict[str, Any] = {
        "schema_version": SCHEMA_VERSION,
        "task_id": packet["task_id"],
        "corpus_id": corpus_id,
        "source_packet_sha256": sha256_file(source_packet_path),
        "atlas_inputs": atlas_identity,
        "query_terms": query_terms(packet),
        "title_anchor_pairs": [list(pair) for pair in title_anchor_pairs],
        "route_status": route_status,
        "selection_policy": selection_policy,
        "root_limit": root_limit,
        "dependency_limit_per_root": dependency_limit,
        "retrieved_roots": exposed_cards,
        "diagnostic_ranked_candidates": cards,
        "retrieval_candidate_count": len(ranked),
        "policy": {
            "automatic": True,
            "human_edits": False,
            "task_time_search_permitted": open_library_access,
            "packet_is_exhaustive_interface": not open_library_access,
            "exposed_signature_source": (
                "elaborated-constant-type"
                if exposed_signature_overrides is not None
                else "source-atlas"
            ),
        },
    }
    access_note = (
        [
            "These cards are starting suggestions, not an access whitelist. The",
            "frozen library source, compiled modules, and declaration index remain",
            "available for read-only task-time search. You may import and use any",
            "compatible declaration in the frozen snapshot. Search time is part of",
            "the contestant clock. Do not assume that a retrieved card is faithful.",
        ] if open_library_access else [
            "This packet was generated automatically from the frozen source contract and",
            "declaration atlas. It is the complete task-time retrieval interface. Do not",
            "search library source or a broader index. Test the smallest compatible card",
            "first; if none is semantically compatible, proceed without library reuse.",
        ]
    )
    lines = [
        f"# Frozen composition packet: {packet['task_id']} / {corpus_id}",
        "",
        *access_note,
        "",
        "The alignment rows are lexical warnings, not faithfulness judgments. In",
        "particular, `not-visible-in-signature` means the contestant must verify or",
        "construct that requirement rather than assuming it.",
        "",
        f"Route status: **{route_status}**.",
        "",
        "## Query concepts",
        "",
        ", ".join(f"`{term}`" for term in result["query_terms"]),
        "",
    ]
    if selection_policy in {"component-roles-1", "component-roles-contextual-2"}:
        lines.extend([
            "A retrieved declaration may use a different probability space,",
            "rounding model, or algorithm representation from the paper. Do not",
            "narrow the paper's domain or assume the desired bound to use a card;",
            "ignore incompatible cards and formalize the source faithfully.",
            "",
        ])
    if route_status == "NO_ROUTE":
        lines.extend(
            [
                "No declaration route met the frozen coupled-concept threshold.",
                (
                    "You may still search the frozen libraries for compatible components."
                    if open_library_access else
                    "Do not search for a substitute. Formalize the task locally using Mathlib."
                ),
                "",
            ]
        )
    for card in exposed_cards:
        declaration = card["declaration"]
        lines.extend(
            [
                f"## {card['rank']}. `{declaration['name']}`",
                "",
                f"- Import: `{declaration['module']}`",
                *(
                    [f"- Component role: `{card['component_role']}`"]
                    if card.get("component_role") else []
                ),
                f"- Retrieval score: `{card['score']}`",
                "- Matched concepts: " + ", ".join(
                    f"`{term}`" for term in card["matched_terms"]
                ),
                f"- Frozen source locator: `{declaration.get('source_file')}:{declaration.get('source_line')}`",
                "",
            ]
        )
        if declaration.get("documentation"):
            lines.extend([str(declaration["documentation"]), ""])
        lines.extend(["```lean", str(declaration.get("signature", "")), "```", ""])
        if card["contract_alignment"]:
            lines.extend(["Contract-surface checks:", ""])
            for row in card["contract_alignment"]:
                evidence = ", ".join(row["lexical_evidence"]) or "none"
                lines.append(
                    f"- {row['requirement']}: **{row['status']}** (evidence: {evidence})"
                )
            lines.append("")
        if card["dependencies"]:
            lines.extend(["Signature dependencies:", ""])
            for dependency in card["dependencies"]:
                lines.extend(
                    [
                        f"- `{dependency['name']}` from `{dependency['module']}`",
                        "  ```lean",
                        *[f"  {line}" for line in str(dependency.get("signature", "")).splitlines()],
                        "  ```",
                    ]
                )
            lines.append("")
    markdown = ("\n".join(lines).rstrip() + "\n").encode("utf-8")
    if len(markdown) > maximum_markdown_bytes:
        raise BenchmarkError(
            f"composition packet exceeds byte budget: {len(markdown)} > {maximum_markdown_bytes}"
        )
    result["markdown_bytes"] = len(markdown)
    result["markdown_sha256"] = __import__("hashlib").sha256(markdown).hexdigest()
    return result, markdown


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-packet", type=Path, required=True)
    parser.add_argument("--atlas", type=Path, action="append", required=True)
    parser.add_argument("--corpus-id", required=True)
    parser.add_argument("--contract-additions", type=Path)
    parser.add_argument("--output-json", type=Path, required=True)
    parser.add_argument("--output-markdown", type=Path, required=True)
    parser.add_argument("--root-limit", type=int, default=6)
    parser.add_argument("--dependency-limit", type=int, default=5)
    parser.add_argument("--maximum-markdown-bytes", type=int, default=48 * 1024)
    args = parser.parse_args()
    additions: list[str] | None = None
    if args.contract_additions is not None:
        overlay = load_json(args.contract_additions)
        if overlay.get("task_id") != load_json(args.source_packet).get("task_id"):
            raise BenchmarkError("contract-additions task ID does not match source packet")
        raw_additions = overlay.get("faithfulness_contract")
        if not isinstance(raw_additions, list) or not all(
            isinstance(value, str) and value for value in raw_additions
        ):
            raise BenchmarkError("contract additions are malformed")
        additions = raw_additions
    result, markdown = build_composition_packet(
        source_packet_path=args.source_packet,
        atlas_paths=args.atlas,
        corpus_id=args.corpus_id,
        contract_additions=additions,
        root_limit=args.root_limit,
        dependency_limit=args.dependency_limit,
        maximum_markdown_bytes=args.maximum_markdown_bytes,
    )
    write_json_atomic(args.output_json, result, mode=0o644)
    write_bytes_atomic(args.output_markdown, markdown, mode=0o644)
    print(canonical_json_bytes(result).decode("utf-8"), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
