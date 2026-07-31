#!/usr/bin/env python3
"""The deterministic parts of the classification proposal policy.

The reviewed *tier* of every module is a human judgement recorded in
``classification/modules.tsv``.  Everything that can be derived from that
judgement plus the frozen sources lives here, so the proposal and its checker
cannot drift: ``check_classification_proposal.py`` recomputes each derived
column with these functions and requires exact agreement.

Vocabulary
----------

Tiers mirror ``docs/architecture/tiers.json`` semantics, with ``mixed`` renamed
``mixed_pending_split`` to make the split queue explicit in the proposal:

reusable
    source-independent mathematics; must not reach ``source``/``mixed``
source
    numbered correspondence to the book (aliases, numbered results,
    corrections, discrepancies, printed displays, worked examples, capstones)
internal
    proof support with no public mathematical surface
aggregate
    declaration-free import-only umbrella
compatibility
    declaration-free import-only historical forwarding path
mixed_pending_split
    reviewed owner that holds both reusable and source-owned declarations

Actions
-------

register_tier_only
    add the tier rule; no file moves
plan_source_extraction
    move to the canonical ``Source/Higham/ChapterNN`` family, leaving an
    import-only wrapper at the historical path
plan_reusable_relocation
    move to the canonical reusable family, leaving an import-only wrapper
plan_semantic_split: <detail>
    split a mixed owner; ``<detail>`` names both destinations
defer_pending_upstream_split
    source-neutral content whose closure still reaches the numbered-source
    tier; do not register it reusable until the named owner is split
"""

from __future__ import annotations

import re


PROPOSAL_HEADER: tuple[str, ...] = (
    "module",
    "path",
    "proposed_tier",
    "confidence",
    "source_markers",
    "reusable_markers",
    "public_declaration_count",
    "direct_project_imports",
    "required_action",
    "proposed_canonical_family",
    "cross_lane_dependency",
    "rationale",
)

TIERS: frozenset[str] = frozenset(
    {"reusable", "source", "internal", "aggregate", "compatibility", "mixed_pending_split"}
)

CONFIDENCES: tuple[str, ...] = ("high", "medium", "low")

SIMPLE_ACTIONS: frozenset[str] = frozenset(
    {
        "register_tier_only",
        "plan_source_extraction",
        "plan_reusable_relocation",
        "defer_pending_upstream_split",
    }
)

SPLIT_ACTION_PREFIX = "plan_semantic_split: "

# Tier -> the actions that tier may carry.
ACTIONS_BY_TIER: dict[str, frozenset[str]] = {
    "reusable": frozenset({"plan_reusable_relocation", "register_tier_only",
                           "defer_pending_upstream_split"}),
    "source": frozenset({"plan_source_extraction", "register_tier_only"}),
    "internal": frozenset({"register_tier_only"}),
    "aggregate": frozenset({"register_tier_only"}),
    "compatibility": frozenset({"register_tier_only"}),
    "mixed_pending_split": frozenset({SPLIT_ACTION_PREFIX.strip()}),
}

BLOCKED_MARKER_PREFIX = "REUSABLE_BLOCKED_BY:"
BLOCKLU_MARKER = "BLOCKLU_REFRESH_REQUIRED"
CH09_MARKER = "CH09_BLOCKED_ON_BLOCKLU_INTEGRATION"
CH11_MARKER = "CH11_BLOCKED_ON_CH09_INTEGRATION"
NON_HIGHAM_MARKER = "NON_HIGHAM_SOURCE_REVIEW_REQUIRED"
NO_DEPENDENCY = "none"

# The three frozen rows whose imports -- but not declaration bodies -- are
# changed by the preserved local BlockLU/Chapter 13 wave.
BLOCKLU_REFRESH_ROWS: tuple[str, ...] = (
    "NumStability.Algorithms.Ch14Problem142",
    "NumStability.Algorithms.HighamChapter9",
    "NumStability.Algorithms.MatrixInversionMethod2BInstance",
)

# Modules whose numbered correspondence is to a non-Higham source (the CACM
# RandNLA survey of Drineas and Mahoney), for which the repository has no
# source family.  The tier here is a conservative reusable reading; creating a
# non-Higham source tier is an integrator decision.
NON_HIGHAM_PREFIX = "NumStability.Algorithms.RandNLA"

SOURCE_FAMILY_RE = re.compile(r"^NumStability\.Source\.Higham\.Chapter\d{2}$")
MODULE_RE = re.compile(r"^NumStability(?:\.[A-Za-z0-9_']+)+$")


def required_action(tier: str, blocked: bool, split_detail: str = "") -> str:
    if tier == "mixed_pending_split":
        if not split_detail:
            raise ValueError("a mixed_pending_split row needs a concrete split detail")
        return SPLIT_ACTION_PREFIX + split_detail
    if tier == "source":
        return "plan_source_extraction"
    if tier == "reusable":
        return "defer_pending_upstream_split" if blocked else "plan_reusable_relocation"
    return "register_tier_only"


def confidence(
    tier: str,
    public_declarations: int,
    located_public: int,
    blocked: bool,
    module: str,
) -> str:
    """Derive the reviewed confidence deterministically from the evidence."""

    if module.startswith(NON_HIGHAM_PREFIX + ".") and located_public > 0:
        return "low"
    if tier in {"aggregate", "compatibility", "internal"}:
        return "high"
    if tier == "source":
        if public_declarations and located_public / public_declarations >= 0.5:
            return "high"
        return "medium"
    if tier == "reusable":
        if blocked or located_public:
            return "medium"
        return "high"
    return "medium"


def cross_lane_dependency(
    module: str,
    tier: str,
    chapter: str | None,
    blockers: list[str] | tuple[str, ...],
) -> str:
    markers: list[str] = []
    if module in BLOCKLU_REFRESH_ROWS:
        markers.append(BLOCKLU_MARKER)
    if chapter == "09" or module == "NumStability.Algorithms.HighamChapter9":
        markers.append(CH09_MARKER)
    if chapter == "11" or module == "NumStability.Algorithms.HighamChapter11":
        markers.append(CH11_MARKER)
    if module.startswith(NON_HIGHAM_PREFIX):
        markers.append(NON_HIGHAM_MARKER)
    if blockers:
        markers.append(BLOCKED_MARKER_PREFIX + blockers[0])
    return ";".join(markers) if markers else NO_DEPENDENCY


def chapter_of_source_family(family: str) -> str | None:
    match = SOURCE_FAMILY_RE.match(family)
    return family[-2:] if match else None
