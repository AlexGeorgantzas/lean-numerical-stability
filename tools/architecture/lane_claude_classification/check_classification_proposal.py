#!/usr/bin/env python3
"""Validate the Claude classification proposal against the frozen sources.

``--check`` (the default) proves every property the lane contract requires of
``classification/modules.tsv``:

structure
    frozen header, exactly one row per frozen module, no extras, unique,
    deterministically sorted, path/module agreement;
vocabulary
    allowed tier, confidence, and action values, and an action that the row's
    tier is permitted to carry;
evidence
    ``source_markers``, ``reusable_markers``, ``public_declaration_count`` and
    ``direct_project_imports`` are recomputed from the frozen Lean sources and
    must agree exactly, so no evidence column can be asserted by hand;
derived columns
    ``confidence``, ``required_action`` and ``cross_lane_dependency`` are
    recomputed from ``lane_policy`` and must agree exactly;
prose
    a nonempty rationale that names the proposed canonical family;
structural tiers
    ``aggregate``/``compatibility`` rows must be import-and-docstring-only and
    ``internal`` rows must have no public declarations;
dependency direction
    no proposed ``source``/``mixed_pending_split`` row may lie inside the
    transitive closure of an already-classified reusable module, and no
    proposed ``reusable`` row may reach a ``source``/``mixed`` module unless it
    is explicitly deferred and names its blocker;
summary
    ``summary.json`` must equal the deterministic derivation from the TSV.

``--self-test`` runs negative tests: every mutation of a minimal valid table
below must be rejected.  ``--write-summary`` regenerates ``summary.json``.

This checker never writes to a shared manifest and never modifies production
Lean sources.
"""

from __future__ import annotations

import argparse
import json
import sys
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import lane_policy
import module_evidence as me


ROOT = Path(__file__).resolve().parents[3]
PROPOSAL = ROOT / "docs/architecture/lane-proposals/claude-classification"
CLASSIFICATION = PROPOSAL / "classification"
MODULES_TSV = CLASSIFICATION / "modules.tsv"
INPUT_TSV = CLASSIFICATION / "input-modules.tsv"
SUMMARY_JSON = CLASSIFICATION / "summary.json"
TIERS = ROOT / "docs/architecture/tiers.json"

MANIFEST_TIER = {"mixed_pending_split": "mixed"}
MIN_RATIONALE = 80


class ProposalError(RuntimeError):
    pass


# --------------------------------------------------------------------------
# manifest helpers
# --------------------------------------------------------------------------
def load_manifest() -> dict:
    return json.loads(TIERS.read_text(encoding="utf-8"))


def existing_tier(module: str, manifest: dict) -> str | None:
    exact = manifest["exact"]
    if module in exact:
        return exact[module]
    prefixes = sorted(
        ((rule["prefix"], rule["tier"]) for rule in manifest["prefixes"]),
        key=lambda item: (-len(item[0]), item[0]),
    )
    for prefix, tier in prefixes:
        if module == prefix or module.startswith(prefix + "."):
            return tier
    return None


def production_import_graph() -> dict[str, tuple[str, ...]]:
    graph: dict[str, tuple[str, ...]] = {}
    paths = [ROOT / "NumStability.lean", *sorted((ROOT / "NumStability").rglob("*.lean"))]
    for path in paths:
        name = ".".join(path.relative_to(ROOT).with_suffix("").parts)
        code, _ = me.strip_comments(me.read_source(path))
        graph[name] = tuple(
            target
            for target in me.IMPORT_RE.findall(code)
            if target == "NumStability" or target.startswith("NumStability.")
        )
    return graph


def transitive(graph: dict[str, tuple[str, ...]], start: str) -> set[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        for target in graph.get(stack.pop(), ()):
            if target not in seen:
                seen.add(target)
                stack.append(target)
    return seen


# --------------------------------------------------------------------------
# validation
# --------------------------------------------------------------------------
def structural_failures(header: tuple[str, ...], rows: list[dict[str, str]],
                        expected: dict[str, str]) -> list[str]:
    failures: list[str] = []
    if header != lane_policy.PROPOSAL_HEADER:
        return [f"unexpected header {header}; expected {lane_policy.PROPOSAL_HEADER}"]
    modules = [row["module"] for row in rows]
    duplicates = sorted({name for name, count in Counter(modules).items() if count > 1})
    if duplicates:
        failures.append("duplicate proposal rows: " + ", ".join(duplicates))
    if modules != sorted(modules):
        failures.append("proposal rows are not sorted by module")
    missing = sorted(set(expected) - set(modules))
    extra = sorted(set(modules) - set(expected))
    if missing:
        failures.append(f"{len(missing)} frozen module(s) missing: " + ", ".join(missing[:8]))
    if extra:
        failures.append(f"{len(extra)} module(s) not in the frozen inventory: "
                        + ", ".join(extra[:8]))
    for row in rows:
        if row["module"] in expected and row["path"] != expected[row["module"]]:
            failures.append(
                f"{row['module']}: path {row['path']!r} disagrees with the frozen inventory "
                f"{expected[row['module']]!r}"
            )
    return failures


def action_wellformed(action: str, tier: str) -> str | None:
    if action.startswith(lane_policy.SPLIT_ACTION_PREFIX):
        if tier != "mixed_pending_split":
            return f"only mixed_pending_split rows may carry a split action, not {tier}"
        detail = action[len(lane_policy.SPLIT_ACTION_PREFIX):]
        if detail.count(" -> ") < 2 or ";" not in detail:
            return ("a split action must name at least two concrete destinations separated by "
                    "';' using ' -> '")
        return None
    if action not in lane_policy.SIMPLE_ACTIONS:
        return f"unknown required_action {action!r}"
    if tier == "mixed_pending_split":
        return "a mixed_pending_split row must carry a concrete plan_semantic_split action"
    if action not in lane_policy.ACTIONS_BY_TIER.get(tier, frozenset()):
        return f"tier {tier} may not carry action {action}"
    return None


def row_failures(
    row: dict[str, str],
    evidence: me.ModuleEvidence | None,
    blockers: list[str],
) -> list[str]:
    module, tier = row["module"], row["proposed_tier"]
    failures: list[str] = []
    if tier not in lane_policy.TIERS:
        failures.append(f"{module}: unknown proposed_tier {tier!r}")
        return failures
    if row["confidence"] not in lane_policy.CONFIDENCES:
        failures.append(f"{module}: unknown confidence {row['confidence']!r}")
    for column in ("source_markers", "reusable_markers", "rationale"):
        if not row[column].strip():
            failures.append(f"{module}: empty {column}")
    if len(row["rationale"]) < MIN_RATIONALE:
        failures.append(f"{module}: rationale is shorter than {MIN_RATIONALE} characters")
    family = row["proposed_canonical_family"]
    if not lane_policy.MODULE_RE.match(family):
        failures.append(f"{module}: proposed_canonical_family {family!r} is not a module name")
    if family not in row["rationale"] and row["required_action"].find(family) < 0:
        failures.append(f"{module}: rationale does not name {family}")
    if tier == "source" and not lane_policy.SOURCE_FAMILY_RE.match(family):
        failures.append(
            f"{module}: a source row must target NumStability.Source.Higham.ChapterNN, not {family}"
        )
    if tier == "reusable" and lane_policy.SOURCE_FAMILY_RE.match(family):
        failures.append(f"{module}: a reusable row may not target the source family {family}")

    problem = action_wellformed(row["required_action"], tier)
    if problem:
        failures.append(f"{module}: {problem}")

    if evidence is None:
        return failures

    checks = {
        "source_markers": evidence.source_markers(),
        "reusable_markers": evidence.reusable_markers(),
        "public_declaration_count": str(evidence.public_declaration_count),
        "direct_project_imports": str(evidence.direct_project_import_count),
    }
    for column, expected in checks.items():
        if row[column] != expected:
            failures.append(
                f"{module}: {column} is {row[column]!r} but the frozen source yields {expected!r}"
            )
    if evidence.has_placeholder:
        failures.append(f"{module}: source contains a sorry/admit placeholder")
    if tier in {"aggregate", "compatibility"} and not evidence.is_import_only:
        failures.append(f"{module}: a {tier} row must be import-and-docstring-only")
    if tier == "internal" and evidence.public_declaration_count:
        failures.append(f"{module}: an internal row must have no public declarations")

    located = sum(
        1
        for declaration in evidence.public_declarations
        if me.NAME_LOCATOR_RE.search(declaration.name)
        or me.PROCESS_WORD_RE.search(declaration.name)
    )
    expected_confidence = lane_policy.confidence(
        tier, evidence.public_declaration_count, located, bool(blockers), module
    )
    if row["confidence"] != expected_confidence:
        failures.append(
            f"{module}: confidence is {row['confidence']!r} but the policy derives "
            f"{expected_confidence!r}"
        )
    detail = row["required_action"][len(lane_policy.SPLIT_ACTION_PREFIX):] \
        if row["required_action"].startswith(lane_policy.SPLIT_ACTION_PREFIX) else ""
    expected_action = lane_policy.required_action(tier, bool(blockers), detail)
    if row["required_action"] != expected_action:
        failures.append(
            f"{module}: required_action is {row['required_action']!r} but the policy derives "
            f"{expected_action!r}"
        )
    expected_dependency = lane_policy.cross_lane_dependency(
        module, tier, lane_policy.chapter_of_source_family(family), blockers
    )
    if row["cross_lane_dependency"] != expected_dependency:
        failures.append(
            f"{module}: cross_lane_dependency is {row['cross_lane_dependency']!r} but the policy "
            f"derives {expected_dependency!r}"
        )
    return failures


def umbrella_failures(rows: list[dict[str, str]], manifest: dict,
                      graph: dict[str, tuple[str, ...]]) -> list[str]:
    """A proposed family may not be an existing declaration-bearing module.

    Relocating leaves under ``X`` while ``X.lean`` still owns declarations turns
    ``X.lean`` into a declaration-bearing umbrella beside a new ``X/`` directory,
    which ``check_layout.py`` counts as new legacy debt.
    """

    failures: list[str] = []
    structural = {"aggregate", "compatibility"}
    structural_rows = {row["module"] for row in rows if row["proposed_tier"] in structural}
    for family in sorted({row["proposed_canonical_family"] for row in rows}):
        parts = family.split(".")
        # The family node itself and every proper ancestor must be free to become
        # a directory: a declaration-bearing module at any of those paths would
        # become an umbrella once leaves are placed beneath it.
        candidates = [
            ".".join(parts[:length]) for length in range(2, len(parts) + 1)
        ]
        for node in candidates:
            if node not in graph or node in structural_rows:
                continue
            tier = existing_tier(node, manifest)
            if tier is None or tier in structural:
                continue
            detail = "" if node == family else f" (ancestor of {family})"
            failures.append(
                f"{node}: proposed as a canonical family{detail}, but the existing module "
                f"is {tier} and owns declarations; placing leaves beneath it would create "
                "a declaration-bearing umbrella"
            )
    return failures


def blocker_map(rows: list[dict[str, str]], manifest: dict,
                graph: dict[str, tuple[str, ...]]) -> dict[str, list[str]]:
    proposed = {row["module"]: row["proposed_tier"] for row in rows}

    def effective(module: str) -> str | None:
        tier = proposed.get(module)
        if tier is not None:
            return MANIFEST_TIER.get(tier, tier)
        return existing_tier(module, manifest)

    blockers: dict[str, list[str]] = {}
    for row in rows:
        if row["proposed_tier"] != "reusable":
            continue
        bad = sorted(
            target
            for target in transitive(graph, row["module"])
            if effective(target) in {"source", "mixed"}
        )
        if bad:
            blockers[row["module"]] = bad
    return blockers


def dependency_failures(rows: list[dict[str, str]], manifest: dict,
                        graph: dict[str, tuple[str, ...]],
                        blockers: dict[str, list[str]]) -> list[str]:
    failures: list[str] = []
    seeds = [name for name in graph if existing_tier(name, manifest) == "reusable"]
    seeds.extend(manifest.get("reusable_entrypoints", []))
    reachable: set[str] = set()
    stack = list(seeds)
    while stack:
        for target in graph.get(stack.pop(), ()):
            if target not in reachable:
                reachable.add(target)
                stack.append(target)
    for row in rows:
        module, tier = row["module"], row["proposed_tier"]
        if tier in {"source", "mixed_pending_split"} and module in reachable:
            failures.append(
                f"{module}: proposing {tier} would create a forbidden reusable-to-{tier} edge; "
                "the module is reachable from an already-classified reusable module"
            )
        if tier != "reusable":
            continue
        bad = blockers.get(module, [])
        if bad:
            marker = lane_policy.BLOCKED_MARKER_PREFIX + bad[0]
            if marker not in row["cross_lane_dependency"]:
                failures.append(
                    f"{module}: reusable row reaches {bad[0]} but does not carry {marker}"
                )
            if row["required_action"] != "defer_pending_upstream_split":
                failures.append(
                    f"{module}: reusable row reaches {bad[0]} and must be deferred"
                )
        elif lane_policy.BLOCKED_MARKER_PREFIX in row["cross_lane_dependency"]:
            failures.append(f"{module}: carries a blocked marker but its closure is clean")
    return failures


# --------------------------------------------------------------------------
# summary
# --------------------------------------------------------------------------
def build_summary(rows: list[dict[str, str]], expected: dict[str, str],
                  blockers: dict[str, list[str]]) -> dict:
    tiers = Counter(row["proposed_tier"] for row in rows)
    confidences = Counter(row["confidence"] for row in rows)
    actions = Counter(
        lane_policy.SPLIT_ACTION_PREFIX.strip()
        if row["required_action"].startswith(lane_policy.SPLIT_ACTION_PREFIX)
        else row["required_action"]
        for row in rows
    )
    dependencies: Counter[str] = Counter()
    for row in rows:
        for marker in row["cross_lane_dependency"].split(";"):
            if marker == lane_policy.NO_DEPENDENCY:
                continue
            key = (
                lane_policy.BLOCKED_MARKER_PREFIX.rstrip(":")
                if marker.startswith(lane_policy.BLOCKED_MARKER_PREFIX)
                else marker
            )
            dependencies[key] += 1
    split_queue = sorted(
        row["module"] for row in rows if row["proposed_tier"] == "mixed_pending_split"
    )
    families = Counter(row["proposed_canonical_family"] for row in rows)
    return {
        "schema_version": 1,
        "generated_from": "classification/modules.tsv",
        "frozen_base_sha": "6487fc33088523b8f27ecde9ad613515b78f9977",
        "input_inventory": {
            "path": "classification/input-modules.tsv",
            "rows": len(expected),
            "sha256": "C0B1C88F34461A44305D269C880F7581BDD7F1D9CC69CF9A144EA099C6A6DF54",
        },
        "rows": len(rows),
        "missing_modules": sorted(set(expected) - {row["module"] for row in rows}),
        "extra_modules": sorted({row["module"] for row in rows} - set(expected)),
        "tier_counts": dict(sorted(tiers.items())),
        "confidence_counts": dict(sorted(confidences.items())),
        "required_action_counts": dict(sorted(actions.items())),
        "cross_lane_dependency_counts": dict(sorted(dependencies.items())),
        "public_declaration_total": sum(int(row["public_declaration_count"]) for row in rows),
        "deferred_reusable_rows": sorted(blockers),
        "split_queue": split_queue,
        "split_queue_size": len(split_queue),
        "proposed_canonical_families": dict(sorted(families.items())),
    }


# --------------------------------------------------------------------------
# self-test
# --------------------------------------------------------------------------
VALID_ROW = {
    "module": "NumStability.Demo.Alpha",
    "path": "NumStability/Demo/Alpha.lean",
    "proposed_tier": "source",
    "confidence": "high",
    "source_markers": "name_locator=Ch01;located_declarations=1",
    "reusable_markers": "neutral_public_declarations=0",
    "public_declaration_count": "1",
    "direct_project_imports": "0",
    "required_action": "plan_source_extraction",
    "proposed_canonical_family": "NumStability.Source.Higham.Chapter01",
    "cross_lane_dependency": "none",
    "rationale": (
        "Numbered Higham Chapter 01 correspondence proposed for "
        "NumStability.Source.Higham.Chapter01 with an import-only wrapper preserved."
    ),
}


def self_test() -> list[str]:
    problems: list[str] = []
    expected = {VALID_ROW["module"]: VALID_ROW["path"]}

    def structure(rows):
        return structural_failures(lane_policy.PROPOSAL_HEADER, rows, expected)

    if structure([dict(VALID_ROW)]):
        problems.append("the reference row must pass the structural checks")
    if not structure([]):
        problems.append("a missing frozen module must be rejected")
    if not structure([dict(VALID_ROW), dict(VALID_ROW)]):
        problems.append("a duplicate row must be rejected")
    if not structure([dict(VALID_ROW), dict(VALID_ROW, module="NumStability.Demo.Beta",
                                            path="NumStability/Demo/Beta.lean")]):
        problems.append("a row outside the frozen inventory must be rejected")
    unsorted_rows = [
        dict(VALID_ROW, module="NumStability.Demo.Zeta", path="NumStability/Demo/Zeta.lean"),
        dict(VALID_ROW),
    ]
    if not structural_failures(lane_policy.PROPOSAL_HEADER, unsorted_rows,
                               {row["module"]: row["path"] for row in unsorted_rows}):
        problems.append("unsorted rows must be rejected")
    if not structure([dict(VALID_ROW, path="NumStability/Demo/Other.lean")]):
        problems.append("a path that disagrees with the inventory must be rejected")
    if not structural_failures(("module",), [dict(VALID_ROW)], expected):
        problems.append("a wrong header must be rejected")

    def row_only(**changes):
        return row_failures(dict(VALID_ROW, **changes), None, [])

    if row_only():
        problems.append("the reference row must pass the vocabulary checks")
    if not row_only(proposed_tier="wonderful"):
        problems.append("an unknown tier must be rejected")
    if not row_only(confidence="certain"):
        problems.append("an unknown confidence must be rejected")
    if not row_only(rationale=""):
        problems.append("an empty rationale must be rejected")
    if not row_only(rationale="too short"):
        problems.append("a short rationale must be rejected")
    if not row_only(source_markers=" "):
        problems.append("empty source markers must be rejected")
    if not row_only(required_action="do_something"):
        problems.append("an unknown action must be rejected")
    if not row_only(required_action="plan_reusable_relocation"):
        problems.append("a source row with a reusable relocation action must be rejected")
    if not row_only(proposed_tier="mixed_pending_split",
                    required_action="plan_source_extraction"):
        problems.append("a mixed row without a split action must be rejected")
    if not row_only(proposed_tier="mixed_pending_split",
                    required_action="plan_semantic_split: everything"):
        problems.append("a split action without concrete destinations must be rejected")
    if not row_only(proposed_canonical_family="not a module"):
        problems.append("a malformed canonical family must be rejected")
    if not row_only(proposed_canonical_family="NumStability.Algorithms.Foo"):
        problems.append("a source row outside the Source.Higham family must be rejected")
    if not row_only(proposed_tier="reusable",
                    required_action="plan_reusable_relocation"):
        problems.append("a reusable row targeting a source family must be rejected")

    manifest = {"exact": {"NumStability.Demo.Src": "source"}, "prefixes": [],
                "reusable_entrypoints": []}
    graph = {
        "NumStability.Demo.Alpha": ("NumStability.Demo.Src",),
        "NumStability.Demo.Src": (),
    }
    reusable_row = dict(
        VALID_ROW,
        proposed_tier="reusable",
        proposed_canonical_family="NumStability.Demo.Canonical",
        rationale="Source-neutral reusable content proposed for NumStability.Demo.Canonical "
                  "once its blocker is split; recorded for review.",
        required_action="plan_reusable_relocation",
        cross_lane_dependency="none",
    )
    blockers = blocker_map([reusable_row], manifest, graph)
    if blockers.get("NumStability.Demo.Alpha") != ["NumStability.Demo.Src"]:
        problems.append("the blocker map must find a reusable-to-source path")
    if not dependency_failures([reusable_row], manifest, graph, blockers):
        problems.append("an undeferred reusable row that reaches source must be rejected")
    deferred = dict(
        reusable_row,
        confidence="medium",
        required_action="defer_pending_upstream_split",
        cross_lane_dependency=lane_policy.BLOCKED_MARKER_PREFIX + "NumStability.Demo.Src",
    )
    if dependency_failures([deferred], manifest, graph,
                           blocker_map([deferred], manifest, graph)):
        problems.append("a correctly deferred reusable row must be accepted")
    clean_graph = {"NumStability.Demo.Alpha": ()}
    if not dependency_failures([deferred], manifest, clean_graph,
                               blocker_map([deferred], manifest, clean_graph)):
        problems.append("a clean reusable row carrying a blocked marker must be rejected")
    umbrella_manifest = {
        "exact": {"NumStability.Demo.Owner": "reusable",
                  "NumStability.Demo.Agg": "aggregate"},
        "prefixes": [], "reusable_entrypoints": [],
    }
    umbrella_graph = {"NumStability.Demo.Owner": (), "NumStability.Demo.Agg": ()}
    owner_row = dict(
        VALID_ROW,
        proposed_tier="reusable",
        proposed_canonical_family="NumStability.Demo.Owner",
        required_action="plan_reusable_relocation",
        rationale="Reusable content proposed for relocation under NumStability.Demo.Owner "
                  "which already owns declarations; recorded for review.",
    )
    if not umbrella_failures([owner_row], umbrella_manifest, umbrella_graph):
        problems.append(
            "a family that is an existing declaration-bearing module must be rejected"
        )
    if umbrella_failures([dict(owner_row, proposed_canonical_family="NumStability.Demo.Agg")],
                         umbrella_manifest, umbrella_graph):
        problems.append("an existing aggregate family must be accepted")

    seeded = {"exact": {"NumStability.Demo.Reu": "reusable"}, "prefixes": [],
              "reusable_entrypoints": []}
    seeded_graph = {
        "NumStability.Demo.Reu": ("NumStability.Demo.Alpha",),
        "NumStability.Demo.Alpha": (),
    }
    if not dependency_failures([dict(VALID_ROW)], seeded, seeded_graph, {}):
        problems.append(
            "a source row inside the classified-reusable closure must be rejected"
        )
    return problems


# --------------------------------------------------------------------------
def run_check(write_summary: bool) -> int:
    _, input_rows = me.read_tsv(INPUT_TSV)
    expected = {row["module"]: row["path"] for row in input_rows}
    header, rows = me.read_tsv(MODULES_TSV)

    failures = structural_failures(header, rows, expected)
    if failures:
        for failure in failures:
            print(f"ERROR: {failure}", file=sys.stderr)
        return 1

    manifest = load_manifest()
    graph = production_import_graph()
    blockers = blocker_map(rows, manifest, graph)

    for row in rows:
        evidence = me.evidence_for(ROOT, row["path"])
        failures.extend(row_failures(row, evidence, blockers.get(row["module"], [])))
    failures.extend(dependency_failures(rows, manifest, graph, blockers))
    failures.extend(umbrella_failures(rows, manifest, graph))

    summary = build_summary(rows, expected, blockers)
    if write_summary:
        SUMMARY_JSON.write_text(
            json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )
        print(f"Wrote {SUMMARY_JSON.relative_to(ROOT)}")
    elif not SUMMARY_JSON.is_file():
        failures.append("missing classification/summary.json")
    else:
        recorded = json.loads(SUMMARY_JSON.read_text(encoding="utf-8"))
        if recorded != summary:
            failures.append(
                "summary.json is not the deterministic derivation of modules.tsv; "
                "regenerate it with --write-summary"
            )

    if failures:
        for failure in failures:
            print(f"ERROR: {failure}", file=sys.stderr)
        return 1
    print(
        f"Proposal verified: {len(rows)} rows, "
        + ", ".join(f"{tier}={count}" for tier, count in sorted(summary["tier_counts"].items()))
        + f"; deferred reusable rows={len(blockers)}; split queue={summary['split_queue_size']}."
    )
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="validate the proposal (default)")
    parser.add_argument("--self-test", action="store_true", help="run the negative checker tests")
    parser.add_argument("--write-summary", action="store_true",
                        help="regenerate classification/summary.json from the TSV")
    args = parser.parse_args()
    if args.self_test:
        problems = self_test()
        if problems:
            for problem in problems:
                print(f"ERROR: self-test: {problem}", file=sys.stderr)
            return 1
        print("Checker self-test passed: every rejection case is detected.")
        return 0
    return run_check(args.write_summary)


if __name__ == "__main__":
    raise SystemExit(main())
