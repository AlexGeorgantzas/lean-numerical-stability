#!/usr/bin/env python3
"""Enforce the reviewed version-2 tier rule manifest (TIER-01).

The manifest at docs/architecture/tiers.json carries, for every exact and prefix
rule, a stable rule id, match kind, role, rationale, introduction commit and
date, reviewer, status, review date, evidence reference, and an optional reviewed
exception. This tool enforces the resolution contract the closeout plan states:

  1. exact rules are consulted before prefix rules, and an exact rule whose role
     differs from its enclosing prefix must name that prefix in `override_of`;
  2. prefix matching is component-boundary aware: `A.B` matches `A.B` and
     `A.B.C`, never `A.BC`;
  3. all matching prefixes are collected, and equally specific rules that
     disagree about the role are a failure rather than a silent choice;
  4. an exact rule agreeing with its enclosing prefix must say `extends`, so a
     redundant row is deliberate rather than accidental;
  5. stale rules fail: an exact rule whose file is absent, or a prefix rule that
     decides no module and is not a reviewed exception;
  6. every production module resolves exactly once, and `mixed` stays empty;
  7. every rule carries complete review metadata;
  8. the resolved role map equals the map recorded in `counts.by_role`, so the
     manifest cannot drift from the tree it describes.

usage: python check_tiers.py [--self-test]
"""
from __future__ import annotations

import collections
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
TIERS = "docs/architecture/tiers.json"
REQUIRED_RULE_FIELDS = ("rule_id", "match_kind", "role", "rationale", "introduction", "review")
REQUIRED_REVIEW_FIELDS = ("reviewer", "status", "review_date", "evidence")
ROLES = ("reusable", "source", "internal", "upstream", "mixed", "compatibility", "aggregate")


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def production_modules(root: Path) -> list[str]:
    out = subprocess.run(["git", "ls-files", "NumStability/*.lean", "NumStability.lean"],
                         cwd=root, capture_output=True, text=True, encoding="utf-8").stdout
    return sorted(p[:-5].replace("/", ".") for p in out.split("\n") if p.endswith(".lean"))


def matching_prefixes(module: str, prefixes: dict[str, str]) -> list[tuple[str, str]]:
    """Component-boundary-aware matches, longest first."""
    hits = [(p, r) for p, r in prefixes.items() if module == p or module.startswith(p + ".")]
    return sorted(hits, key=lambda pr: -len(pr[0]))


def resolve(module: str, exact: dict[str, str], prefixes: dict[str, str]) -> tuple[str, str]:
    """(role, deciding rule id). Raises on equally specific disagreement."""
    if module in exact:
        return exact[module], f"exact:{module}"
    hits = matching_prefixes(module, prefixes)
    if not hits:
        return "unclassified", "none"
    longest = len(hits[0][0])
    tied = [h for h in hits if len(h[0]) == longest]
    roles = {r for _, r in tied}
    if len(roles) > 1:
        raise ValueError(f"{module}: equally specific prefix rules disagree: {sorted(roles)}")
    return tied[0][1], f"prefix:{tied[0][0]}"


def validate(root: Path, manifest: dict, modules: list[str]) -> list[str]:
    failures: list[str] = []
    if manifest.get("schema_version") != 2:
        return [f"{TIERS}: schema_version must be 2 for the reviewed rule manifest"]

    exact = manifest.get("exact") or {}
    prefixes = {r["prefix"]: r["tier"] for r in manifest.get("prefixes") or []}
    exact_rules = {r.get("rule_id"): r for r in manifest.get("exact_rules") or []}
    prefix_rules = {r.get("rule_id"): r for r in manifest.get("prefix_rules") or []}

    resolution = manifest.get("resolution") or {}
    for key, want in (("order", ["exact", "prefix"]),
                      ("prefix_match", "component_boundary"),
                      ("conflicting_equal_specificity", "fail"),
                      ("unclassified", "fail"),
                      ("mixed_allowed", False)):
        if resolution.get(key) != want:
            failures.append(f"{TIERS}: resolution.{key} must be {want!r}")

    # rule records: completeness, role validity, and agreement with the flat tables
    if len(exact_rules) != len(exact):
        failures.append(f"{TIERS}: {len(exact_rules)} exact rule records for {len(exact)} exact entries")
    if len(prefix_rules) != len(prefixes):
        failures.append(f"{TIERS}: {len(prefix_rules)} prefix rule records for {len(prefixes)} prefix entries")

    for rid, rule in sorted(exact_rules.items()) + sorted(prefix_rules.items()):
        missing = [f for f in REQUIRED_RULE_FIELDS if f not in rule]
        if missing:
            failures.append(f"{TIERS}: rule {rid} lacks {missing}")
            continue
        if rule["role"] not in ROLES:
            failures.append(f"{TIERS}: rule {rid} has unknown role {rule['role']!r}")
        review = rule.get("review") or {}
        absent = [f for f in REQUIRED_REVIEW_FIELDS if not review.get(f)]
        if absent:
            failures.append(f"{TIERS}: rule {rid} review lacks {absent}")
        intro = rule.get("introduction") or {}
        if not intro.get("commit") or not intro.get("date"):
            failures.append(f"{TIERS}: rule {rid} introduction needs commit and date")

    # rule 1 and 4: overrides and extensions must be declared
    for rid, rule in sorted(exact_rules.items()):
        module = rule.get("module")
        if module is None:
            continue
        hits = matching_prefixes(module, prefixes)
        if not hits:
            if "override_of" in rule or "extends" in rule:
                failures.append(f"{TIERS}: {rid} declares a relationship but matches no prefix")
            continue
        enclosing, enclosing_role = hits[0]
        if enclosing_role != rule["role"]:
            if rule.get("override_of") != f"prefix:{enclosing}":
                failures.append(
                    f"{TIERS}: {rid} differs from prefix {enclosing} ({enclosing_role}) "
                    f"and must declare override_of"
                )
            elif not rule.get("override_rationale"):
                failures.append(f"{TIERS}: {rid} overrides {enclosing} without a rationale")
        elif rule.get("extends") != f"prefix:{enclosing}":
            failures.append(f"{TIERS}: {rid} agrees with prefix {enclosing} and must declare extends")

    # rule 5: stale rules
    for rid, rule in sorted(exact_rules.items()):
        module = rule.get("module")
        if module and not (root / (module.replace(".", "/") + ".lean")).is_file():
            failures.append(f"{TIERS}: {rid} classifies an absent file")

    # rule 6 and 8: total, unambiguous resolution matching the recorded census
    decided: collections.Counter = collections.Counter()
    roles: collections.Counter = collections.Counter()
    for module in modules:
        try:
            role, rid = resolve(module, exact, prefixes)
        except ValueError as error:
            failures.append(f"{TIERS}: {error}")
            continue
        decided[rid] += 1
        roles[role] += 1
    if roles.get("unclassified"):
        failures.append(f"{TIERS}: {roles['unclassified']} production module(s) resolve to no rule")
    if roles.get("mixed"):
        failures.append(f"{TIERS}: mixed must be empty, found {roles['mixed']}")

    recorded = (manifest.get("counts") or {}).get("by_role") or {}
    measured = {k: v for k, v in roles.items() if v}
    if recorded != measured:
        failures.append(f"{TIERS}: counts.by_role {recorded} disagrees with the resolved map {measured}")
    if (manifest.get("counts") or {}).get("production_modules") != len(modules):
        failures.append(f"{TIERS}: counts.production_modules must equal {len(modules)}")

    idle = sorted(p for p in prefixes if decided.get(f"prefix:{p}", 0) == 0)
    reviewed_idle = {c.get("rule_id") for c in manifest.get("reviewed_corrections") or []}
    for prefix in idle:
        rid = f"prefix:{prefix}"
        rule = prefix_rules.get(rid) or {}
        if rid not in reviewed_idle and not rule.get("exception"):
            failures.append(
                f"{TIERS}: prefix rule {rid} decides no module and carries no reviewed record"
            )
    return failures


def self_test() -> list[str]:
    failures: list[str] = []
    prefixes = {"A.B": "source", "A.B.C": "reusable"}
    if resolve("A.B.C.D", {}, prefixes) != ("reusable", "prefix:A.B.C"):
        failures.append("self-test: the longest matching prefix must decide")
    if resolve("A.BC", {}, prefixes) != ("unclassified", "none"):
        failures.append("self-test: prefix matching must respect component boundaries")
    if resolve("A.B.C", {"A.B.C": "internal"}, prefixes) != ("internal", "exact:A.B.C"):
        failures.append("self-test: an exact rule must precede prefix rules")
    # a manifest whose recorded census disagrees with the tree must fail
    bad = {
        "schema_version": 2,
        "exact": {"NumStability.X": "source"},
        "prefixes": [],
        "exact_rules": [{
            "rule_id": "exact:NumStability.X", "match_kind": "exact", "module": "NumStability.X",
            "role": "source", "rationale": "r", "introduction": {"commit": "0" * 40, "date": "2026-01-01T00:00:00Z"},
            "review": {"reviewer": "primary-human", "status": "accepted", "review_date": "2026-01-01T00:00:00Z", "evidence": "e"},
        }],
        "prefix_rules": [],
        "resolution": {"order": ["exact", "prefix"], "prefix_match": "component_boundary",
                       "conflicting_equal_specificity": "fail", "unclassified": "fail", "mixed_allowed": False},
        "counts": {"by_role": {"source": 99}, "production_modules": 1},
    }
    problems = validate(ROOT, bad, ["NumStability.X"])
    if not any("disagrees with the resolved map" in p for p in problems):
        failures.append("self-test: a census disagreeing with the resolved map must fail")
    if not any("classifies an absent file" in p for p in problems):
        failures.append("self-test: an exact rule for an absent file must fail")
    return failures


def main(argv: list[str]) -> int:
    if "--self-test" in argv:
        problems = self_test()
        if problems:
            for problem in problems:
                print(f"error: {problem}", file=sys.stderr)
            return 1
        print("tier manifest self-test passed: precedence, boundary matching, "
              "census agreement and stale-rule rejection")
        return 0
    manifest = load(ROOT / TIERS)
    modules = production_modules(ROOT)
    problems = self_test() + validate(ROOT, manifest, modules)
    if problems:
        for problem in problems:
            print(f"error: {problem}", file=sys.stderr)
        return 1
    counts = manifest["counts"]
    print(f"tier contract passed: {counts['production_modules']} production modules, "
          f"{counts['exact_rules']} exact and {counts['prefix_rules']} prefix rules, "
          f"roles {counts['by_role']}, mixed 0, unclassified 0")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
