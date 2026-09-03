#!/usr/bin/env python3
"""Verify the documented old-to-new Lean module forwarding contract."""

from __future__ import annotations

import collections
import json
import tempfile
import re
import sys
from pathlib import Path

from generate_baseline import IMPORT_RE, module_name, remove_lean_comments, source_paths


ROOT = Path(__file__).resolve().parents[2]
POLICY = ROOT / "docs" / "architecture" / "COMPATIBILITY.md"
IMPORT_LINE_RE = re.compile(
    r"(?m)^[ \t]*(?:(?:public|private|meta)\s+)*import[ \t]+[^\r\n]+(?:\r?\n|$)"
)

def module_path(name: str) -> Path:
    return ROOT / Path(*name.split(".")).with_suffix(".lean")


def documented_mappings() -> dict[str, tuple[str, ...]]:
    mappings: dict[str, tuple[str, ...]] = {}
    for line in POLICY.read_text(encoding="utf-8").splitlines():
        if not line.startswith("|"):
            continue
        names = re.findall(r"`(NumStability(?:\.[A-Za-z0-9_']+)+)`", line)
        if len(names) < 2:
            continue
        historical, *canonical = names
        if historical in mappings:
            raise ValueError(f"duplicate compatibility row: {historical}")
        mappings[historical] = tuple(canonical)
    if not mappings:
        raise ValueError(f"no compatibility mappings found in {POLICY}")
    return mappings


def production_import_failures(
    production_import_edges: set[tuple[str, str]],
) -> list[str]:
    return [
        f"{name}: production import uses historical path {target}"
        for name, target in sorted(production_import_edges)
    ]


def self_test_zero_production_imports() -> None:
    assert not production_import_failures(set())

    adversarial_edge = (
        "NumStability.Source.Higham.Chapter19.Core",
        "NumStability.Algorithms.LinearSystems.QR.HouseholderQRSupport",
    )
    assert production_import_failures({adversarial_edge}) == [
        "NumStability.Source.Higham.Chapter19.Core: production import uses "
        "historical path "
        "NumStability.Algorithms.LinearSystems.QR.HouseholderQRSupport"
    ]

    second_adversarial_edge = (
        "NumStability.Source.Higham.Chapter19.Unreviewed",
        "NumStability.Algorithms.LinearSystems.QR.HouseholderSpecSupport",
    )
    assert len(
        production_import_failures({adversarial_edge, second_adversarial_edge})
    ) == 2


MANIFEST_PATH = "docs/architecture/compatibility.json"
REMOVAL_POLICY_ID = "no_removal_in_this_migration"
MANIFEST_REQUIRED_FIELDS = (
    "canonical_only_smoke_test",
    "canonical_targets",
    "historical_module",
    "import_only",
    "introduction",
    "old_only_smoke_test",
    "removal_policy",
    "review",
    "wrapper_shape",
)


def resolve_historical(module: str, exact: dict, prefixes: dict) -> tuple[str, ...]:
    """Resolve a historical module to canonical targets.

    Exact rules precede prefix rules; among prefix rules the longest wins.

    Two distinct dot-aligned prefix rules cannot both match at the same length:
    each would be a dot-aligned prefix of the module, so one must be a prefix of
    the other and thus shorter. The invariant is asserted rather than defended
    with a branch that can never run.
    """

    if module in exact:
        return tuple(exact[module])
    matches = [p for p in prefixes if module == p or module.startswith(p + ".")]
    if not matches:
        return ()
    longest = max(len(p) for p in matches)
    winners = [p for p in matches if len(p) == longest]
    assert len(winners) == 1, f"unreachable: equal-length prefix rules {winners} both match {module}"
    return tuple(prefixes[winners[0]])


def validate_manifest(root: Path, documented: dict) -> list[str]:
    """Validate the COMP-01 machine-readable compatibility manifest."""

    failures: list[str] = []
    path = root / MANIFEST_PATH
    if not path.is_file():
        return [f"missing compatibility manifest {MANIFEST_PATH}"]
    try:
        doc = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        return [f"cannot read {MANIFEST_PATH}: {error}"]

    if doc.get("schema_version") != 1:
        failures.append(f"{MANIFEST_PATH}: schema_version must be 1")
    if doc.get("rule_precedence") != ["exact", "prefix"]:
        failures.append(f"{MANIFEST_PATH}: rule_precedence must be exact before prefix")
    if doc.get("ambiguous_match") != "fail":
        failures.append(f"{MANIFEST_PATH}: ambiguous_match must be fail")
    policy = doc.get("removal_policy") or {}
    if policy.get("id") != REMOVAL_POLICY_ID:
        failures.append(f"{MANIFEST_PATH}: removal policy id must be {REMOVAL_POLICY_ID}")

    records = doc.get("paths")
    if not isinstance(records, list):
        return failures + [f"{MANIFEST_PATH}: paths must be a list"]

    seen: set[str] = set()
    for record in records:
        if not isinstance(record, dict):
            failures.append(f"{MANIFEST_PATH}: every path record must be an object")
            continue
        name = record.get("historical_module")
        missing = [f for f in MANIFEST_REQUIRED_FIELDS if f not in record]
        if missing:
            failures.append(f"{MANIFEST_PATH}: {name} lacks field(s) {missing}")
            continue
        if name in seen:
            failures.append(f"{MANIFEST_PATH}: {name} recorded twice: ambiguous")
        seen.add(name)
        if name not in documented:
            failures.append(f"{MANIFEST_PATH}: {name} is not a documented historical path")
            continue
        if tuple(record["canonical_targets"]) != tuple(documented[name]):
            failures.append(f"{MANIFEST_PATH}: {name} targets disagree with COMPATIBILITY.md")
        expected_shape = "single_target" if len(documented[name]) == 1 else "aggregate_target_set"
        if record["wrapper_shape"] != expected_shape:
            failures.append(f"{MANIFEST_PATH}: {name} wrapper_shape must be {expected_shape}")
        if record["import_only"] is not True:
            failures.append(f"{MANIFEST_PATH}: {name} must be import-only")
        if record["removal_policy"] != REMOVAL_POLICY_ID:
            failures.append(f"{MANIFEST_PATH}: {name} removal_policy must be {REMOVAL_POLICY_ID}")
        review = record.get("review") or {}
        if not review.get("status") or not review.get("reviewer"):
            failures.append(f"{MANIFEST_PATH}: {name} review needs status and reviewer")
        intro = record.get("introduction") or {}
        if not intro.get("commit") or not intro.get("date"):
            failures.append(f"{MANIFEST_PATH}: {name} introduction needs commit and date")

    absent = sorted(set(documented) - seen)
    if absent:
        failures.append(
            f"{MANIFEST_PATH}: {len(absent)} documented path(s) absent from the manifest, "
            f"first: {absent[:3]}"
        )
    counts = doc.get("counts") or {}
    if counts.get("historical_modules") != len(records):
        failures.append(f"{MANIFEST_PATH}: counts.historical_modules must equal the record count")
    return failures


def self_test_manifest_contract() -> list[str]:
    """Exercise precedence, longest-prefix, no-match, and the real ambiguity."""

    failures: list[str] = []
    exact = {"A.B.C": ("Canon.Exact",)}
    prefixes = {"A.B": ("Canon.Short",), "A.B.C": ("Canon.Long",)}
    if resolve_historical("A.B.C", exact, prefixes) != ("Canon.Exact",):
        failures.append("self-test: an exact rule must precede prefix rules")
    if resolve_historical("A.B.C.D", {}, prefixes) != ("Canon.Long",):
        failures.append("self-test: the longest matching prefix must win")
    if resolve_historical("A.B.X", {}, prefixes) != ("Canon.Short",):
        failures.append("self-test: a shorter prefix must still match when the longer does not")
    if resolve_historical("Z.Y", exact, prefixes) != ():
        failures.append("self-test: a module matching nothing must resolve to no targets")
    if resolve_historical("A.BC", {}, prefixes) != ():
        failures.append("self-test: prefix matching must be dot-aligned, not textual")

    # The ambiguity that can actually occur: one historical module, two records.
    duplicated = {
        "schema_version": 1,
        "rule_precedence": ["exact", "prefix"],
        "ambiguous_match": "fail",
        "removal_policy": {"id": REMOVAL_POLICY_ID},
        "counts": {"historical_modules": 2},
        "paths": [
            {
                "historical_module": "Old.Path",
                "canonical_targets": ["New.Path"],
                "wrapper_shape": "single_target",
                "import_only": True,
                "introduction": {"commit": "0" * 40, "date": "2026-01-01T00:00:00+00:00"},
                "old_only_smoke_test": None,
                "canonical_only_smoke_test": None,
                "removal_policy": REMOVAL_POLICY_ID,
                "review": {"status": "accepted", "reviewer": "primary-human"},
            }
        ] * 2,
    }
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        (root / "docs" / "architecture").mkdir(parents=True)
        (root / MANIFEST_PATH).write_text(json.dumps(duplicated), encoding="utf-8")
        problems = validate_manifest(root, {"Old.Path": ("New.Path",)})
    if not any("recorded twice" in p for p in problems):
        failures.append("self-test: a duplicated historical module must be rejected as ambiguous")
    return failures


ISOLATION_COMMAND_RE = re.compile(r"^\s*#(check|print|eval|guard|reduce)\b", re.M)
CHECKED_NAME_RE = re.compile(r"#(?:check|print)\s+@?([A-Za-z_][A-Za-z0-9_'.]*)")
# A declaration keyword may stand alone on its line with the name following, so
# the name is matched across at most one newline. A line-only pattern misses
# roughly a hundred long-named theorems in this repository.
DECLARATION_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+|private\s+|protected\s+)*"
    r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)\b[ \t]*\r?\n?[ \t]*"
    r"([A-Za-z_][A-Za-z0-9_'.]*)", re.M)
NAMESPACE_RE = re.compile(r"^namespace\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.M)
NAMESPACE_END_RE = re.compile(r"^end\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.M)


def isolation_coverage(root: Path) -> dict[str, tuple[str, frozenset]]:
    """Modules covered by a strict single-import, declaration-bearing test file.

    Returns module -> (covering test module, declarations that file checks).
    """

    covered: dict[str, tuple[str, frozenset]] = {}
    for path in sorted((root / "NumStabilityTest").rglob("*.lean")):
        text = remove_lean_comments(path.read_text(encoding="utf-8-sig", errors="replace"))
        imports = IMPORT_RE.findall(text)
        if len(imports) != 1 or not ISOLATION_COMMAND_RE.search(text):
            continue
        covered.setdefault(
            imports[0],
            (module_name(path.relative_to(root)), frozenset(CHECKED_NAME_RE.findall(text))),
        )
    return covered


def declarations_in(root: Path, module: str) -> set[str]:
    """Public declaration names a module declares, namespace-qualified."""

    path = root / (module.replace(".", "/") + ".lean")
    if not path.is_file():
        return set()
    body = remove_lean_comments(path.read_text(encoding="utf-8", errors="replace"))
    lines = body.split("\n")
    names: set[str] = set()
    stack: list[str] = []
    for index, line in enumerate(lines):
        opened = NAMESPACE_RE.match(line)
        if opened:
            stack.append(opened.group(1))
            continue
        closed = NAMESPACE_END_RE.match(line)
        if closed and stack and stack[-1] == closed.group(1):
            stack.pop()
            continue
        chunk = line + "\n" + (lines[index + 1] if index + 1 < len(lines) else "")
        found = DECLARATION_RE.match(chunk)
        if found:
            names.add(".".join(stack + [found.group(1)]) if stack else found.group(1))
    return names


def declaration_closure(root: Path, modules: list[str], budget: int = 400) -> set[str]:
    """Declarations reachable by importing `modules`, bounded for CI cost."""

    seen: set[str] = set()
    queue = collections.deque(modules)
    names: set[str] = set()
    while queue and len(seen) < budget:
        current = queue.popleft()
        if current in seen:
            continue
        seen.add(current)
        names |= declarations_in(root, current)
        path = root / (current.replace(".", "/") + ".lean")
        if path.is_file():
            text = path.read_text(encoding="utf-8", errors="replace")
            for match in re.finditer(r"^import\s+(NumStability\S*)", text, re.M):
                queue.append(match.group(1))
    return names


def isolation_failures(root: Path, mappings: dict) -> list[str]:
    """Enforce per-file isolation coverage and old/canonical declaration consistency."""

    failures: list[str] = []
    covered = isolation_coverage(root)
    historical = set(mappings)
    targets = {target for values in mappings.values() for target in values}

    uncovered_historical = sorted(historical - set(covered))
    uncovered_canonical = sorted(targets - set(covered))
    if uncovered_historical:
        failures.append(
            f"{len(uncovered_historical)} historical path(s) lack a strict single-import "
            f"declaration-bearing test, first: {uncovered_historical[:3]}"
        )
    if uncovered_canonical:
        failures.append(
            f"{len(uncovered_canonical)} canonical target(s) lack a strict single-import "
            f"declaration-bearing test, first: {uncovered_canonical[:3]}"
        )

    inconsistent: list[str] = []
    for historical_module, canonical in sorted(mappings.items()):
        if historical_module not in covered:
            continue
        old_checked = covered[historical_module][1]
        if not old_checked:
            continue
        union: frozenset = frozenset()
        for target in canonical:
            if target in covered:
                union |= covered[target][1]
        if not union:
            continue
        if old_checked & union:
            continue
        if old_checked & declaration_closure(root, list(canonical)):
            continue
        inconsistent.append(historical_module)
    if inconsistent:
        failures.append(
            f"{len(inconsistent)} forwarding pair(s) check declarations the canonical "
            f"target does not provide, first: {inconsistent[:3]}"
        )
    return failures


def self_test_isolation_rules() -> list[str]:
    """Prove that a multi-import test does not count and that a strict one does."""

    failures: list[str] = []
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        tests = root / "NumStabilityTest" / "Fixture"
        tests.mkdir(parents=True)
        (tests / "Multi.lean").write_text(
            "import NumStability.Old\nimport NumStability.Other\n#check @Some.Decl\n",
            encoding="utf-8",
        )
        if "NumStability.Old" in isolation_coverage(root):
            failures.append("self-test: a multi-import test must not establish isolation")
        (tests / "Bare.lean").write_text("import NumStability.Bare\n", encoding="utf-8")
        if "NumStability.Bare" in isolation_coverage(root):
            failures.append("self-test: an import-only test must not establish isolation")
        (tests / "Strict.lean").write_text(
            "import NumStability.Strict\n#check @Some.Decl\n", encoding="utf-8"
        )
        covered = isolation_coverage(root)
        if "NumStability.Strict" not in covered:
            failures.append("self-test: a strict declaration-bearing test must establish isolation")
        elif covered["NumStability.Strict"][1] != frozenset({"Some.Decl"}):
            failures.append("self-test: the checked declaration must be recorded")

        # a declaration keyword alone on its line must still be found
        lib = root / "NumStability"
        lib.mkdir(exist_ok=True)
        (lib / "Wrapped.lean").write_text(
            "namespace NumStability\n\ntheorem\n    long_name_on_the_next_line\n"
            "    (h : True) : True := h\n\nend NumStability\n",
            encoding="utf-8",
        )
        if "NumStability.long_name_on_the_next_line" not in declarations_in(root, "NumStability.Wrapped"):
            failures.append("self-test: a name on the line after its keyword must be found")
    return failures


def main() -> int:
    try:
        self_test_zero_production_imports()
    except AssertionError as error:
        print(f"error: compatibility checker self-test failed: {error}", file=sys.stderr)
        return 2

    try:
        mappings = documented_mappings()
    except (OSError, ValueError) as error:
        print(f"error: {error}", file=sys.stderr)
        return 2

    failures: list[str] = []
    failures.extend(self_test_manifest_contract())
    failures.extend(validate_manifest(ROOT, documented_mappings()))

    tier_manifest_path = ROOT / "docs" / "architecture" / "tiers.json"
    try:
        tier_manifest = json.loads(tier_manifest_path.read_text(encoding="utf-8"))
        tier_compatibility = {
            name
            for name, tier in tier_manifest.get("exact", {}).items()
            if tier == "compatibility"
        }
        if tier_compatibility != set(mappings):
            missing = sorted(tier_compatibility - set(mappings))
            extra = sorted(set(mappings) - tier_compatibility)
            if missing:
                failures.append(
                    "compatibility-tier modules absent from table: " + ", ".join(missing)
                )
            if extra:
                failures.append(
                    "tabled historical modules not in compatibility tier: "
                    + ", ".join(extra)
                )
    except (OSError, json.JSONDecodeError, AttributeError) as error:
        failures.append(f"cannot read tier manifest {tier_manifest_path}: {error}")

    for historical, canonical in sorted(mappings.items()):
        old_path = module_path(historical)
        if not old_path.is_file():
            failures.append(f"missing historical module: {historical}")
            continue
        for target in canonical:
            if not module_path(target).is_file():
                failures.append(f"missing canonical module: {target}")

        text = old_path.read_text(encoding="utf-8-sig", errors="replace")
        uncommented = remove_lean_comments(text)
        imports = tuple(
            target
            for target in IMPORT_RE.findall(uncommented)
            if target.startswith("NumStability.")
        )
        if imports != canonical:
            failures.append(
                f"{historical}: imports {imports!r}, documented {canonical!r}"
            )
        remaining = IMPORT_LINE_RE.sub("", uncommented).strip()
        if remaining:
            failures.append(f"{historical}: forwarding module contains Lean code")

    historical_names = set(mappings)
    production_import_edges: set[tuple[str, str]] = set()
    for path in source_paths(ROOT):
        name = module_name(path.relative_to(ROOT))
        if name in historical_names:
            continue
        text = path.read_text(encoding="utf-8-sig", errors="replace")
        for target in IMPORT_RE.findall(remove_lean_comments(text)):
            if target in historical_names:
                production_import_edges.add((name, target))
    failures.extend(production_import_failures(production_import_edges))

    canonical_names = {target for targets in mappings.values() for target in targets}
    failures.extend(self_test_isolation_rules())
    failures.extend(isolation_failures(ROOT, mappings))

    if failures:
        for failure in failures:
            print(f"error: {failure}", file=sys.stderr)
        return 1
    target_count = sum(len(targets) for targets in mappings.values())
    unique_target_count = len(canonical_names)
    print(
        f"compatibility contract passed: {len(mappings)} forwarding modules, "
        f"{unique_target_count} unique canonical targets over {target_count} target edges, "
        f"{len(production_import_edges)} production imports of historical paths"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
