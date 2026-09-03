#!/usr/bin/env python3
"""Enforce the placeholder and allowed-axiom policy (AXIOM-01).

Three claims are checked.

  1. NO PLACEHOLDERS. No `sorry` and no `admit` appears as Lean code anywhere in
     the production library or the test library.
  2. NO UNREVIEWED AXIOMS IN SOURCE. No top-level `axiom` or `constant`
     declaration exists outside the reviewed allowlist.
  3. NO UNREVIEWED AXIOM DEPENDENCIES. Every axiom reported by Lean's
     `#print axioms` in a build log is present in the reviewed allowlist, and
     `sorryAx` never appears, since a proof completed by `sorry` depends on it.

Strict comment and string handling is the substance of claim 1, not a detail:
this repository contains 36 files whose documentation states "No `sorry`/`admit`"
and many docstring lines that begin with the word "constant". A naive text search
reports all of them. Block comments nest in Lean, so the stripper tracks depth.

usage:
  python check_placeholders.py [--self-test] [--log BUILD_LOG] [--completion]
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
POLICY = "docs/architecture/allowed-axioms.json"
PLACEHOLDER_RE = re.compile(r"(?<![A-Za-z0-9_'.])(sorry|admit)(?![A-Za-z0-9_'])")
AXIOM_DECL_RE = re.compile(r"^\s*(axiom|constant)\s+([A-Za-z_][A-Za-z0-9_'.]*)", re.M)
AXIOM_REPORT_RE = re.compile(r"depends on axioms: \[([^\]]*)\]")
SORRY_AX = "sorryAx"


def strip_lean_comments_and_strings(text: str) -> str:
    """Blank out nested block comments, line comments and string literals.

    Replaces removed spans with spaces so that line and column positions of the
    surviving code are preserved.
    """

    out = list(text)
    i, n = 0, len(text)
    depth = 0
    while i < n:
        two = text[i:i + 2]
        if depth == 0 and two == "/-":
            depth = 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth > 0:
            if two == "/-":
                depth += 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if two == "-/":
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if text[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if two == "--":
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
            continue
        if text[i] == '"':
            out[i] = " "
            i += 1
            while i < n and text[i] != '"':
                if text[i] == "\\" and i + 1 < n:
                    out[i] = out[i + 1] = " "
                    i += 2
                    continue
                if text[i] != "\n":
                    out[i] = " "
                i += 1
            if i < n:
                out[i] = " "
                i += 1
            continue
        i += 1
    return "".join(out)


def lean_sources(root: Path) -> list[Path]:
    paths: list[Path] = []
    for top in ("NumStability", "NumStabilityTest"):
        base = root / top
        if base.is_dir():
            paths.extend(sorted(base.rglob("*.lean")))
        single = root / f"{top}.lean"
        if single.is_file():
            paths.append(single)
    return paths


def load_policy(root: Path) -> tuple[set[str], set[str], list[str]]:
    """(allowed axioms, allowed axiom declarations, problems)."""
    path = root / POLICY
    if not path.is_file():
        return set(), set(), [f"missing axiom policy {POLICY}"]
    try:
        doc = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as error:
        return set(), set(), [f"cannot read {POLICY}: {error}"]
    problems: list[str] = []
    if doc.get("schema_version") != 1:
        problems.append(f"{POLICY}: schema_version must be 1")
    allowed = doc.get("allowed_axioms")
    if not isinstance(allowed, list) or not allowed:
        return set(), set(), problems + [f"{POLICY}: allowed_axioms must be a non-empty list"]
    names: set[str] = set()
    for entry in allowed:
        if not isinstance(entry, dict) or not entry.get("name"):
            problems.append(f"{POLICY}: every allowed axiom needs a name")
            continue
        for field in ("rationale", "reviewer", "status"):
            if not entry.get(field):
                problems.append(f"{POLICY}: allowed axiom {entry['name']} needs {field}")
        names.add(entry["name"])
    if SORRY_AX in names:
        problems.append(f"{POLICY}: {SORRY_AX} must never be allowlisted")
    declarations = {d.get("name") for d in doc.get("allowed_axiom_declarations") or []
                    if isinstance(d, dict) and d.get("name")}
    return names, declarations, problems


def placeholder_failures(root: Path) -> list[str]:
    failures: list[str] = []
    for path in lean_sources(root):
        code = strip_lean_comments_and_strings(path.read_text(encoding="utf-8", errors="replace"))
        for match in PLACEHOLDER_RE.finditer(code):
            line = code.count("\n", 0, match.start()) + 1
            failures.append(
                f"{path.relative_to(root).as_posix()}:{line}: placeholder `{match.group(1)}` in Lean code"
            )
    return failures


def axiom_declaration_failures(root: Path, allowed_declarations: set[str]) -> list[str]:
    failures: list[str] = []
    for path in lean_sources(root):
        code = strip_lean_comments_and_strings(path.read_text(encoding="utf-8", errors="replace"))
        for match in AXIOM_DECL_RE.finditer(code):
            kind, name = match.group(1), match.group(2)
            if name in allowed_declarations:
                continue
            line = code.count("\n", 0, match.start()) + 1
            failures.append(
                f"{path.relative_to(root).as_posix()}:{line}: unreviewed `{kind} {name}`"
            )
    return failures


def axiom_dependency_failures(log_path: Path, allowed: set[str]) -> tuple[list[str], int, set[str]]:
    """Check every reported axiom set in a build log against the allowlist."""
    failures: list[str] = []
    if not log_path.is_file():
        return [f"missing build log {log_path}"], 0, set()
    text = log_path.read_text(encoding="utf-8", errors="replace")
    # a reported axiom list can wrap across lines
    flat = re.sub(r"\s*\n\s+", " ", text)
    reports = AXIOM_REPORT_RE.findall(flat)
    seen: set[str] = set()
    for report in reports:
        for raw in report.split(","):
            name = raw.strip()
            if name:
                seen.add(name)
    if SORRY_AX in seen:
        failures.append(f"{log_path.name}: a proof depends on {SORRY_AX}, so a `sorry` reached the environment")
    for name in sorted(seen - allowed):
        if name != SORRY_AX:
            failures.append(f"{log_path.name}: axiom `{name}` is not in the reviewed allowlist")
    return failures, len(reports), seen


def self_test() -> list[str]:
    failures: list[str] = []

    # false positives: documentation that mentions the words must not trigger
    benign = (
        "/-! No `sorry`/`admit`/`axiom`/`native_decide`. -/\n"
        "-- a comment mentioning sorry and admit\n"
        "/- nested /- sorry -/ still a comment -/\n"
        'def message : String := "sorry"\n'
        "/-- A constant bound. -/\ntheorem t : True := trivial\n"
    )
    code = strip_lean_comments_and_strings(benign)
    if PLACEHOLDER_RE.search(code):
        failures.append("self-test: documentation mentioning sorry/admit must not be flagged")
    if AXIOM_DECL_RE.search(code):
        failures.append("self-test: a docstring line about a constant must not read as a declaration")
    if code.count("\n") != benign.count("\n"):
        failures.append("self-test: stripping must preserve line structure")

    # true positives
    real = "theorem bad : True := by\n  sorry\n"
    if not PLACEHOLDER_RE.search(strip_lean_comments_and_strings(real)):
        failures.append("self-test: a real `sorry` must be flagged")
    if not PLACEHOLDER_RE.search(strip_lean_comments_and_strings("example : True := by admit\n")):
        failures.append("self-test: a real `admit` must be flagged")

    # namespace forms and indentation
    for text in ("namespace N\naxiom bad_ax : True\nend N\n",
                 "  axiom indented_ax : True\n",
                 "constant legacy_const : Nat\n"):
        if not AXIOM_DECL_RE.search(strip_lean_comments_and_strings(text)):
            failures.append(f"self-test: an axiom declaration must be found in {text.strip()[:28]!r}")

    # a new axiom in a dependency report must be rejected, and the allowlist must not escape
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    flat = "'X' depends on axioms: [propext, Classical.choice, Quot.sound, My.NewAxiom]"
    seen = {n.strip() for r in AXIOM_REPORT_RE.findall(flat) for n in r.split(",")}
    if not (seen - allowed):
        failures.append("self-test: a new axiom must be detected as outside the allowlist")
    if SORRY_AX in allowed:
        failures.append("self-test: sorryAx must never be treated as allowed")
    sorry_report = "'Y' depends on axioms: [propext, sorryAx]"
    seen2 = {n.strip() for r in AXIOM_REPORT_RE.findall(sorry_report) for n in r.split(",")}
    if SORRY_AX not in seen2:
        failures.append("self-test: a sorryAx dependency must be detected")
    return failures


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--log", type=Path, default=None,
                        help="build log carrying `#print axioms` output")
    parser.add_argument("--completion", action="store_true",
                        help="require the axiom-dependency evidence, not just the source scan")
    args = parser.parse_args(argv)

    problems = self_test()
    if args.self_test:
        if problems:
            for problem in problems:
                print(f"error: {problem}", file=sys.stderr)
            return 1
        print("placeholder policy self-test passed: documentation false positives rejected, "
              "real placeholders and namespace axiom forms detected, a new axiom and a "
              "sorryAx dependency caught")
        return 0

    allowed, allowed_declarations, policy_problems = load_policy(ROOT)
    problems += policy_problems
    problems += placeholder_failures(ROOT)
    problems += axiom_declaration_failures(ROOT, allowed_declarations)

    reports = 0
    seen: set[str] = set()
    if args.log is not None:
        log_problems, reports, seen = axiom_dependency_failures(args.log, allowed)
        problems += log_problems
    elif args.completion:
        problems.append("completion mode requires --log carrying axiom-dependency evidence")

    if problems:
        for problem in problems:
            print(f"error: {problem}", file=sys.stderr)
        return 1
    scanned = len(lean_sources(ROOT))
    detail = f", {reports} axiom report(s) using {sorted(seen)}" if reports else ""
    print(f"placeholder and axiom policy passed: {scanned} Lean file(s) with no `sorry` or "
          f"`admit` in code and no unreviewed axiom declaration; allowlist {sorted(allowed)}{detail}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
