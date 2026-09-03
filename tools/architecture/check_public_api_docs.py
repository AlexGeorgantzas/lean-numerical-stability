#!/usr/bin/env python3
"""Enforce the public-API documentation policy (EVID-05).

Scope: every non-private declaration of the kinds listed in the policy, in every
module whose tier is `reusable` or `source`. Two rules are checked.

  1. TYPES ARE DOCUMENTED. Every public `structure`, `class` and `inductive` in
     scope carries a docstring. Types are the vocabulary of the API, so this
     rule has no debt list.
  2. NO NEW UNDOCUMENTED DECLARATION. Every other public declaration without a
     docstring must be fingerprinted in the reviewed baseline. The baseline may
     only shrink: a fingerprint that no longer corresponds to an undocumented
     declaration is stale and must be removed by regenerating.

The scan is textual and presence-only: it decides whether a docstring sits
immediately before a declaration head (blank lines and attribute lines may
intervene), not whether the docstring is adequate. Block comments nest in Lean
and docstring prose often begins a line with a declaration keyword, so the
scanner blanks every comment before matching heads and walks the original text
to find the preceding docstring. A declaration written on the same line as its
docstring is invisible to the head regex and is neither counted nor required.

usage:
  python check_public_api_docs.py [--self-test] [--regenerate] [--commit SHA]
"""
from __future__ import annotations

import argparse
import collections
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
POLICY = "docs/architecture/public-api-policy.json"
BASELINE = "docs/architecture/public-api-baseline.json"
TIERS = "docs/architecture/tiers.json"

KINDS = ("theorem", "lemma", "def", "abbrev", "opaque", "structure", "class", "inductive", "instance")
TYPE_KINDS = ("structure", "class", "inductive")
HEAD_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?P<mods>(?:private |protected |noncomputable |partial |unsafe |scoped |local )*)"
    r"(?P<kind>" + "|".join(KINDS) + r")\b(?:\s+(?P<name>[A-Za-z_][A-Za-z0-9_'.]*))?"
)
DOC_RE = re.compile(r"/--.*?-/", re.S)


def blank_comments(text: str) -> str:
    """Blank nested block comments and line comments, preserving line structure."""
    out = list(text)
    i, n, depth = 0, len(text), 0
    while i < n:
        if text.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth > 0:
            if text.startswith("-/", i):
                depth -= 1
                out[i] = out[i + 1] = " "
                i += 2
                continue
            if text[i] != "\n":
                out[i] = " "
            i += 1
            continue
        if text.startswith("--", i):
            while i < n and text[i] != "\n":
                out[i] = " "
                i += 1
            continue
        i += 1
    return "".join(out)


def scan_text(text: str) -> list[tuple[int, str, str, bool]]:
    """(line, kind, name, documented) for every non-private declaration head."""
    code = blank_comments(text)
    doc_end_lines: set[int] = set()
    for match in DOC_RE.finditer(text):
        rest_of_line = text[match.end():].split("\n", 1)[0].strip()
        # a docstring documents the declaration that FOLLOWS it; if code follows on
        # the same line, that code is the documented declaration, not the next line
        if rest_of_line == "" or rest_of_line.startswith("@["):
            doc_end_lines.add(text.count("\n", 0, match.end()))
    code_lines = code.split("\n")
    original_lines = text.split("\n")
    found: list[tuple[int, str, str, bool]] = []
    for index, line in enumerate(code_lines):
        head = HEAD_RE.match(line)
        if not head or "private " in (head.group("mods") or ""):
            continue
        j = index - 1
        while j >= 0 and (not original_lines[j].strip() or original_lines[j].lstrip().startswith("@[")):
            j -= 1
        found.append((index + 1, head.group("kind"), head.group("name") or "", j in doc_end_lines))
    return found


def load_tiers(root: Path):
    manifest = json.loads((root / TIERS).read_text(encoding="utf-8"))
    exact = manifest["exact"]
    prefixes = [(r["prefix"].rstrip("."), r["tier"]) for r in manifest["prefixes"]]

    def role(module: str) -> str:
        if module in exact:
            return exact[module]
        best = None
        for prefix, tier in prefixes:
            if module == prefix or module.startswith(prefix + "."):
                if best is None or len(prefix) > len(best[0]):
                    best = (prefix, tier)
        return best[1] if best else "unclassified"

    return role


def tracked_modules(root: Path) -> list[tuple[str, Path]]:
    out = subprocess.run(["git", "ls-files", "NumStability/*.lean"], cwd=root,
                         capture_output=True, text=True, encoding="utf-8").stdout
    return [(p[:-5].replace("/", "."), root / p) for p in out.split("\n") if p.endswith(".lean")]


def scan_repository(root: Path, scope_tiers: set[str]):
    role = load_tiers(root)
    totals: collections.Counter = collections.Counter()
    documented: collections.Counter = collections.Counter()
    undocumented: list[dict] = []
    for module, path in tracked_modules(root):
        tier = role(module)
        if tier not in scope_tiers:
            continue
        occurrences: collections.Counter = collections.Counter()
        for line, kind, name, is_documented in scan_text(path.read_text(encoding="utf-8", errors="replace")):
            totals[(tier, kind)] += 1
            # anonymous instances have no name and a name may be reused across sections of one
            # module, so the ordinal of this (kind, name) pair within the module is part of the identity
            occurrences[(kind, name)] += 1
            if is_documented:
                documented[(tier, kind)] += 1
            else:
                undocumented.append({"module": module, "kind": kind, "name": name, "line": line,
                                     "tier": tier, "occurrence": occurrences[(kind, name)]})
    return totals, documented, undocumented


def fingerprint(entry: dict) -> str:
    # line numbers move; the identity of an undocumented declaration is its module, kind, name and
    # the ordinal of that (kind, name) pair within the module
    return f"{entry['module']}|{entry['kind']}|{entry['name']}|{entry['occurrence']}"


def load_json(root: Path, relative: str):
    return json.loads((root / relative).read_text(encoding="utf-8"))


def self_test() -> list[str]:
    failures: list[str] = []
    fixture = (
        "/-- doc -/\ntheorem a : True := trivial\n\n"
        "/-! module docs are not declaration docs -/\n\ntheorem b : True := trivial\n\n"
        "/-- multi\nline -/\n@[simp]\ndef c := 1\n"
        "/-- d -/ theorem d0 : True := trivial\n"
        "theorem e : True := trivial -- structure\n"
        "/-- f -/ @[simp]\ntheorem f : True := trivial\n"
        "/-- prose that begins a line with\nstructure of the proof -/\ntheorem g : True := trivial\n"
        "private theorem hidden : True := trivial\n"
        "/- plain comment -/\nstructure S where\n  x : Nat\n"
    )
    got = [(name, doc) for _, _, name, doc in scan_text(fixture)]
    expected = [("a", True), ("b", False), ("c", True), ("e", False), ("f", True), ("g", True), ("S", False)]
    if got != expected:
        failures.append(f"self-test: fixture scan produced {got}, expected {expected}")
    if fingerprint({"module": "M", "kind": "def", "name": "x", "occurrence": 1}) != "M|def|x|1":
        failures.append("self-test: fingerprint format changed")
    # two anonymous instances in one module must not share a fingerprint
    two = "instance : Inhabited Nat := ⟨0⟩\ninstance : Inhabited Int := ⟨0⟩\n"
    names = [(kind, name) for _, kind, name, _ in scan_text(two)]
    if names != [("instance", ""), ("instance", "")]:
        failures.append(f"self-test: anonymous instances must scan as unnamed instances, got {names}")
    if blank_comments("a /- b /- c -/ d -/ e").split() != ["a", "e"]:
        failures.append("self-test: nested block comments must be blanked")
    return failures


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--regenerate", action="store_true", help="rewrite the baseline from the current tree")
    parser.add_argument("--commit", default=None, help="commit recorded in a regenerated baseline header")
    args = parser.parse_args(argv)

    problems = self_test()
    if args.self_test:
        for problem in problems:
            print(f"error: {problem}", file=sys.stderr)
        if not problems:
            print("public-API documentation self-test passed: docstring attribution, same-line and "
                  "attribute cases, prose beginning with a keyword, private exclusion and nesting")
        return 1 if problems else 0

    policy = load_json(ROOT, POLICY)
    population = policy.get("supported_population") or policy.get("scope") or {}
    scope = set(population.get("owner_tiers") or population.get("tiers") or ())
    if not scope:
        print(f"error: {POLICY} names no owner tiers", file=sys.stderr)
        return 1
    totals, documented, undocumented = scan_repository(ROOT, scope)

    if args.regenerate:
        entries = sorted(
            (e for e in undocumented if e["kind"] not in TYPE_KINDS),
            key=lambda e: (e["module"], e["kind"], e["name"]),
        )
        baseline = {
            "schema_version": 1,
            "policy": POLICY,
            "generated_at_commit": args.commit,
            "note": "Reviewed debt: public declarations in scope without a docstring at generation time. "
                    "This list may only shrink. Types never appear here; rule 1 has no debt.",
            "count": len(entries),
            "fingerprints": [fingerprint(e) for e in entries],
        }
        (ROOT / BASELINE).write_text(json.dumps(baseline, indent=1) + "\n", encoding="utf-8")
        print(f"regenerated {BASELINE}: {len(entries)} undocumented declaration(s) recorded")
        return 0

    baseline = load_json(ROOT, BASELINE)
    allowed = set(baseline["fingerprints"])
    current = {fingerprint(e): e for e in undocumented if e["kind"] not in TYPE_KINDS}
    for entry in undocumented:
        if entry["kind"] in TYPE_KINDS:
            problems.append(
                f"{entry['module']}:{entry['line']}: public {entry['kind']} `{entry['name']}` "
                "has no docstring (rule 1: types are documented)"
            )
    for key in sorted(set(current) - allowed):
        e = current[key]
        problems.append(
            f"{e['module']}:{e['line']}: new undocumented public {e['kind']} `{e['name']}` "
            "(rule 2: add a docstring)"
        )
    for key in sorted(allowed - set(current)):
        problems.append(
            f"stale baseline fingerprint {key}: the declaration is now documented or gone; "
            "regenerate the baseline"
        )
    if len(allowed) != len(baseline["fingerprints"]):
        problems.append("baseline contains duplicate fingerprints")

    if problems:
        for problem in problems:
            print(f"error: {problem}", file=sys.stderr)
        return 1
    total = sum(totals.values())
    docs = sum(documented.values())
    types_total = sum(v for k, v in totals.items() if k[1] in TYPE_KINDS)
    print(f"public-API documentation policy satisfied: {docs:,}/{total:,} public declarations documented "
          f"({100 * docs / total:.2f}%), all {types_total} public types documented, "
          f"{len(allowed):,} reviewed undocumented declarations in the baseline, none new")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
