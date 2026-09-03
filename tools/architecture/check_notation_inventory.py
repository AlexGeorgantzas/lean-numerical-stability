#!/usr/bin/env python3
"""Enforce the notation and syntax-extension inventory (EVID-05).

Static mode (default): scan every reusable-, source- and internal-tier module for notation, macro
and syntax commands outside comments, and require the set of (module, command) pairs to equal the
rows of `docs/architecture/notation-inventory.json`. A new notation fails until it is reviewed into
the inventory; a listed notation that vanished fails as stale.

Probe mode (`--probe`, needs a built library): for every `local` row, write an importer that uses
the token and check that `lake env lean` rejects it, proving the notation is not exported; for every
exported row (none today) check that the importer accepts it.

usage:
  python check_notation_inventory.py [--self-test] [--probe]
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
INVENTORY = "docs/architecture/notation-inventory.json"
TIERS = "docs/architecture/tiers.json"
SCANNED_TIERS = ("reusable", "source", "internal")
# horizontal whitespace only: `\s*` would crawl through every blanked comment run from each
# line start and make the scan quadratic on heavily documented files
COMMAND_RE = re.compile(
    r"^[ \t]*(?:@\[[^\]]*\][ \t]*)?(?:(?:scoped|local)[ \t]+)?"
    r"(?:notation\d*|infixl?|infixr|prefix|postfix|macro_rules|macro|syntax|elab_rules|elab|declare_syntax_cat|binder_predicate)\b[^\n]*",
    re.M)


def blank_comments(text: str) -> str:
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


def load_role(root: Path):
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


def scan_commands(text: str) -> list[str]:
    return [" ".join(m.group(0).split()) for m in COMMAND_RE.finditer(blank_comments(text))]


def scan_tree(root: Path) -> set[tuple[str, str]]:
    role = load_role(root)
    out = subprocess.run(["git", "ls-files", "NumStability/*.lean"], cwd=root, capture_output=True,
                         text=True, encoding="utf-8").stdout
    found: set[tuple[str, str]] = set()
    for rel in out.split("\n"):
        if not rel.endswith(".lean"):
            continue
        module = rel[:-5].replace("/", ".")
        if role(module) not in SCANNED_TIERS:
            continue
        for command in scan_commands((root / rel).read_text(encoding="utf-8", errors="replace")):
            found.add((module, command))
    return found


def static_failures(root: Path, inventory: dict) -> list[str]:
    problems: list[str] = []
    listed = {(r["module"], " ".join(r["command"].split())) for r in inventory["rows"]}
    found = scan_tree(root)
    for module, command in sorted(found - listed):
        problems.append(f"{module}: unreviewed syntax extension `{command}`; review it into {INVENTORY}")
    for module, command in sorted(listed - found):
        problems.append(f"{module}: inventory row `{command}` no longer exists in the tree; remove the stale row")
    for row in inventory["rows"]:
        if row["scope"] == "local" and (row["exported"] or row["supported_api"]):
            problems.append(f"{row['module']}: a local notation cannot be exported or supported API")
        if row["scope"] != "local" and not row.get("precedence") and row["kind"] != "notation":
            pass
    summary = inventory.get("summary", {})
    if summary.get("rows") != len(inventory["rows"]):
        problems.append(f"{INVENTORY}: summary.rows disagrees with the row count")
    if summary.get("exported") != sum(1 for r in inventory["rows"] if r["exported"]):
        problems.append(f"{INVENTORY}: summary.exported disagrees with the rows")
    return problems


def probe_failures(root: Path, inventory: dict) -> list[str]:
    problems: list[str] = []
    with tempfile.TemporaryDirectory(prefix="notation-probe-") as tmp:
        for index, row in enumerate(inventory["rows"]):
            probe = Path(tmp) / f"Probe{index}.lean"
            probe.write_text(f"import {row['module']}\n\nexample : Type := {row['token']}\n", encoding="utf-8")
            result = subprocess.run(["lake", "env", "lean", str(probe)], cwd=root, capture_output=True,
                                    text=True, encoding="utf-8", errors="replace")
            accepted = result.returncode == 0
            if row["exported"] and not accepted:
                problems.append(f"{row['module']}: exported notation `{row['token']}` was rejected by an importer: "
                                + (result.stderr or result.stdout).strip()[:200])
            if not row["exported"] and accepted:
                problems.append(f"{row['module']}: notation `{row['token']}` is declared {row['scope']} but an importer accepted it")
    return problems


def self_test() -> list[str]:
    failures: list[str] = []
    text = ("/-! docs mentioning notation and macro -/\n"
            "-- local notation \"X\" => Nat\n"
            "local notation \"𝔼\" => EuclideanSpace ℂ (Fin n)\n"
            "@[inherit_doc] scoped infixl:65 \" +ₐ \" => add\n"
            "macro \"foo\" : term => `(1)\n"
            "def notationLike := 1\n")
    got = scan_commands(text)
    want = ["local notation \"𝔼\" => EuclideanSpace ℂ (Fin n)",
            "@[inherit_doc] scoped infixl:65 \" +ₐ \" => add",
            "macro \"foo\" : term => `(1)"]
    if got != want:
        failures.append(f"self-test: command scan produced {got}")
    inventory = {"rows": [{"module": "M", "command": want[0], "scope": "local", "exported": False, "supported_api": False, "kind": "notation"}],
                 "summary": {"rows": 1, "exported": 0}}
    bad = dict(inventory, rows=[dict(inventory["rows"][0], exported=True)])
    if not [p for p in static_failures_from(set([("M", want[0])]), bad) if "cannot be exported" in p]:
        failures.append("self-test: an exported local notation must be rejected")
    if static_failures_from({("M", want[0])}, inventory):
        failures.append("self-test: a matching inventory must pass")
    if not static_failures_from({("M", want[0]), ("M", want[2])}, inventory):
        failures.append("self-test: an unreviewed macro must fail")
    if not static_failures_from(set(), inventory):
        failures.append("self-test: a stale row must fail")
    return failures


def static_failures_from(found: set[tuple[str, str]], inventory: dict) -> list[str]:
    """The static rule over an already-scanned set (used by the self-test)."""
    problems: list[str] = []
    listed = {(r["module"], " ".join(r["command"].split())) for r in inventory["rows"]}
    problems += [f"unreviewed {m} {c}" for m, c in sorted(found - listed)]
    problems += [f"stale {m} {c}" for m, c in sorted(listed - found)]
    for row in inventory["rows"]:
        if row["scope"] == "local" and (row["exported"] or row["supported_api"]):
            problems.append(f"{row['module']}: a local notation cannot be exported or supported API")
    return problems


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--probe", action="store_true", help="also run the importer probes (needs a built library)")
    args = parser.parse_args(argv)
    problems = self_test()
    if args.self_test or problems:
        for p in problems:
            print(f"error: {p}", file=sys.stderr)
        if not problems:
            print("notation inventory self-test passed: comment exclusion, scoped and attributed forms, "
                  "unreviewed, stale and local-but-exported cases")
        return 1 if problems else 0
    inventory = json.loads((ROOT / INVENTORY).read_text(encoding="utf-8"))
    problems = static_failures(ROOT, inventory)
    if args.probe and not problems:
        problems = probe_failures(ROOT, inventory)
    if problems:
        for p in problems:
            print(f"error: {p}", file=sys.stderr)
        return 1
    rows = inventory["rows"]
    print(f"notation inventory satisfied: {len(rows)} syntax extension(s) in the scanned tiers, "
          f"{sum(1 for r in rows if r['exported'])} exported, {sum(1 for r in rows if r['supported_api'])} in the supported API"
          + ("; importer probes agree" if args.probe else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
