#!/usr/bin/env python3
"""Enforce the entry-point manifest (EVID-04).

An ENTRY POINT here is any module that other code is expected to import as a
surface rather than as a leaf: every family parent (a module with at least one
descendant module), every key of the `complete_aggregates` layout contract,
every module advertised in the README key-entry-point table or as the subject
of an ARCHITECTURE.md entry-point bullet, and every reusable seed.

`docs/architecture/entrypoints.json` records one row per entry point, and this
checker recomputes every field live, so the manifest cannot drift from the
tree, and the documentation cannot drift from the manifest.

Each row carries one of five classes: `complete` (a family parent reaching
every canonical descendant), `historical/discovery` (a complete parent whose
own documentation or advertising presents it as a historical or discovery
surface, kept for navigation rather than as a curated import), `partial` (a
parent missing canonical descendants; always a failure), `compatibility`
(compatibility-tier forwarding parents), `non-entrypoint` (internal- or
upstream-tier parents), and `leaf` for advertised, contracted or seeded
modules that have no descendants. Rules:

  R1  BIJECTION. The manifest rows are exactly the computed entry-point set.
  R2  RECORD. Every recorded field equals the live value (regenerate to update).
  R3  COMPLETENESS. Every family parent that is not a compatibility or
      non-entrypoint module reaches every canonical (source- or reusable-tier)
      descendant.
  R4  TIER. An import-only family parent is tiered aggregate or compatibility,
      never source or reusable: a module with no declarations of its own is a
      structural surface and must be classified as one.
  R5  ISOLATION. Every complete entry point that is contracted or advertised
      has an isolated test: a test module whose only import is the entry point
      and which `#check`s at least one declaration, so the surface is proven to
      supply declarations on its own.
  R6  CLAIMS. An ARCHITECTURE.md bullet that presents its subject as reusable
      names a module that is reusable-tier or a reusable seed.

usage:
  python check_entrypoints.py [--self-test] [--regenerate] [--commit SHA]
"""
from __future__ import annotations

import argparse
import json
import re
import subprocess
import sys
from collections import deque
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
MANIFEST = "docs/architecture/entrypoints.json"
TIERS = "docs/architecture/tiers.json"
LAYOUT = "docs/architecture/layout-exceptions.json"
README = "README.md"
ARCHITECTURE = "ARCHITECTURE.md"

IMPORT_RE = re.compile(r"^import\s+(\S+)", re.M)
DECL_RE = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:private |protected |noncomputable |partial |unsafe |scoped |local )*"
    r"(?:theorem|lemma|def|abbrev|opaque|structure|class|inductive|instance|axiom|example)\b", re.M)
CHECK_RE = re.compile(r"^\s*#(?:check|print|eval)\b", re.M)
BULLET_RE = re.compile(r"^- `(NumStability(?:\.[A-Za-z0-9_]+)*)`((?:[^\n]*\n?)(?:  [^\n]*\n?)*)", re.M)
README_ROW_RE = re.compile(r"^\| `(NumStability(?:\.[A-Za-z0-9_]+)*)` \| ([^|\n]*)\|", re.M)
MODULE_DOC_RE = re.compile(r"/-!(.*?)-/", re.S)
DISCOVERY_RE = re.compile(r"\b(discovery|historical)\b", re.I)
# "`X` is the deliberately small reusable foundation", "`X` is the reusable ...": a claim about the
# subject itself, as opposed to "reusable consumers import ..." or "not a claim that ... is reusable"
REUSABLE_CLAIM_RE = re.compile(r"^\s*is (?:the |a |an )?(?:[\w-]+ ){0,3}reusable\b")

SURFACE_README = "README.md#key-entry-points"
SURFACE_ARCHITECTURE = "ARCHITECTURE.md#entry-points"
SURFACE_SEED = "tiers.json#reusable_entrypoints"


def strip_comments(text: str) -> str:
    return re.sub(r"/-.*?-/", "", text, flags=re.S)


def git_lean_files(root: Path, *patterns: str) -> list[str]:
    out = subprocess.run(["git", "ls-files", *patterns], cwd=root, capture_output=True,
                         text=True, encoding="utf-8").stdout
    return [p for p in out.split("\n") if p.endswith(".lean")]


class Tree:
    def __init__(self, root: Path):
        self.root = root
        paths = git_lean_files(root, "NumStability/*.lean", "NumStability.lean")
        self.path_of = {p[:-5].replace("/", "."): p for p in paths}
        self.text = {m: (root / p).read_text(encoding="utf-8", errors="replace") for m, p in self.path_of.items()}
        self.imports = {m: [x for x in IMPORT_RE.findall(strip_comments(t)) if x in self.path_of]
                        for m, t in self.text.items()}
        self.declaring = {m for m, t in self.text.items() if DECL_RE.search(strip_comments(t))}
        tiers = json.loads((root / TIERS).read_text(encoding="utf-8"))
        self.exact = tiers["exact"]
        self.prefixes = [(r["prefix"].rstrip("."), r["tier"]) for r in tiers["prefixes"]]
        self.seeds = set(tiers.get("reusable_entrypoints", []))
        layout = json.loads((root / LAYOUT).read_text(encoding="utf-8"))
        self.contracts = layout["complete_aggregates"]
        self._reach: dict[str, set[str]] = {}
        children: dict[str, list[str]] = {}
        for m in self.path_of:
            for k in range(m.count("."), 0, -1):
                children.setdefault(".".join(m.split(".")[:k]), []).append(m)
        self.descendants = {m: sorted(children.get(m, [])) for m in self.path_of}
        # isolated tests: test modules with exactly one import, mapped to that import
        self.isolated: dict[str, list[tuple[str, int]]] = {}
        for p in git_lean_files(root, "NumStabilityTest/*.lean"):
            body = strip_comments((root / p).read_text(encoding="utf-8", errors="replace"))
            imps = IMPORT_RE.findall(body)
            if len(imps) == 1:
                self.isolated.setdefault(imps[0], []).append((p, len(CHECK_RE.findall(body))))

    def tier(self, m: str) -> str:
        if m in self.exact:
            return self.exact[m]
        best = None
        for prefix, tier in self.prefixes:
            if m == prefix or m.startswith(prefix + "."):
                if best is None or len(prefix) > len(best[0]):
                    best = (prefix, tier)
        return best[1] if best else "unclassified"

    def reach(self, m: str) -> set[str]:
        if m not in self._reach:
            seen: set[str] = set()
            queue = deque([m])
            while queue:
                cur = queue.popleft()
                if cur in seen:
                    continue
                seen.add(cur)
                queue.extend(self.imports[cur])
            self._reach[m] = seen
        return self._reach[m]


def advertised(root: Path) -> tuple[dict[str, list[str]], dict[str, str], dict[str, str]]:
    """(module -> surfaces it is advertised on, module -> first clause of its ARCHITECTURE bullet,
    module -> all advertising text about it)."""
    surfaces: dict[str, list[str]] = {}
    clauses: dict[str, str] = {}
    texts: dict[str, str] = {}
    readme = (root / README).read_text(encoding="utf-8")
    start = readme.find("## Key entry points")
    end = readme.find("\n## ", start + 1)
    for m, purpose in README_ROW_RE.findall(readme[start:end]):
        surfaces.setdefault(m, []).append(SURFACE_README)
        texts[m] = texts.get(m, "") + " " + purpose
    arch = (root / ARCHITECTURE).read_text(encoding="utf-8")
    start = arch.find("## Entry points")
    end = arch.find("\n## ", start + 1)
    for m, body in BULLET_RE.findall(arch[start:end]):
        surfaces.setdefault(m, []).append(SURFACE_ARCHITECTURE)
        clauses[m] = " ".join(body.split())
        texts[m] = texts.get(m, "") + " " + clauses[m]
    return surfaces, clauses, texts


def compute_rows(tree: Tree, root: Path) -> tuple[list[dict], list[str]]:
    surfaces, clauses, texts = advertised(root)
    for m in tree.seeds:
        surfaces.setdefault(m, []).append(SURFACE_SEED)
    parents = {m for m, d in tree.descendants.items() if d}
    universe = parents | set(tree.contracts) | set(surfaces)
    rows: list[dict] = []
    problems: list[str] = []
    for m in sorted(universe):
        if m not in tree.path_of:
            problems.append(f"entry point {m} is advertised or contracted but is not a module")
            continue
        tier = tree.tier(m)
        canonical = [d for d in tree.descendants[m] if tree.tier(d) in ("source", "reusable")]
        reach = tree.reach(m)
        missing = [d for d in canonical if d not in reach]
        is_parent = m in parents
        module_doc = MODULE_DOC_RE.search(tree.text[m])
        described_as = " ".join(((module_doc.group(1) if module_doc else "") + " " + texts.get(m, "")).split())
        if tier == "compatibility":
            cls = "compatibility"
        elif tier in ("internal", "upstream"):
            cls = "non-entrypoint"
        elif not is_parent:
            cls = "leaf"
        elif missing:
            cls = "partial"
        elif DISCOVERY_RE.search(described_as):
            cls = "historical/discovery"
        else:
            cls = "complete"
        contract = tree.contracts.get(m)
        tests = tree.isolated.get(m, [])
        checked = [(p, n) for p, n in tests if n > 0]
        rows.append({
            "module": m,
            "tier": tier,
            "class": cls,
            "import_only": m not in tree.declaring,
            "descendants": len(tree.descendants[m]),
            "canonical_descendants": len(canonical),
            "canonical_missing": missing,
            "contract": ("prefix" if isinstance(contract, str) else "members") if contract is not None else None,
            "reusable_seed": m in tree.seeds,
            "advertised_in": sorted(surfaces.get(m, [])),
            "isolated_test": checked[0][0] if checked else (tests[0][0] if tests else None),
            "declaration_checks": checked[0][1] if checked else 0,
        })
        # R3
        if cls == "partial":
            problems.append(f"R3 {m} does not reach {len(missing)} canonical descendant(s): " + ", ".join(missing))
        # R4
        if is_parent and m not in tree.declaring and tier in ("source", "reusable"):
            problems.append(f"R4 {m} is an import-only family parent tiered {tier}; retier it as aggregate")
        # R5
        if cls in ("complete", "historical/discovery") and (contract is not None or surfaces.get(m)) and not checked:
            problems.append(f"R5 {m} is a complete {'contracted' if contract is not None else 'advertised'} "
                            "entry point without an isolated single-import test that checks a declaration")
        # R6
        clause = clauses.get(m)
        if clause is not None and REUSABLE_CLAIM_RE.match(clause) and tier != "reusable" and m not in tree.seeds:
            problems.append(f"R6 ARCHITECTURE.md presents {m} as reusable, but it is tiered {tier} and is not a reusable seed")
    return rows, problems


def compare(recorded: dict, rows: list[dict]) -> list[str]:
    problems: list[str] = []
    live = {r["module"]: r for r in rows}
    rec = {r["module"]: r for r in recorded.get("entrypoints", [])}
    for m in sorted(set(live) - set(rec)):
        problems.append(f"R1 {m} is an entry point but is missing from {MANIFEST}; regenerate")
    for m in sorted(set(rec) - set(live)):
        problems.append(f"R1 {m} is recorded in {MANIFEST} but is no longer an entry point; regenerate")
    for m in sorted(set(live) & set(rec)):
        for key, value in live[m].items():
            if rec[m].get(key) != value:
                problems.append(f"R2 {m}.{key} recorded as {rec[m].get(key)!r} but is {value!r}; regenerate")
    return problems


def summary(rows: list[dict]) -> dict:
    out: dict = {"rows": len(rows)}
    for key in ("class", "tier"):
        counts: dict[str, int] = {}
        for r in rows:
            counts[r[key]] = counts.get(r[key], 0) + 1
        out[f"by_{key}"] = dict(sorted(counts.items()))
    out["with_isolated_declaration_test"] = sum(1 for r in rows if r["declaration_checks"] > 0)
    out["advertised"] = sum(1 for r in rows if r["advertised_in"])
    out["contracted"] = sum(1 for r in rows if r["contract"])
    return out


def self_test() -> list[str]:
    failures: list[str] = []
    yes = ["is the deliberately small reusable foundation entry point.",
           "is the declaration-free reusable linear-systems entry point.",
           "is the reusable probability-analysis entry point."]
    no = ["is the complete published summation surface. Its umbrellas preserve source reachability, while reusable consumers import their `.Core` leaves.",
          "is a complete family-discovery umbrella, not a claim that every Chapter 16 declaration is reusable mathematics.",
          "is the canonical Higham correspondence entry point."]
    for text in yes:
        if not REUSABLE_CLAIM_RE.match(text):
            failures.append(f"self-test: reusable claim not recognized: {text[:50]}")
    for text in no:
        if REUSABLE_CLAIM_RE.match(text):
            failures.append(f"self-test: non-claim treated as a reusable claim: {text[:50]}")
    if not DECL_RE.search("namespace X\n@[simp] theorem t : True := trivial\n"):
        failures.append("self-test: an attributed theorem must count as a declaration")
    if DECL_RE.search(strip_comments("/-! the word theorem in a docstring -/\nimport A\n")):
        failures.append("self-test: documentation must not count as a declaration")
    # a commented-out check is not a check
    if len(CHECK_RE.findall("#check a\n  #check b\n-- #check c\n")) != 2:
        failures.append("self-test: #check counting changed")
    if not DISCOVERY_RE.search("Declaration-free W06 discovery aggregate.") or \
            not DISCOVERY_RE.search("Broad historical algorithm surface") or \
            DISCOVERY_RE.search("Declaration-free aggregate for the canonical modules in this family."):
        failures.append("self-test: historical/discovery recognition changed")
    rows = README_ROW_RE.findall("| `NumStability.Core` | Small reusable foundation |\n| `NumStability` | Historical entry |\n")
    if rows != [("NumStability.Core", "Small reusable foundation "), ("NumStability", "Historical entry ")]:
        failures.append(f"self-test: README table parsing changed: {rows}")
    return failures


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--regenerate", action="store_true")
    parser.add_argument("--commit", default=None)
    args = parser.parse_args(argv)

    problems = self_test()
    if args.self_test:
        for p in problems:
            print(f"error: {p}", file=sys.stderr)
        if not problems:
            print("entry-point self-test passed: reusable-claim recognition, declaration and check detection")
        return 1 if problems else 0

    tree = Tree(ROOT)
    rows, live_problems = compute_rows(tree, ROOT)
    if args.regenerate:
        manifest = {
            "schema_version": 1,
            "generated_at_commit": args.commit,
            "policy": "Every entry point is recorded here with live-checked fields. Non-compatibility family "
                      "parents reach every canonical descendant; import-only parents are aggregates; "
                      "contracted or advertised entry points have isolated declaration-checking tests; "
                      "documentation may call a module reusable only if its tier or seed status says so.",
            "surfaces": [SURFACE_README, SURFACE_ARCHITECTURE, SURFACE_SEED],
            "summary": summary(rows),
            "entrypoints": rows,
        }
        (ROOT / MANIFEST).write_text(json.dumps(manifest, indent=1) + "\n", encoding="utf-8")
        print(f"regenerated {MANIFEST}: {summary(rows)}")
        for p in live_problems:
            print(f"warning (still failing): {p}", file=sys.stderr)
        return 0

    manifest_path = ROOT / MANIFEST
    if not manifest_path.is_file():
        problems.append(f"missing {MANIFEST}; run --regenerate")
    else:
        problems += compare(json.loads(manifest_path.read_text(encoding="utf-8")), rows)
    problems += live_problems
    if problems:
        for p in problems:
            print(f"error: {p}", file=sys.stderr)
        return 1
    s = summary(rows)
    print(f"entry-point manifest satisfied: {s['rows']} entry points ({s['by_class']}), "
          f"{s['with_isolated_declaration_test']} with isolated declaration tests, "
          f"{s['advertised']} advertised, {s['contracted']} contracted; documentation claims consistent")
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
