#!/usr/bin/env python3
"""Static audit of the R11 worker tree against the frozen B0003 route contract.

    python -B docs/architecture/deliveries/R11/CHECK_STATIC.py [--control-root DIR]

This is a source-level audit and needs no Lean build. It proves the properties a
build cannot: that relocated declaration bodies are byte-identical to their C0001
preimages, that every historical path is retained and declaration-free, that the
reusable destinations reach neither `NumStability.Source` nor a compatibility facade,
and that the import graph stayed acyclic.

Byte-identity is the load-bearing check. A wave that re-emitted declarations instead of
moving them could still compile and still satisfy a projection replay on names and
edges, while having silently reformatted a proof. Comparing the exact body bytes against
`git show BASE:<owner>` removes that possibility.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = "117aa2bb7e61f41e1531a78452f9f7f6cd5b0771"
PHASE = "docs/architecture/phases/2026-08-repository-reorganization-completion/"
CONTROL_CANDIDATES = [
    Path(r"C:\Users\qed_s\higham-worktrees\completion-integrator-c0001"),
    Path(r"C:\Users\qed_s\OneDrive\Documents\QED 94"),
]
B0003_SHA = "29E5C9D60EB7B8A19F114ED4570BA9C125A3FDF7960C39796A4DDE45A9062519"

MOVES = {
    "NumStability.Algorithms.LinearSystems.QR.HouseholderSpecSupport":
        "NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels",
    "NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport":
        "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication",
    "NumStability.Algorithms.LinearSystems.QR.HouseholderQRSupport":
        "NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR",
    "NumStability.Source.Higham.Chapter19.Sensitivity":
        "NumStability.Source.Higham.Chapter19.Sensitivity.Bounds.Results",
    "NumStability.Source.Higham.Chapter19.StoredLoop":
        "NumStability.Source.Higham.Chapter19.StoredLoop.Perturbation.Bridge",
}
REUSABLE = {
    "NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels",
    "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication",
    "NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR",
}
RETARGETED = {
    "NumStability.Algorithms.QR.HouseholderApplySupport":
        "NumStability.Algorithms.LinearSystems.QR.Householder.PanelApplication",
    "NumStability.Algorithms.QR.HouseholderQRSupport":
        "NumStability.Algorithms.LinearSystems.QR.Householder.StoredQR",
    "NumStability.Algorithms.QR.HouseholderSpecSupport":
        "NumStability.Algorithms.LinearSystems.QR.Householder.TrailingPanels",
}
CORE = "NumStability.Source.Higham.Chapter19.Core"
TESTROOT = ROOT / "NumStabilityTest" / "Reorganization" / "R11"
AGGREGATE = "NumStabilityTest.Reorganization.R11.All"

IMPORT_RE = re.compile(r"^\s*(?:public\s+)?import\s+(\S+)\s*$")
BLOCK_COMMENT = re.compile(r"/-.*?-/", re.S)
LINE_COMMENT = re.compile(r"--.*?$", re.M)
DECL_RE = re.compile(
    r"(?m)^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|partial\s+|"
    r"unsafe\s+|scoped\s+)*(theorem|lemma|def|abbrev|structure|inductive|instance|class|"
    r"axiom|opaque|example)\b")

problems: list[str] = []


def fail(m: str) -> None:
    problems.append(m)


def path_of(module: str) -> Path:
    return ROOT.joinpath(*module.split(".")).with_suffix(".lean")


def read_exact(path: Path) -> str:
    """Read without newline translation. `Path.read_text(newline=...)` is 3.13+."""
    with open(path, encoding="utf-8", newline="") as fh:
        return fh.read()


def read(module: str) -> str:
    return read_exact(path_of(module))


def base_blob(rel: str) -> bytes:
    r = subprocess.run(["git", "-C", str(ROOT), "show", f"{BASE}:{rel}"],
                       capture_output=True)
    if r.returncode != 0:
        raise SystemExit(f"cannot read {BASE}:{rel}")
    return r.stdout


def imports_of(text: str) -> list[str]:
    return [m.group(1) for m in (IMPORT_RE.match(l) for l in text.split("\n")) if m]


def body_of(text: str) -> str:
    lines = text.split("\n")
    if "namespace NumStability" not in lines:
        return ""
    return "\n".join(lines[lines.index("namespace NumStability"):])


def strip_comments(text: str) -> str:
    return LINE_COMMENT.sub("", BLOCK_COMMENT.sub("", text))


def declaration_free(module: str) -> bool:
    return DECL_RE.search(strip_comments(read(module))) is None


def find_control(explicit: str | None) -> Path:
    rec = PHASE + "branches/B0003.json"
    for c in ([Path(explicit)] if explicit else CONTROL_CANDIDATES):
        p = c / rec
        if p.is_file() and hashlib.sha256(p.read_bytes()).hexdigest().upper() == B0003_SHA:
            return c
    raise SystemExit("no control root with the pinned B0003 record; pass --control-root")


def read_lossy(path: Path) -> str:
    with open(path, encoding="utf-8", errors="replace", newline="") as fh:
        return fh.read()


def build_graph() -> dict[str, list[str]]:
    g: dict[str, list[str]] = {}
    for p in ROOT.rglob("*.lean"):
        parts = p.relative_to(ROOT).parts
        if ".lake" in parts:
            continue
        mod = ".".join(parts)[:-5]
        g[mod] = imports_of(read_lossy(p))
    return g


def reach(g: dict[str, list[str]], start: str) -> set[str]:
    seen: set[str] = set()
    frontier = [start]
    while frontier:
        for t in g.get(frontier.pop(), ()):
            if t not in seen:
                seen.add(t)
                frontier.append(t)
    return seen


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--control-root")
    args = ap.parse_args()
    control = find_control(args.control_root)
    print(f"control root: {control}")

    routes = list(csv.DictReader(
        (control / (PHASE + "branches/B0003-declaration-routes.tsv")).open(encoding="utf-8"),
        delimiter="\t"))
    module_routes = list(csv.DictReader(
        (control / (PHASE + "branches/B0003-module-routes.tsv")).open(encoding="utf-8"),
        delimiter="\t"))
    plan = list(csv.DictReader(
        (control / (PHASE + "branches/B0003-test-plan.tsv")).open(encoding="utf-8"),
        delimiter="\t"))
    owners = [r["owner_module"] for r in module_routes]

    # ---------- 1. relocated bodies are byte-identical to their C0001 preimages
    moved_ok = 0
    for owner, dest in MOVES.items():
        rel = "/".join(owner.split(".")) + ".lean"
        pre = body_of(base_blob(rel).decode("utf-8"))
        if not path_of(dest).is_file():
            fail(f"destination missing: {dest}")
            continue
        post = body_of(read(dest))
        if pre != post:
            fail(f"relocated body differs from its C0001 preimage: {owner} -> {dest} "
                 f"({len(pre)} vs {len(post)} bytes)")
        else:
            moved_ok += 1
    print(f"relocated bodies byte-identical: {moved_ok}/{len(MOVES)}")

    # ---------- 2. the five relocated owners are documented import-only wrappers
    for owner, dest in MOVES.items():
        if not declaration_free(owner):
            fail(f"relocated owner still declares something: {owner}")
        imps = imports_of(read(owner))
        if imps != [dest]:
            fail(f"wrapper {owner} imports {imps}, expected exactly [{dest}]")
        if "/-!" not in read(owner):
            fail(f"wrapper {owner} has no module documentation")

    # ---------- 3. Chapter19.Core preserved byte-for-byte, imports unchanged
    core_rel = "/".join(CORE.split(".")) + ".lean"
    if base_blob(core_rel) != path_of(CORE).read_bytes():
        fail(f"{CORE} is not byte-identical to C0001")
    else:
        print(f"{CORE}: byte-identical, {len(imports_of(read(CORE)))} imports retained")

    # ---------- 4. the 59 declaration-free wrappers
    plain = retarget = 0
    for r in module_routes:
        owner, act = r["owner_module"], r["compatibility_action"]
        if not act.startswith("declaration-free"):
            continue
        if not declaration_free(owner):
            fail(f"declaration-free wrapper now declares something: {owner}")
        if "/-!" not in read(owner):
            fail(f"wrapper {owner} has no module documentation")
        rel = "/".join(owner.split(".")) + ".lean"
        was = imports_of(base_blob(rel).decode("utf-8"))
        now = imports_of(read(owner))
        if "retarget" in act:
            want = [RETARGETED[owner] if i in MOVES else i for i in was]
            if now != want:
                fail(f"retargeted wrapper {owner}: imports {now}, expected {want}")
            retarget += 1
        else:
            if now != was:
                fail(f"wrapper {owner} was required to retain its exact imports: "
                     f"{was} -> {now}")
            plain += 1
    print(f"declaration-free wrappers: {plain} import-preserving + {retarget} retargeted")

    # ---------- 5. import graph: acyclic, and no destination reaches Source or a facade
    g = build_graph()
    for m in list(MOVES.values()):
        if m not in g:
            fail(f"destination not in graph: {m}")
    color: dict[str, int] = {}
    cycles: list[list[str]] = []
    sys.setrecursionlimit(200000)

    def dfs(u: str, stack: list[str]) -> None:
        color[u] = 1
        stack.append(u)
        for v in g.get(u, ()):
            if v not in g:
                continue
            if color.get(v, 0) == 0:
                dfs(v, stack)
            elif color[v] == 1:
                cycles.append(stack[stack.index(v):] + [v])
        color[u] = 2
        stack.pop()

    for m in g:
        if color.get(m, 0) == 0:
            dfs(m, [])
    if cycles:
        fail(f"import cycles: {len(cycles)} (first: {' -> '.join(cycles[0])})")
    print(f"import graph: {len(g)} modules, cycles={len(cycles)}")

    owner_set = set(owners)
    for dest in MOVES.values():
        r = reach(g, dest)
        facades = sorted(r & owner_set)
        if facades:
            fail(f"destination {dest} reaches historical facade(s): {facades[:4]}")
        if dest in REUSABLE:
            src = sorted(x for x in r if x.startswith("NumStability.Source"))
            if src:
                fail(f"reusable destination {dest} reaches Source: {src[:4]}")
    print(f"destination reachability: {len(MOVES)} checked, "
          f"{len(REUSABLE)} reusable held free of Source and facades")

    # ---------- 6. no duplicate declaration: every routed name occurs in one file only
    by_dest: dict[str, list[str]] = {}
    for r in routes:
        by_dest.setdefault(r["destination_module"], []).append(r["baseline_declaration_name"])
    for dest, names in by_dest.items():
        if len(names) != len(set(names)):
            fail(f"frozen route lists a duplicate declaration for {dest}")
    print(f"routed declarations: {len(routes)} over {len(by_dest)} destinations, no duplicates")

    # ---------- 7. test matrix
    files = sorted(p for p in TESTROOT.rglob("*.lean"))
    if len(files) != len(plan) + 1:
        fail(f"test files {len(files)} != {len(plan)} planned + 1 aggregate")
    agg = TESTROOT / "All.lean"
    if not agg.is_file():
        fail("missing R11 test aggregate All.lean")
    else:
        agg_text = read_exact(agg)
        if DECL_RE.search(strip_comments(agg_text)):
            fail("R11 test aggregate must be declaration-free")
        agg_imports = imports_of(agg_text)
        if len(agg_imports) != len(plan):
            fail(f"aggregate imports {len(agg_imports)}, expected {len(plan)}")
        if sorted(agg_imports) != agg_imports:
            fail("aggregate imports are not sorted")
        if len(set(agg_imports)) != len(agg_imports):
            fail("aggregate imports contain duplicates")
    planned_targets = {(r["test_class"], r["target"]) for r in plan}
    # Match filenames forward, target -> mangled name. Inverting the mangling would be
    # wrong: `.` -> `_` is not injective in reverse for targets that already contain an
    # underscore, e.g. `Higham19Problem19_10` and `Higham20Theorem20_7`.
    mangled_to_target: dict[tuple[str, str], str] = {}
    for r in plan:
        k = (r["test_class"], r["target"].replace(".", "_"))
        if k in mangled_to_target:
            fail(f"two planned targets share one mangled filename: {k[1]}")
        mangled_to_target[k] = r["target"]
    seen: set[tuple[str, str]] = set()
    for p in files:
        if p.name == "All.lean":
            continue
        rel = p.relative_to(TESTROOT)
        cls = {"Canonical": "canonical_only", "Focused": "focused",
               "OldOnly": "old_only", "Consumer": "protected_consumer"}.get(rel.parts[0])
        if cls is None:
            fail(f"test file outside a planned class directory: {rel}")
            continue
        target = mangled_to_target.get((cls, p.stem))
        if target is None:
            fail(f"test file matches no planned {cls} target: {rel}")
            continue
        imps = imports_of(read_exact(p))
        prod = [i for i in imps if i.startswith("NumStability")]
        if len(prod) != 1:
            fail(f"{rel} imports {len(prod)} production modules, expected exactly 1")
        elif prod[0] != target:
            fail(f"{rel} imports {prod[0]}, expected its target {target}")
        if cls == "canonical_only" and any(i in owner_set for i in imps):
            fail(f"canonical-only test {rel} imports a historical owner")
        seen.add((cls, target))
    for missing in sorted(planned_targets - seen):
        fail(f"planned test target has no test file: {missing}")
    print(f"test matrix: {len(files)} files = {len(plan)} planned + 1 aggregate; "
          f"all targets present")

    # ---------- 8. casefold collisions across the whole tracked tree
    tracked = subprocess.run(["git", "-C", str(ROOT), "ls-files"],
                             capture_output=True, text=True, check=True).stdout.split("\n")
    extra = [str(p.relative_to(ROOT)).replace("\\", "/") for p in TESTROOT.rglob("*.lean")]
    extra += [str(p.relative_to(ROOT)).replace("\\", "/")
              for d in MOVES.values() for p in [path_of(d)]]
    seen_ci: dict[str, str] = {}
    collisions = 0
    for p in [t for t in tracked if t.strip()] + extra:
        k = p.lower()
        if k in seen_ci and seen_ci[k] != p:
            fail(f"casefold collision: {p} vs {seen_ci[k]}")
            collisions += 1
        seen_ci[k] = p
    print(f"casefold collisions: {collisions}")

    if problems:
        print(f"\nFAIL: {len(problems)} static violation(s)")
        for p in problems:
            print("   " + p)
        return 1
    print("\nPASS: the worker tree matches the frozen B0003 route contract")
    return 0


if __name__ == "__main__":
    sys.exit(main())
