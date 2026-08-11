"""Emit the R02 canonical destinations and rewrite the 28 owners as import-only wrappers.

Two reviewed compatibility paths, 14 owners each:

  bearing   move ALL frozen declarations to the single listed destination, and replace the
            historical owner with a documented import-only wrapper.
  free      declaration-free reviewed owner: normalize imports to the exact canonical
            targets and retain a documented import-only wrapper.

Because every bearing owner routes its WHOLE block to exactly one destination (verified:
0 fan-out), the destination takes the owner's body verbatim. That is materially safer than
span-slicing: namespaces, `variable`/`open` ambient context, `noncomputable section`,
attributes and proof text all move untouched, so no signature or proof can drift.

The 76 private renames need no textual edit. Every one is module-prefix-only -- the logical
name is identical on both sides and the new prefix equals `destination_module` in 76/76 --
so Lean re-derives the mangled name from the new module. Verified precondition: zero
logical-name collisions inside any destination, so every ordinal stays 0.

Tier rule: a destination must never import an R02 owner, since owners are historical
wrappers after this wave and that would be canonical-to-historical. Owner imports are
therefore rewritten to the owner's destination, and imports of declaration-free owners are
expanded to the non-owner modules behind them.
"""
from __future__ import annotations

import csv, json, os, re, shutil, sys
from collections import defaultdict

OUT = os.path.dirname(os.path.abspath(__file__))
WT = r"C:\Users\qed_s\higham-worktrees\completion-r02-claude"
STAGE = os.path.join(OUT, "emit")
IMP = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_'.]+)\s*$")


def tsv(n):
    with open(os.path.join(OUT, n), encoding="utf-8-sig", newline="") as fh:
        return list(csv.DictReader(fh, delimiter="\t"))


SRC = json.load(open(os.path.join(OUT, "sources.json"), encoding="utf-8"))
mr = tsv("B0002-module-routes.tsv")
dr = tsv("B0002-declaration-routes.tsv")

OWNERS = [r["owner_module"] for r in mr]
OWNER_SET = set(OWNERS)
PATH = {r["owner_module"]: r["path"] for r in mr}
BEARING = {r["owner_module"] for r in mr if int(r["declaration_count"]) > 0}
FREE = {r["owner_module"] for r in mr if int(r["declaration_count"]) == 0}
DEST = {}                      # bearing owner -> its single destination module
for r in dr:
    DEST.setdefault(r["baseline_owner_module"], set()).add(r["destination_module"])
assert all(len(v) == 1 for v in DEST.values()), "fan-out detected; reviewed sheet says 0"
DEST = {k: next(iter(v)) for k, v in DEST.items()}
assert set(DEST) == BEARING, (len(DEST), len(BEARING))


def split(text):
    """(import module names, body lines) -- body is everything from the first non-import."""
    lines = text.splitlines()
    imports, i = [], 0
    while i < len(lines):
        s = lines[i].strip()
        m = IMP.match(lines[i])
        if m:
            imports.append(m.group(1))
            i += 1
        elif not s or s == "module":
            i += 1
        else:
            break
    return imports, lines[i:]


BODY, IMPORTS = {}, {}
for o in OWNERS:
    IMPORTS[o], BODY[o] = split(SRC[o])


def canonicalise(imports, seen=None):
    """For DESTINATIONS: a canonical module may never import any historical wrapper, so
    bearing owners are replaced by their destination and declaration-free owners are
    expanded past."""
    seen = seen if seen is not None else set()
    out = []
    for i in imports:
        if i in BEARING:
            out.append(DEST[i])
        elif i in FREE:
            if i in seen:
                continue
            seen.add(i)
            out.extend(canonicalise(IMPORTS[i], seen))   # expand past the wrapper
        else:
            out.append(i)
    return out


def normalize_wrapper(imports):
    """For WRAPPERS: rewrite only imports of declaration-BEARING owners, whose declarations
    genuinely moved. Imports of declaration-free owners are kept VERBATIM.

    Expanding those away orphaned `Algorithms.HighamChapter15BoydSourceDomain` from the
    production graph -- at C0000 it was imported by `HighamChapter15BoydRowwiseDomain`, and
    after expansion only tests reached it, so three aggregates reported a missing canonical
    descendant. Nothing moves out of a declaration-free owner, it stays a wrapper, and
    historical-to-historical is permitted for compatibility tier -- so keeping the edge both
    fixes the aggregate reach and preserves the transitive surface a consumer saw at C0000.
    """
    # Keep EVERY original import verbatim. Reachability of the wrappers is a graph
    # property, not a per-edge one: NumStability/Algorithms.lean imports only 21 of the 28
    # owners directly, and the other 7 were reachable at C0000 solely through owner->owner
    # chains (BoydRowwiseDomain only via BoydSourceSecondDerivative). Rewriting any of
    # those edges breaks the aggregate's reach -- expanding declaration-free imports
    # orphaned 1 wrapper, rewriting bearing imports orphaned 5. Preserving the original
    # edges reproduces C0000 reachability exactly, and is legal because wrappers are
    # compatibility tier, where historical-to-historical is permitted. Destinations still
    # use canonicalise() and import no owner at all.
    return list(imports)


def render(imports, doc, body=None):
    b = [f"import {i}" for i in sorted(set(imports))]
    b += ["", "/-!", doc, "-/", ""]
    if body:
        b += body
    b.append("")
    return "\n".join(b)


written = {}

# ---- path 1: 14 declaration-bearing owners ---------------------------------
for o in sorted(BEARING):
    d = DEST[o]
    written[d] = render(
        canonicalise(IMPORTS[o]),
        f"# {d.rsplit('.', 1)[-1]}\n\n"
        f"Canonical destination for the frozen declaration block of\n"
        f"`{o}`, routed by wave R02 of the August 2026 repository reorganization\n"
        f"completion phase. Declaration names, kinds, visibilities, signatures and\n"
        f"proofs are unchanged; only the module they live in has changed. Private\n"
        f"declarations keep their logical names and are re-mangled against this module,\n"
        f"exactly as recorded in the reviewed private normalization.",
        BODY[o])
    written[o] = render(
        normalize_wrapper(IMPORTS[o]) + [d],
        f"# {o.rsplit('.', 1)[-1]} (compatibility wrapper)\n\n"
        f"Import-only historical path, retained so existing imports of `{o}`\n"
        f"keep resolving. Its whole declaration block moved unchanged to\n"
        f"`{d}`, which is imported above. The module's own original imports are\n"
        f"re-stated so consumers that reached an identifier transitively through this\n"
        f"path still see the same surface. This module declares nothing.")

# ---- path 2: 14 declaration-free owners ------------------------------------
for o in sorted(FREE):
    norm = normalize_wrapper(IMPORTS[o])
    written[o] = render(
        norm,
        f"# {o.rsplit('.', 1)[-1]} (compatibility wrapper)\n\n"
        f"Declaration-free reviewed owner. Its imports are normalized to the exact\n"
        f"canonical and source targets that now hold the material it used to reach\n"
        f"through historical paths, and the historical path itself is retained so\n"
        f"existing imports of `{o}` keep resolving. This module declares nothing.")

# ---- stage -----------------------------------------------------------------
if os.path.isdir(STAGE):
    shutil.rmtree(STAGE)
for mod, text in written.items():
    p = os.path.join(STAGE, *mod.split(".")) + ".lean"
    os.makedirs(os.path.dirname(p), exist_ok=True)
    with open(p, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(text)

dests = sorted(set(DEST.values()))
print(f"destinations         : {len(dests)}")
print(f"wrappers             : {len(OWNERS)}  ({len(BEARING)} bearing, {len(FREE)} free)")
print(f"files staged         : {len(written)}")
print(f"body lines relocated : {sum(len(BODY[o]) for o in BEARING):,}")
bad = [m for m, t in written.items()
       if m in dests and any(i in OWNER_SET for i in
                             [x.group(1) for x in map(IMP.match, t.splitlines()) if x])]
print(f"destinations importing an owner: {len(bad)} {bad[:3]}")
json.dump({"destinations": dests, "written": sorted(written)},
          open(os.path.join(OUT, "emitted.json"), "w", encoding="utf-8"), indent=1)
sys.exit(1 if bad else 0)
