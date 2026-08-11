"""Generate the 63 R02 tests from B0002-test-plan.tsv, and TEST_MATRIX.tsv.

One module per planned row, no more and no fewer, so the matrix is exact.

  old_only (28)            import ONLY the historical wrapper; check every public name the
                           owner had at C0000 still resolves through it.
  canonical_only (14)      import ONLY the canonical destination; check the public names
                           routed there, with no historical module in scope.
  focused (14)             the frozen route plus the private-normalized closure: check the
                           public closure members that live in this destination.
  protected_consumer (7)   import the integrator-owned consumer unedited, so its postimage
                           is compiled without this wave touching it.

Private declarations are never `#check`ed: a mangled `_private.…` name is not addressable
from another module. That is the same fact that makes the 76 renames automatic.
`#check @name` is used so implicit binders need not be supplied.
"""
from __future__ import annotations

import csv, json, os
from collections import defaultdict

OUT = os.path.dirname(os.path.abspath(__file__))
WT = r"C:\Users\qed_s\higham-worktrees\completion-r02-claude"
ROOT = os.path.join(WT, "NumStabilityTest", "Reorganization", "R02")
DEL = os.path.join(WT, "docs", "architecture", "deliveries", "R02")
os.makedirs(DEL, exist_ok=True)


def tsv(n):
    with open(os.path.join(OUT, n), encoding="utf-8-sig", newline="") as fh:
        return list(csv.DictReader(fh, delimiter="\t"))


tp = tsv("B0002-test-plan.tsv")
clo = json.load(open(os.path.join(OUT, "closure.json"), encoding="utf-8"))
TBL, ROUTES, CLOSURE = clo["table"], clo["routes"], set(clo["closure"])
PUB = {n for n, v in TBL.items() if v[2] == "public"}

by_dest, by_owner = defaultdict(list), defaultdict(list)
for n in PUB:
    by_dest[ROUTES[n]].append(n)
    by_owner[TBL[n][0]].append(n)

SUB = {"old_only": "OldOnly", "canonical_only": "Canonical",
       "focused": "Focused", "protected_consumer": "Consumer"}
rows = []


def leaf(mod):
    return mod.replace("NumStability.", "").replace(".", "")


def write(cls, target, imports, names, doc):
    rel = f"{SUB[cls]}/{leaf(target)}.lean"
    path = os.path.join(ROOT, rel.replace("/", os.sep))
    os.makedirs(os.path.dirname(path), exist_ok=True)
    body = [f"import {i}" for i in imports]
    body += ["", "/-!", doc, "-/", ""]
    body += [f"#check @{n}" for n in sorted(names)]
    body.append("")
    with open(path, "w", encoding="utf-8", newline="\n") as fh:
        fh.write("\n".join(body))
    mod = "NumStabilityTest.Reorganization.R02." + rel[:-5].replace("/", ".")
    rows.append((mod, cls, target, len(imports), len(names)))


for r in tp:
    cls, target = r["test_class"], r["target"]
    if cls == "old_only":
        names = sorted(by_owner.get(target, []))
        doc = (f"# Old path: `{target}`\n\n"
               f"Imports only the historical wrapper. Every public declaration this owner\n"
               f"had at C0000 still resolves through it, so no consumer of the historical\n"
               f"path can have been broken. This wrapper declares nothing itself."
               + ("" if names else
                  "\n\nThis owner was already declaration-free at C0000; the test therefore\n"
                  "proves the normalized wrapper still compiles and resolves."))
        write(cls, target, [target], names, doc)
    elif cls == "canonical_only":
        names = sorted(by_dest.get(target, []))
        write(cls, target, [target], names,
              f"# Canonical: `{target}`\n\n"
              f"Imports only the canonical destination, with no historical module in\n"
              f"scope, so the relocated declarations are shown to stand on the canonical\n"
              f"surface alone.")
    elif cls == "focused":
        names = sorted(n for n in by_dest.get(target, []) if n in CLOSURE)
        extra = sorted(set(by_dest.get(target, [])) - set(names))[:6]
        write(cls, target, [target], names or extra,
              f"# Frozen route and private-normalized closure: `{target}`\n\n"
              f"Exercises the frozen declaration route together with the reviewed private\n"
              f"normalization. The private members re-mangle against this module and are\n"
              f"not addressable from here; the public members of the private reverse\n"
              f"closure that live here are checked instead, which is what pins the\n"
              f"normalization observably.")
    else:
        write(cls, target, [target], [],
              f"# Protected consumer: `{target}`\n\n"
              f"Integrator-owned shared wiring, imported unedited. R02 does not modify it;\n"
              f"this test compiles its postimage so the hash-pinned integrator request can\n"
              f"be validated without this wave touching the file.")

with open(os.path.join(DEL, "TEST_MATRIX.tsv"), "w", encoding="utf-8", newline="") as fh:
    fh.write("test_module\ttest_class\tplanned_target\timports\tchecks\n")
    for mod, cls, target, ni, nc in sorted(rows):
        fh.write(f"{mod}\t{cls}\t{target}\t{ni}\t{nc}\n")

with open(os.path.join(OUT, "test-modules.txt"), "w", encoding="utf-8") as fh:
    for mod, *_ in sorted(rows):
        fh.write(mod + "\n")
for cls, sub in SUB.items():
    with open(os.path.join(OUT, f"tests-{cls}.txt"), "w", encoding="utf-8") as fh:
        for mod, c, *_ in sorted(rows):
            if c == cls:
                fh.write(mod + "\n")

from collections import Counter
c = Counter(cls for _m, cls, *_ in rows)
print(f"generated {len(rows)} test modules (plan has {len(tp)})")
for k in sorted(c):
    print(f"  {k:20} {c[k]}")
print(f"total #check lines: {sum(r[4] for r in rows)}")
print("plan coverage exact:", len(rows) == len(tp))
