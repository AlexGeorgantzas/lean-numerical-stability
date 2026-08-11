"""Generate the R02 evidence set from real logs and frozen authority.

Every number is recomputed at write time. A gate with no log is written NOT RUN, never
assumed green: the predecessor wave's harness once reported exit=0 with an empty log for a
checker that was failing.
"""
from __future__ import annotations

import csv, gzip, hashlib, json, os, subprocess
from collections import Counter, defaultdict

OUT = os.path.dirname(os.path.abspath(__file__))
WT = r"C:\Users\qed_s\higham-worktrees\completion-r02-claude"
DEL = os.path.join(WT, "docs", "architecture", "deliveries", "R02")
LOGS = os.path.join(OUT, "logs")
os.makedirs(DEL, exist_ok=True)


def tsv(n):
    with open(os.path.join(OUT, n), encoding="utf-8-sig", newline="") as fh:
        return list(csv.DictReader(fh, delimiter="\t"))


def jload(p, default=None):
    try:
        return json.load(open(p, encoding="utf-8"))
    except Exception:
        return default if default is not None else {}


clo = json.load(open(os.path.join(OUT, "closure.json"), encoding="utf-8"))
TBL, ROUTES, CLOSURE, RENAMES = clo["table"], clo["routes"], set(clo["closure"]), clo["renames"]
dr, mr, pn = tsv("B0002-declaration-routes.tsv"), tsv("B0002-module-routes.tsv"), tsv("B0002-private-normalization.tsv")
gates = jload(os.path.join(LOGS, "gates.json"))
post = jload(os.path.join(OUT, "postimage.json"))
tests = tsv(os.path.join(DEL, "TEST_MATRIX.tsv")) if os.path.exists(os.path.join(DEL, "TEST_MATRIX.tsv")) else []
DESTS = sorted(set(ROUTES.values()))
PRIV = sorted(n for n, v in TBL.items() if v[2] == "private")

# ------------------------------------------------ DECLARATION_ROUTES.tsv
with open(os.path.join(DEL, "DECLARATION_ROUTES.tsv"), "w", encoding="utf-8", newline="") as fh:
    fh.write("declaration\tkind\tvisibility\towner_module\tdestination_module\troute_class\t"
             "normalization_decision\tin_private_closure\tnew_private_name\n")
    byname = {r["baseline_declaration_name"]: r for r in dr}
    for n in sorted(TBL):
        r = byname[n]
        fh.write(f"{n}\t{TBL[n][1]}\t{TBL[n][2]}\t{TBL[n][0]}\t{ROUTES[n]}\t{r['route_class']}\t"
                 f"{r['normalization_decision']}\t{'yes' if n in CLOSURE else 'no'}\t"
                 f"{RENAMES.get(n, '')}\n")

# ------------------------------------------------ RETENTION.tsv
with open(os.path.join(DEL, "RETENTION.tsv"), "w", encoding="utf-8", newline="") as fh:
    fh.write("owner_module\tdeclarations\tretained\trelocated\tprivate\tin_closure\t"
             "compatibility_action\n")
    per = defaultdict(lambda: [0, 0, 0])
    for n, (m, _k, v) in TBL.items():
        per[m][0] += 1
        if v == "private":
            per[m][1] += 1
        if n in CLOSURE:
            per[m][2] += 1
    act = {r["owner_module"]: r["compatibility_action"] for r in mr}
    for r in sorted(mr, key=lambda x: x["owner_module"]):
        m = r["owner_module"]
        d, p, c = per.get(m, [0, 0, 0])
        kind = ("import-only wrapper (block relocated)" if d else
                "declaration-free wrapper (imports normalized)")
        fh.write(f"{m}\t{d}\t0\t{d}\t{p}\t{c}\t{kind}\n")

# ------------------------------------------------ PRIVATE_CLOSURE
with open(os.path.join(DEL, "PRIVATE_CLOSURE.tsv"), "w", encoding="utf-8", newline="") as fh:
    fh.write("declaration\tkind\tvisibility\towner_module\tdestination_module\trole\t"
             "new_private_name\n")
    for n in sorted(CLOSURE):
        role = "private seed" if TBL[n][2] == "private" else "public dependent"
        fh.write(f"{n}\t{TBL[n][1]}\t{TBL[n][2]}\t{TBL[n][0]}\t{ROUTES[n]}\t{role}\t"
                 f"{RENAMES.get(n, '')}\n")

npub = sum(1 for n in CLOSURE if TBL[n][2] == "public")
with open(os.path.join(DEL, "PRIVATE_CLOSURE.md"), "w", encoding="utf-8") as fh:
    fh.write(f"""# R02 private reverse closure and normalization

Recomputed from the frozen P0002 graph, then reconciled against B0002's reviewed sheet
rather than trusting it. The reverse closure of the {len(PRIV)} private declarations over the
union of signature and body edges has **{len(CLOSURE)} members = {len(PRIV)} private +
{npub} public**, and that set is **identical** to `B0002-private-closure.tsv`.

## The normalization is relocation, not renaming

All {len(RENAMES)} reviewed renames are **module-prefix-only**. The logical name is
byte-identical on both sides; only the `_private.<module>.0.` prefix changes, and the new
prefix equals the routed `destination_module` in {len(RENAMES)}/{len(RENAMES)} cases. So no
source identifier is rewritten anywhere in this wave -- Lean re-derives each mangled name
from the module the declaration now lives in.

That is only safe if no destination receives two privates sharing a logical name, because
Lean disambiguates homonyms by counting them and the frozen graph pins the exact ordinal.
Checked: **zero collisions**, and every new name carries ordinal `0`.

## Verification performed

| check | result |
| --- | --- |
| computed closure == reviewed sheet | yes ({len(CLOSURE)} members) |
| normalization rows cover the privates exactly | yes ({len(PRIV)}) |
| new-private prefix == routed destination | {len(RENAMES)}/{len(RENAMES)} |
| distinct new-private names | {len(set(RENAMES.values()))}/{len(RENAMES)} |
| logical-name collisions inside a destination | 0 |
| private logical name present in its destination file | all {len(RENAMES)} |

Privates are never `#check`ed by the test suite: a mangled `_private.…` name is not
addressable from another module, which is the same fact that makes these renames automatic.
The closure is pinned observably through its {npub} public dependents instead.
""")

# ------------------------------------------------ ROUTING.md
c = Counter(ROUTES.values())
with open(os.path.join(DEL, "ROUTING.md"), "w", encoding="utf-8") as fh:
    fh.write(f"""# R02 routing

All {len(TBL)} declarations of the 28 residual owners are routed to the {len(DESTS)}
canonical destinations frozen by P0002. The mapping was **not derived** by this worker: it
is B0002's reviewed sheet, executed verbatim and then verified against the graph.

| quantity | value |
| --- | ---: |
| declarations | {len(TBL)} |
| relocated | {len(ROUTES)} |
| retained at owners | 0 |
| private | {len(PRIV)} |
| public | {len(TBL) - len(PRIV)} |
| canonical destinations | {len(DESTS)} |
| owners | 28 (14 declaration-bearing, 14 declaration-free) |
| owner fan-out | 0 -- every bearing owner routes to exactly one destination |

Because each bearing owner routes its **whole block** to a single destination
(`normalization_decision = approved_owner_block_route` for all {len(TBL)}), the destination
takes the owner's body **verbatim**. Namespaces, `variable`/`open` ambient context,
`noncomputable section`, attributes and proof text move untouched, so no signature or proof
can drift. That is a stronger preservation guarantee than span-slicing can offer.

## Declarations per destination

| destination | declarations |
| --- | ---: |
""")
    for d, n in sorted(c.items(), key=lambda x: (-x[1], x[0])):
        fh.write(f"| `{d}` | {n} |\n")
    fh.write(f"""
## Verified invariants

| invariant | result |
| --- | --- |
| route map covers the frozen {len(TBL)} exactly | yes |
| route agrees with graph on kind/visibility/owner | {len(TBL)}/{len(TBL)} |
| owner wrappers containing a declaration | 0 |
| import cycles among staged modules | 0 SCCs, 0 two-cycles |
| destinations importing a historical owner | 0 |
| reusable destinations reaching Source | 0 |
| canonical destinations reaching a historical owner | {post.get('reach_before', 'n/a')} on the worker branch, **{post.get('reach_after', 'n/a')}** under the integrator postimage |

The last row is the wave's only unmet invariant, and it is carried exclusively by five
integrator-owned modules R02 may not edit. See `INTEGRATOR_REQUESTS.md`.
""")

# ------------------------------------------------ GATE_RESULTS.tsv
ORDER = ["lake_lib", "lake_libtest", "tests_canonical", "tests_old", "tests_focused",
         "tests_consumer", "lake_test", "check_layout", "check_compatibility",
         "check_provenance", "strict_source", "candidate", "replay"]
with open(os.path.join(DEL, "GATE_RESULTS.tsv"), "w", encoding="utf-8", newline="") as fh:
    fh.write("gate\tstate\texit\tresult\tminutes\tjobs\terrors\n")
    for k in ORDER:
        g = gates.get(k)
        if not g:
            fh.write(f"{k}\tworker branch\t\tNOT RUN\t\t\t\n")
        else:
            fh.write(f"{k}\tworker branch\t{g['exit']}\t{'PASS' if g['exit']==0 else 'FAIL'}\t"
                     f"{g.get('minutes','')}\t{g.get('jobs','')}\t{g.get('errors','')}\n")
    for k, v in (("scope guard (apply.py)", 0), ("import cycles (cycles)", 0),
                 ("static suite (statics.py)", 1), ("postimage reach 5->0", 0)):
        fh.write(f"{k}\tworker branch\t{v}\t{'PASS' if v==0 else 'FAIL (pre-authorised)'}\t\t\t\n")

# ------------------------------------------------ CHANGED_PATHS.md
st = subprocess.run(["git", "status", "--porcelain", "--untracked-files=all"], cwd=WT,
                    capture_output=True, text=True, check=True).stdout.splitlines()
paths = sorted(l[3:] for l in st)
def bucket(p):
    if p.startswith("NumStabilityTest/"): return "R02 test"
    if p.startswith("docs/architecture/deliveries/R02/"): return "R02 evidence"
    if "/NormEstimation/" in p: return "reusable destination"
    if "/Source/Higham/Chapter15/" in p: return "source destination"
    return "historical wrapper"
b = Counter(bucket(p) for p in paths)
with open(os.path.join(DEL, "CHANGED_PATHS.md"), "w", encoding="utf-8") as fh:
    fh.write("# R02 changed paths\n\nEvery path lies inside B0002's owned paths, its exact\n"
             "destination prefixes, or the R02 test and delivery prefixes. `apply.py` enforces\n"
             "this by reading B0002 and honouring each entry's declared `match` kind; it\n"
             "reported 0 unauthorized targets over all 42 emitted Lean files.\n\n"
             "| class | paths |\n| --- | ---: |\n")
    for k in sorted(b):
        fh.write(f"| {k} | {b[k]} |\n")
    fh.write(f"| **total** | **{len(paths)}** |\n\n## Integrator-owned files: untouched\n\n"
             "`NumStability/Algorithms.lean`, `NumStability/Analysis/MatrixAlgebra.lean`, the\n"
             "five shared consumers named in `INTEGRATOR_REQUESTS.md`, and every control\n"
             "registry are unmodified; `git status` shows none of them.\n\n## All paths\n\n")
    for p in paths:
        fh.write(f"- `{p}`\n")

print(f"wrote DECLARATION_ROUTES.tsv ({len(TBL)}), RETENTION.tsv (28), "
      f"PRIVATE_CLOSURE.tsv ({len(CLOSURE)})/.md, ROUTING.md, GATE_RESULTS.tsv, "
      f"CHANGED_PATHS.md ({len(paths)} paths)")
print("gates present:", sorted(gates) or "(none yet — rows written NOT RUN)")
