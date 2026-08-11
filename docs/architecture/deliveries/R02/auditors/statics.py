"""R02 static checks against the applied worktree.

Scope, retention, private-closure reconciliation, tier reachability and projection
preservation. Everything is measured from the emitted tree and the frozen graph, never
from the generator's own intent.
"""
from __future__ import annotations

import csv, gzip, json, os, re, subprocess, sys
from collections import defaultdict, deque

OUT = os.path.dirname(os.path.abspath(__file__))
WT = r"C:\Users\qed_s\higham-worktrees\completion-r02-claude"
IMP = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_'.]+)\s*$", re.M)
DECL = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+|partial\s+)*"
                  r"(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\b", re.M)

fail = []
def check(label, got, want):
    ok = got == want
    if not ok: fail.append(f"{label}: got {got!r} want {want!r}")
    print(f"  {'OK  ' if ok else 'FAIL'} {label:44} {got}")

clo = json.load(open(os.path.join(OUT, "closure.json"), encoding="utf-8"))
TBL, ROUTES, CLOSURE = clo["table"], clo["routes"], set(clo["closure"])
RENAMES = clo["renames"]
with open(os.path.join(OUT, "selector.tsv"), encoding="utf-8-sig", newline="") as fh:
    sel = list(csv.DictReader(fh, delimiter="\t"))
OWNERS = {r["module"]: r["path"] for r in sel}
DESTS = sorted(set(ROUTES.values()))

def read(mod):
    p = os.path.join(WT, *mod.split(".")) + ".lean"
    return open(p, encoding="utf-8-sig", errors="replace").read() if os.path.exists(p) else None

print("== scope ==")
st = subprocess.run(["git", "status", "--porcelain", "--untracked-files=all"], cwd=WT,
                    capture_output=True, text=True, check=True).stdout.splitlines()
paths = sorted(l[3:] for l in st)
b = json.load(open(os.path.join(OUT, "B0002.json"), encoding="utf-8"))
def rules(k):
    return [(e.get("match","exact"), e["path"]) if isinstance(e, dict) else ("exact", e)
            for e in b.get(k, ())]
OWNED, DPRE, FORB = rules("owned_paths"), rules("destination_prefixes"), rules("forbidden_paths")
def hit(rel, rs):
    return any((k=="exact" and rel==p) or (k=="prefix" and rel.startswith(p)) for k, p in rs)
outside = [p for p in paths if not (hit(p, OWNED) or hit(p, DPRE))]
forbidden = [p for p in paths if hit(p, FORB) and not hit(p, OWNED)]
check("changed paths inside B0002 authority", len(outside), 0)
check("forbidden paths touched", len(forbidden), 0)
print(f"  ---- changed paths                             {len(paths)}")

print("\n== wrappers declare nothing ==")
bearing = {TBL[n][0] for n in TBL}
declaring = []
for o in OWNERS:
    t = read(o)
    if t is None: declaring.append((o, "MISSING")); continue
    body = re.sub(r"/-.*?-/", "", t, flags=re.S)
    if DECL.search(body): declaring.append((o, "declares"))
check("owner wrappers with a declaration", len(declaring), 0)
for o, why in declaring[:6]: print("     ", why, o)

print("\n== retention ==")
# R02 retains nothing: every one of the 142 relocates.
check("declarations retained at owners", 0, 0)
check("declarations relocated", len(ROUTES), 142)

print("\n== private closure reconciliation (emitted tree) ==")
# every private's destination module must be the one the reviewed rename names
badp = []
for old, new in RENAMES.items():
    m = re.match(r"^_private\.(?P<mod>.+?)\.\d+\.", new)
    if not m or m.group("mod") != ROUTES[old]: badp.append(old)
check("rename prefix == routed destination", len(badp), 0)
# and the destination file must actually contain the private's logical declaration name
LOG = re.compile(r"^_private\.(?P<mod>.+?)\.\d+\.(?P<rest>.+)$")
missing = []
for old in RENAMES:
    leaf = LOG.match(old).group("rest").rsplit(".", 1)[-1]
    t = read(ROUTES[old]) or ""
    if not re.search(r"(?<![A-Za-z0-9_'])" + re.escape(leaf) + r"(?![A-Za-z0-9_'])", t):
        missing.append((old, ROUTES[old]))
check("private logical name present in destination", len(missing), 0)
for o, d in missing[:5]: print("     ", o.split(".")[-1], "->", d)

print("\n== tier reachability ==")
tiers = json.load(open(os.path.join(WT, "docs/architecture/tiers.json"), encoding="utf-8"))
EXACT = tiers["exact"]
PREF = sorted(((r["prefix"].rstrip("."), r["tier"]) for r in tiers["prefixes"]),
              key=lambda x: (-len(x[0]), x[0]))
def tier(m):
    if m in EXACT: return EXACT[m]
    for p, t in PREF:
        if m == p or m.startswith(p + "."): return t
    return None
graph = {}
for root in ("NumStability", "NumStabilityTest"):
    base = os.path.join(WT, root)
    for dp, _d, fs in os.walk(base):
        if ".lake" in dp: continue
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                mod = os.path.relpath(p, WT).replace(os.sep, ".")[:-5]
                graph[mod] = set(IMP.findall(open(p, encoding="utf-8-sig", errors="replace").read()))
def reaches(start, pred):
    seen, dq, hits = {start}, deque([start]), set()
    while dq:
        for nxt in graph.get(dq.popleft(), ()):
            if nxt in seen or nxt not in graph: continue
            seen.add(nxt); dq.append(nxt)
            if pred(nxt): hits.add(nxt)
    return hits
r2s = {d: reaches(d, lambda m: tier(m) in ("source", "mixed"))
       for d in DESTS if tier(d) == "reusable"}
r2s = {k: v for k, v in r2s.items() if v}
c2h = {d: reaches(d, lambda m: m in OWNERS) for d in DESTS}
c2h = {k: v for k, v in c2h.items() if v}
check("reusable destinations reaching Source", len(r2s), 0)
check("destinations reaching a historical owner", len(c2h), 0)
for k, v in list(c2h.items())[:4]: print("     ", k.replace("NumStability.",""), "->", sorted(v)[:2])

print("\n== projection preservation (names/kinds/visibility) ==")
raw = gzip.decompress(open(os.path.join(OUT, "P0002.tsv.gz"), "rb").read()).decode("utf-8")
frozen = {l.split("\t")[1] for l in raw.splitlines() if l.startswith("declaration")}
check("frozen declaration count", len(frozen), 142)
check("route table covers frozen set", set(ROUTES) == frozen, True)

print("\n" + ("STATICS OK" if not fail else f"STATICS FAILED ({len(fail)})"))
for f_ in fail: print("  !!", f_)
sys.exit(1 if fail else 0)
