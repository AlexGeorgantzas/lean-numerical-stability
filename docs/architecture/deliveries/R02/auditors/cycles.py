"""Detect import cycles among the staged R02 modules before any build.

A missed cycle cost a 42-minute build in the predecessor wave and surfaced as 313
cascading `bad import` lines; this static check finds the same class in under a second.
Runs Tarjan over the staged graph overlaid on the base repository graph, so a cycle that
closes through an unchanged module is visible too.
"""
import json, os, re, sys
IMP = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_'.]+)\s*$", re.M)
OUT = os.path.dirname(os.path.abspath(__file__))
staged = {}
for dp, _d, fs in os.walk(os.path.join(OUT, "emit")):
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.join(dp, f)
            mod = os.path.relpath(p, os.path.join(OUT, "emit")).replace(os.sep, ".")[:-5]
            staged[mod] = set(IMP.findall(open(p, encoding="utf-8").read()))
repo = json.load(open(os.path.join(OUT, "imports.json"), encoding="utf-8"))["imports"]
graph = {m: (staged[m] if m in staged else set(repo.get(m, ()))) for m in set(staged) | set(repo)}
idx, low, on, st, comps, c = {}, {}, set(), [], [], [0]
def sc(v):
    work = [(v, iter(graph.get(v, ())))]
    idx[v] = low[v] = c[0]; c[0] += 1; st.append(v); on.add(v)
    while work:
        node, it = work[-1]; adv = False
        for w in it:
            if w not in graph: continue
            if w not in idx:
                idx[w] = low[w] = c[0]; c[0] += 1; st.append(w); on.add(w)
                work.append((w, iter(graph.get(w, ())))); adv = True; break
            if w in on: low[node] = min(low[node], idx[w])
        if adv: continue
        work.pop()
        if work: low[work[-1][0]] = min(low[work[-1][0]], low[node])
        if low[node] == idx[node]:
            comp = []
            while True:
                w = st.pop(); on.discard(w); comp.append(w)
                if w == node: break
            if len(comp) > 1: comps.append(comp)
sys.setrecursionlimit(10000)
for v in list(graph):
    if v not in idx: sc(v)
wave = [k for k in comps if any(m in staged for m in k)]
pairs = sorted({(a, b) for a, i in staged.items() for b in i
                if b in staged and a in staged.get(b, set()) and a < b})
print(f"staged {len(staged)}  graph {len(graph)}")
print(f"SCCs>1 {len(comps)}  involving staged {len(wave)}  direct 2-cycles {len(pairs)}")
for k in wave[:3]: print("  cycle:", sorted(k)[:6])
for a, b in pairs[:4]: print(f"  {a} <-> {b}")
print("CYCLES OK" if not wave and not pairs else "CYCLES FOUND")
sys.exit(1 if (wave or pairs) else 0)
