"""Disposable C0000 postimage for the five integrator-owned carriers.

Proves that retargeting those five files drives `destinations reaching a historical owner`
from 5 to 0, and emits an executable forward/reverse replay pair.

The effect is computed on the import graph rather than by editing the worktree, because the
gate battery holds the worktree while it builds; a virtual overlay is exact for a
reachability question and cannot race the build. `replay.ps1` applies the same change to a
disposable C0000 checkout for the integrator.
"""
from __future__ import annotations

import hashlib, json, os, re, subprocess
from collections import deque

OUT = os.path.dirname(os.path.abspath(__file__))
WT = r"C:\Users\qed_s\higham-worktrees\completion-r02-claude"
BASE = "b1b18772d80185ec08f49c818919558645c330a1"
IMP = re.compile(r"^\s*(?:(?:public|private|meta)\s+)*import\s+([A-Za-z0-9_'.]+)\s*$", re.M)

RETARGET = {
    "NumStability.Algorithms.NormEstimation.PNorm.Endpoints.ConvergenceStatements":
        "NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Square",
    "NumStability.Algorithms.NormEstimation.PNorm.Endpoints.PNormRectangular":
        "NumStability.Algorithms.NormEstimation.PNorm.OneAndInfinityNorms.Rectangular",
}
CARRIERS = [
    "NumStability/Algorithms/NormEstimation/PNorm/All.lean",
    "NumStability/Algorithms/NormEstimation/PNorm/Rectangular/RectangularTermination.lean",
    "NumStability/Source/Higham/Chapter15/Lemma02/PNormPowerMethod/PNormRectangular.lean",
    "NumStability/Source/Higham/Chapter15/Section02/Boyd/EndpointTermination/ConvergenceStatements.lean",
    "NumStability/Source/Higham/Chapter15/Section02/Boyd/EndpointTermination/RectangularTermination.lean",
]


def git(*a):
    return subprocess.run(["git"] + list(a), cwd=WT, capture_output=True, check=True).stdout


def blob(rel):
    return git("rev-parse", f"{BASE}:{rel}").decode().strip()


def text(rel):
    return git("show", f"{BASE}:{rel}").decode("utf-8", errors="replace")


# ---- build the graph: repo at base, overlaid with R02 emit -------------------
graph = {}
for root in ("NumStability", "NumStabilityTest"):
    for dp, _d, fs in os.walk(os.path.join(WT, root)):
        if ".lake" in dp:
            continue
        for f in fs:
            if f.endswith(".lean"):
                p = os.path.join(dp, f)
                mod = os.path.relpath(p, WT).replace(os.sep, ".")[:-5]
                graph[mod] = set(IMP.findall(
                    open(p, encoding="utf-8-sig", errors="replace").read()))

clo = json.load(open(os.path.join(OUT, "closure.json"), encoding="utf-8"))
DESTS = sorted(set(clo["routes"].values()))
with open(os.path.join(OUT, "selector.tsv"), encoding="utf-8-sig") as fh:
    OWNERS = {l.split("\t")[0] for l in fh.read().splitlines()[1:] if l.strip()}


def reach_count(g):
    hits = {}
    for d in DESTS:
        seen, dq = {d}, deque([d])
        found = set()
        while dq:
            for n in g.get(dq.popleft(), ()):
                if n in seen or n not in g:
                    continue
                seen.add(n)
                dq.append(n)
                if n in OWNERS:
                    found.add(n)
        if found:
            hits[d] = sorted(found)
    return hits


before = reach_count(graph)
print(f"before postimage: destinations reaching a historical owner = {len(before)}")

# ---- apply the retarget virtually -------------------------------------------
patch_fwd, patch_rev, rows = [], [], []
for rel in CARRIERS:
    mod = rel[:-len(".lean")].replace("/", ".")
    pre = text(rel)
    post = pre
    for old, new in RETARGET.items():
        post = re.sub(rf"^import {re.escape(old)}\s*$", f"import {new}", post, flags=re.M)
    # keep the import block sorted and duplicate-free
    lines = post.splitlines()
    idx = [i for i, l in enumerate(lines) if l.startswith("import ")]
    if idx:
        block = sorted({lines[i].strip() for i in idx})
        lines = lines[:idx[0]] + block + lines[idx[-1] + 1:]
        post = "\n".join(lines) + ("\n" if pre.endswith("\n") else "")
    changed = post != pre
    rows.append({"path": rel, "c0000_blob": blob(rel), "changed": changed,
                 "postimage_sha256": hashlib.sha256(post.encode()).hexdigest().upper(),
                 "endpoint_refs_before": len(re.findall(r"PNorm\.Endpoints\.", pre)),
                 "endpoint_refs_after": len(re.findall(r"PNorm\.Endpoints\.", post))})
    graph[mod] = set(IMP.findall(post))
    patch_fwd.append((rel, post))
    patch_rev.append((rel, pre))

after = reach_count(graph)
print(f"after  postimage: destinations reaching a historical owner = {len(after)}")
for d, v in list(after.items())[:4]:
    print("   still:", d.replace("NumStability.", ""), "->", v[:2])

os.makedirs(os.path.join(OUT, "postimage"), exist_ok=True)
for rel, t in patch_fwd:
    p = os.path.join(OUT, "postimage", rel.replace("/", "__"))
    open(p, "w", encoding="utf-8", newline="\n").write(t)
for rel, t in patch_rev:
    p = os.path.join(OUT, "postimage", "REVERSE__" + rel.replace("/", "__"))
    open(p, "w", encoding="utf-8", newline="\n").write(t)

json.dump({"base": BASE, "retarget": RETARGET, "rows": rows,
           "reach_before": len(before), "reach_after": len(after)},
          open(os.path.join(OUT, "postimage.json"), "w", encoding="utf-8"), indent=1)
print("\nper-file:")
for r in rows:
    print(f"  {'CHANGED' if r['changed'] else 'no-change'}  {r['path'].split('/')[-1]:34} "
          f"blob={r['c0000_blob'][:12]}  endpointRefs {r['endpoint_refs_before']}->{r['endpoint_refs_after']}")
print("\nwrote postimage/ and postimage.json")
print("POSTIMAGE OK" if not after else "POSTIMAGE INCOMPLETE")
