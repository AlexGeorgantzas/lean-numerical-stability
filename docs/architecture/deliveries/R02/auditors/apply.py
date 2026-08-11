"""Copy the staged R02 emit into the worktree, refusing any path B0002 does not authorize.

The guard reads B0002 itself and honours each entry's declared `match` kind, so it cannot
drift from the branch record. Forbidden paths are rejected structurally, not by convention.

Stale-file sweep is deliberately restricted to production destination prefixes: B0002's
destination prefixes also cover the R02 test and delivery trees, and sweeping those deleted
every generated test module in the predecessor wave.

Usage: python apply.py [--apply]
"""
from __future__ import annotations

import json, os, shutil, subprocess, sys

OUT = os.path.dirname(os.path.abspath(__file__))
WT = r"C:\Users\qed_s\higham-worktrees\completion-r02-claude"
STAGE = os.path.join(OUT, "emit")

b = json.load(open(os.path.join(OUT, "B0002.json"), encoding="utf-8"))


def rules(k):
    return [(e.get("match", "exact"), e["path"]) if isinstance(e, dict) else ("exact", e)
            for e in b.get(k, ())]


OWNED, DESTS, FORB = rules("owned_paths"), rules("destination_prefixes"), rules("forbidden_paths")


def hit(rel, rs):
    return any((k == "exact" and rel == p) or (k == "prefix" and rel.startswith(p))
               for k, p in rs)


targets = []
for dp, _d, fs in os.walk(STAGE):
    for f in fs:
        if f.endswith(".lean"):
            src = os.path.join(dp, f)
            targets.append((src, os.path.relpath(src, STAGE).replace(os.sep, "/")))

auth, rej = [], []
for src, rel in targets:
    if hit(rel, FORB) and not hit(rel, OWNED):
        rej.append(("FORBIDDEN", rel))
    elif hit(rel, OWNED) or hit(rel, DESTS):
        auth.append((src, rel))
    else:
        rej.append(("UNAUTHORIZED", rel))

print(f"staged {len(targets)}  authorized {len(auth)}  rejected {len(rej)}")
print(f"  owner wrappers {sum(1 for _s, r in auth if hit(r, OWNED))}")
print(f"  destinations   {sum(1 for _s, r in auth if hit(r, DESTS) and not hit(r, OWNED))}")
for k, r in rej[:10]:
    print(f"  {k}: {r}")
if rej:
    sys.exit(f"refusing to apply: {len(rej)} unauthorized targets")

if "--apply" not in sys.argv:
    print("\ndry run (pass --apply to write)")
    sys.exit(0)

tracked = set(subprocess.run(["git", "ls-files"], cwd=WT, capture_output=True, text=True,
                             check=True).stdout.split())
keep = {rel for _s, rel in auth}
SWEEP = [p for k, p in DESTS
         if p.startswith("NumStability/") and not p.startswith("NumStabilityTest/")]
removed = 0
for prefix in SWEEP:
    root = os.path.join(WT, prefix.replace("/", os.sep))
    if not os.path.isdir(root):
        continue
    for dp, _d, fs in os.walk(root):
        for f in fs:
            if not f.endswith(".lean"):
                continue
            rel = os.path.relpath(os.path.join(dp, f), WT).replace(os.sep, "/")
            if rel not in keep and rel not in tracked:
                os.remove(os.path.join(dp, f))
                removed += 1

for src, rel in auth:
    dst = os.path.join(WT, rel.replace("/", os.sep))
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    shutil.copyfile(src, dst)

st = subprocess.run(["git", "status", "--porcelain"], cwd=WT, capture_output=True,
                    text=True, check=True).stdout.splitlines()
print(f"\nAPPLIED {len(auth)} files; removed {removed} stale untracked destination modules")
print(f"git status: {len(st)} entries "
      f"({sum(1 for l in st if l.startswith(' M'))} modified, "
      f"{sum(1 for l in st if l.startswith('??'))} untracked)")
