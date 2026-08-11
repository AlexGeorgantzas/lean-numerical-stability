"""R02 baseline: verify P0002, derive the selector, and reconcile the private closure.

Reads only frozen authority. Recomputes the private reverse closure from the graph and
compares it against B0002's reviewed 123-row closure, so the reviewed sheet is checked
rather than assumed.
"""
from __future__ import annotations

import csv, gzip, hashlib, json, os, sys
from collections import Counter, defaultdict

HERE = os.path.dirname(os.path.abspath(__file__))
EXPECT = {"declarations": 142, "signature_edges": 460, "body_edges": 945,
          "union_edges": 966, "private": 76, "public": 66, "owners": 28}

fail = []


def check(label, got, want):
    ok = got == want
    if not ok:
        fail.append(f"{label}: got {got!r} want {want!r}")
    print(f"  {'OK  ' if ok else 'FAIL'} {label:36} {got}")


def tsv(name):
    with open(os.path.join(HERE, name), encoding="utf-8-sig", newline="") as fh:
        return list(csv.DictReader(fh, delimiter="\t"))


raw = gzip.decompress(open(os.path.join(HERE, "P0002.tsv.gz"), "rb").read())
lines = raw.decode("utf-8").splitlines()
print("P0002 raw sha256", hashlib.sha256(raw).hexdigest().upper())

decls, sig, body = {}, set(), set()
for ln in lines[1:]:
    f = ln.split("\t")
    if f[0] == "declaration":
        decls[f[1]] = {"module": f[2], "kind": f[3], "visibility": f[4]}
    elif f[0] == "edge":
        (sig if f[1] == "signature" else body).add((f[2], f[3]))

print("\n== graph ==")
check("declarations", len(decls), EXPECT["declarations"])
check("signature_edges", len(sig), EXPECT["signature_edges"])
check("body_edges", len(body), EXPECT["body_edges"])
check("union_edges", len(sig | body), EXPECT["union_edges"])
vis = Counter(v["visibility"] for v in decls.values())
check("private", vis["private"], EXPECT["private"])
check("public", vis["public"], EXPECT["public"])
print("  ---- kinds:", dict(Counter(v["kind"] for v in decls.values())))

# ---- selector, from the reviewed module-route sheet -------------------------
mr = tsv("B0002-module-routes.tsv")
check("selector rows", len(mr), EXPECT["owners"])
with open(os.path.join(HERE, "selector.tsv"), "w", encoding="utf-8", newline="") as fh:
    fh.write("module\tpath\n")
    for r in sorted(mr, key=lambda x: x["owner_module"]):
        fh.write(f"{r['owner_module']}\t{r['path']}\n")
bad = [r for r in mr
       if r["path"][:-len(".lean")].replace("/", ".") != r["owner_module"]]
check("selector module==path", len(bad), 0)
graph_owners = {v["module"] for v in decls.values()}
check("graph owners subset of selector", graph_owners <= {r["owner_module"] for r in mr}, True)
check("owners bearing declarations", len(graph_owners), 14)

# ---- route map --------------------------------------------------------------
dr = tsv("B0002-declaration-routes.tsv")
check("route rows", len(dr), EXPECT["declarations"])
check("route covers graph exactly",
      {r["baseline_declaration_name"] for r in dr} == set(decls), True)
mismatch = [r for r in dr
            if decls[r["baseline_declaration_name"]]["visibility"] != r["visibility"]
            or decls[r["baseline_declaration_name"]]["kind"] != r["kind"]
            or decls[r["baseline_declaration_name"]]["module"] != r["baseline_owner_module"]]
check("route agrees with graph on kind/visibility/owner", len(mismatch), 0)

# ---- private normalization -------------------------------------------------
pn = tsv("B0002-private-normalization.tsv")
privs = {n for n, v in decls.items() if v["visibility"] == "private"}
check("normalization rows", len(pn), EXPECT["private"])
check("normalization covers privates exactly", {r["old_private"] for r in pn} == privs, True)
check("all normalization targets distinct", len({r["new_private"] for r in pn}), len(pn))
renamed = sum(1 for r in pn if r["old_private"] != r["new_private"])
print(f"  ---- renamed by reviewed mapping        {renamed} of {len(pn)}")
route_dest = {r["baseline_declaration_name"]: r["destination_module"] for r in dr}
disagree = [r for r in pn if route_dest.get(r["old_private"]) != r["destination_module"]]
check("normalization dest == route dest", len(disagree), 0)

# ---- private reverse closure, recomputed ------------------------------------
rev = defaultdict(set)
for s, d in sig | body:
    rev[d].add(s)
closure, stack = set(privs), list(privs)
while stack:
    for p in rev.get(stack.pop(), ()):
        if p in decls and p not in closure:
            closure.add(p)
            stack.append(p)
pub_in = sorted(n for n in closure if decls[n]["visibility"] == "public")
print("\n== private reverse closure ==")
print(f"  ---- computed closure                  {len(closure)}"
      f"  ({len(privs)} private + {len(pub_in)} public)")
pc = tsv("B0002-private-closure.tsv")
col = next((k for k in pc[0] if "decl" in k.lower() or "name" in k.lower()), list(pc[0])[0])
reviewed = {r[col] for r in pc}
print(f"  ---- reviewed sheet rows               {len(pc)}")
check("computed closure == reviewed closure", closure == reviewed, True)
if closure != reviewed:
    print("     only computed:", sorted(closure - reviewed)[:4])
    print("     only reviewed:", sorted(reviewed - closure)[:4])

json.dump({"table": {n: [v["module"], v["kind"], v["visibility"]] for n, v in decls.items()},
           "privates": sorted(privs), "closure": sorted(closure),
           "routes": {r["baseline_declaration_name"]: r["destination_module"] for r in dr},
           "renames": {r["old_private"]: r["new_private"] for r in pn}},
          open(os.path.join(HERE, "closure.json"), "w", encoding="utf-8"))

print("\nwrote selector.tsv, closure.json")
print("BASELINE OK" if not fail else f"BASELINE MISMATCH ({len(fail)})")
for f_ in fail:
    print("  !!", f_)
sys.exit(1 if fail else 0)
