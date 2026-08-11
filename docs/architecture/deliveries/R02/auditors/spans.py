"""Authoritative declaration spans for the 28 R02 owners.

Spans come from `.ilean`'s `decls` key (name -> 8-int zero-based range). The
`references` key is use sites and must never be used for this.

A donor is only sound where its copy of an owner file is byte-identical to this
wave's base commit: a span is a position in a source file, so identical text gives
identical ranges regardless of what the donor did elsewhere. Every file is
hash-checked; a mismatch is reported, never trusted. The worker's own base build is
first donor and is authoritative.

Reconciles the three name-space mismatches between P0002 and `.ilean`: privates are
mangled (and `.ilean` stores the mangled form), generated constructors/recursors carry
no span of their own, and `deriving` instances are named after their type with
different capitalisation.
"""
from __future__ import annotations

import collections
import hashlib
import json
import os
import re
import subprocess
import sys

OUT = os.path.dirname(os.path.abspath(__file__))
WR = r"C:\Users\qed_s\higham-worktrees\completion-r02-claude"
SELECTOR = os.path.join(OUT, "selector.tsv")
MANDATED_LINES = None   # not pinned for R02

DONORS = [
    r"C:\Users\qed_s\higham-worktrees\completion-r02-claude",
]

_PRIVATE_RE = re.compile(r"^_private\.(?P<mod>.+?)\.(?P<ord>\d+)\.(?P<rest>.+)$")


def logical_name(n: str) -> str:
    m = _PRIVATE_RE.match(n)
    return m.group("rest") if m else n


def sha(t: str) -> str:
    return hashlib.sha256(t.encode("utf-8")).hexdigest().upper()


def main() -> None:
    rows = []
    with open(SELECTOR, encoding="utf-8-sig") as fh:
        next(fh)
        for line in fh:
            if line.strip():
                rows.append(tuple(line.rstrip("\n").split("\t")))
    print(f"owners: {len(rows)}")

    spans, sources, donor_used, missing = {}, {}, collections.Counter(), []
    total_lines = 0
    for mod, path in rows:
        want = subprocess.run(["git", "show", f"HEAD:{path}"], cwd=WR, capture_output=True,
                              text=True, encoding="utf-8", check=True).stdout
        sources[mod] = want
        total_lines += len(want.splitlines())
        wh = sha(want)
        rel = os.path.join(".lake", "build", "lib", "lean", *mod.split(".")) + ".ilean"
        chosen = None
        for d in DONORS:
            dp, ip = os.path.join(d, path.replace("/", os.sep)), os.path.join(d, rel)
            if not (os.path.exists(dp) and os.path.exists(ip)):
                continue
            with open(dp, encoding="utf-8") as fh:
                if sha(fh.read()) != wh:
                    continue
            chosen = (d, ip)
            break
        if chosen is None:
            missing.append(mod)
            continue
        d, ip = chosen
        donor_used[os.path.basename(d)] += 1
        data = json.load(open(ip, encoding="utf-8"))
        spans[mod] = {n: {"span_start": int(r[0]) + 1, "span_end": int(r[2]) + 1}
                      for n, r in (data.get("decls") or {}).items() if r}

    print(f"source lines at base: {total_lines:,}")
    print("span donors:", dict(donor_used))
    if missing:
        print(f"\nNO hash-matched donor for {len(missing)} owners -> local build required:")
        for m in missing:
            print("   ", m)

    # ---- reconcile against P0002 ------------------------------------------
    clo = json.load(open(os.path.join(OUT, "closure.json"), encoding="utf-8"))
    decls = {n: {"module": v[0], "kind": v[1], "visibility": v[2]}
             for n, v in clo["table"].items()}
    by_mod = {m: sorted(t, key=len, reverse=True) for m, t in spans.items()}
    resolved, unmapped = {}, []
    for name, rec in decls.items():
        mod = rec["module"]
        table = spans.get(mod, {})
        lg = logical_name(name)
        sp, origin = table.get(name) or table.get(lg), "direct"
        if sp is None:
            parent = next((c for c in by_mod.get(mod, ()) if lg.startswith(c + ".")), None)
            if parent:
                sp, origin = table[parent], f"parent:{parent}"
        if sp is None:
            hay, best, blen = lg.lower(), None, 0
            for c in by_mod.get(mod, ()):
                cs = c.rsplit(".", 1)[-1]
                if len(cs) > 3 and cs.lower() in hay and len(cs) > blen:
                    best, blen = c, len(cs)
            if best:
                sp, origin = table[best], f"derived:{best}"
        if sp is None:
            unmapped.append(name)
            continue
        resolved[name] = {"module": mod, "kind": rec["kind"], "visibility": rec["visibility"],
                          "logical": lg, "span_start": sp["span_start"],
                          "span_end": sp["span_end"], "origin": origin}

    print(f"\nmapped: {len(resolved)} / {len(decls)}   unmapped: {len(unmapped)}")
    if unmapped:
        per = collections.Counter(decls[n]["module"].split(".")[-1] for n in unmapped)
        for m, c in per.most_common(15):
            print(f"   {c:5d}  {m}")
        for n in unmapped[:12]:
            print(f"      [{decls[n]['kind']}] {n[:100]}")

    by_origin = collections.Counter(r["origin"].split(":")[0] for r in resolved.values())
    print("origins:", dict(by_origin))
    groups = collections.defaultdict(list)
    for n, r in resolved.items():
        groups[(r["module"], r["span_start"], r["span_end"])].append(n)
    print(f"distinct spans: {len(groups)}   spans with >1 declaration: "
          f"{sum(1 for v in groups.values() if len(v) > 1)}")

    json.dump(spans, open(os.path.join(OUT, "spans.json"), "w", encoding="utf-8"))
    json.dump(sources, open(os.path.join(OUT, "sources.json"), "w", encoding="utf-8"))
    json.dump(resolved, open(os.path.join(OUT, "inventory.json"), "w", encoding="utf-8"))
    print("\nwrote spans.json, sources.json, inventory.json")
    if unmapped or missing:
        sys.exit(1)


if __name__ == "__main__":
    main()
