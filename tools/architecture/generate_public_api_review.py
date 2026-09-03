"""Generate docs/architecture/public-api-review.tsv with the packet's columns.

Rows: the nine reviewed public types (documented in the EVID-05 landing), then one explicit
`unreviewed-candidate` row per (tier, kind) class with its count, so unreviewed status is stated,
not inferred from a filename or a missing test.

usage: python gen_review_tsv.py <presence.json> <out.tsv>
"""
import collections
import json
import sys

presence = json.load(open(sys.argv[1], encoding="utf-8"))
COLS = ["name", "owner_module", "tier", "kind", "selection_reason", "api_status", "doc_policy",
        "source_locator", "canonical_tests", "compatibility_tests", "entrypoints", "accountable_owner",
        "reviewer_status", "rationale", "removal_release"]
rows = ["\t".join(COLS)]
for tier, f, ln, kind, name in presence["type_gaps"]:
    mod = f[:-5].replace("/", ".")
    rows.append("\t".join([
        name, mod, tier, kind, "major-by-default:public-type", "major", "docstring-required",
        f"{f}:{ln}", "see entrypoints.json isolated_test of the owning chapter root", "see compatibility.json",
        "reachable from NumStability.Source (advertised)", "primary-human", "primary-human/accepted",
        "public type documented in the EVID-05 landing from its surrounding code", "n/a"]))
classes = collections.Counter()
for tier, f, ln, kind, name in presence["gaps"]:
    if kind not in ("structure", "class", "inductive"):
        classes[(tier, kind)] += 1
for (tier, kind), n in sorted(classes.items()):
    rows.append("\t".join([
        f"<class:{tier}/{kind}:{n} undocumented>", "-", tier, kind,
        "major-by-default" if kind in ("def", "abbrev", "opaque") else "promotion-pending",
        "unreviewed-candidate", "ratchet:no-new-undocumented", "-", "-", "-", "-", "primary-human",
        "unreviewed", "inherited debt recorded by fingerprint in public-api-baseline.json; API status requires per-row review", "-"]))
open(sys.argv[2], "w", encoding="utf-8", newline="\n").write("\n".join(rows) + "\n")
print(f"wrote {sys.argv[2]}: {len(rows) - 1} rows")
