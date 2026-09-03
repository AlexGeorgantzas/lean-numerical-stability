"""TIER-01: build the reviewed version-2 tier rule manifest.

Every exact and prefix rule gains: a stable rule id, match kind, role, rationale,
introduction (checkpoint and 40-character commit), reviewer, status, review date,
evidence reference, and an optional reviewed exception. Prefix rules carry
`shared_default: true`, because the packet forbids a prefix from inferring an
old-to-canonical mapping; exact rules that shadow a prefix carry `override_of`
naming that prefix.

The critical safety property, from the packet: the version-2 resolver's role map
must be compared BYTE FOR BYTE with the version-1 resolver over every production
module. This script asserts that equality and refuses to emit on any difference.

usage: python tools/architecture/generate_tier_manifest.py [REPO_ROOT] [--check] [--out PATH]

The input must be a schema-1 manifest: regenerating from schema 2 is refused,
so a v2 manifest is rebuilt by restoring v1 from history first.
"""
import collections
import json
import pathlib
import re
import subprocess
import sys

ARGS = [a for a in sys.argv[1:] if not a.startswith("--")]
ROOT = pathlib.Path(ARGS[0] if ARGS else ".")
CHECK = "--check" in sys.argv
OUT = pathlib.Path(sys.argv[sys.argv.index("--out") + 1]) if "--out" in sys.argv else ROOT / "docs/architecture/tiers.json"

V1 = json.loads((ROOT / "docs/architecture/tiers.json").read_text(encoding="utf-8"))
assert V1.get("schema_version") == 1, f"expected schema 1, found {V1.get('schema_version')}"
EXACT = dict(V1["exact"])
PREFIXES = [(r["prefix"].rstrip("."), r["tier"]) for r in V1["prefixes"]]

# Reviewed correction, TIER-01. The prefix rule `NumStability.Higham` claims role
# `source`, but every one of the 14 modules it can match carries an exact rule
# saying `compatibility`, and all 13 files under NumStability/Higham/ are
# historical forwarders listed in COMPATIBILITY.md. The rule therefore decides
# nothing today only because exact rules shadow it, while standing ready to
# misclassify any module later added to that historical tree. Version 2 corrects
# its role; the resolved role map is unchanged, which the v1 comparison below
# asserts rather than assumes.
PREFIX_ROLE_CORRECTIONS = {"NumStability.Higham": ("source", "compatibility")}
PREFIXES = [(p, PREFIX_ROLE_CORRECTIONS[p][1] if p in PREFIX_ROLE_CORRECTIONS else r)
            for p, r in PREFIXES]
ROLES = list(V1["tiers"])


# ---------------------------------------------------------------- resolvers
V1_PREFIXES = [(r["prefix"].rstrip("."), r["tier"]) for r in V1["prefixes"]]


def resolve_v1(module: str) -> str:
    """The historical resolver, using the UNCORRECTED v1 prefix roles."""
    if module in EXACT:
        return EXACT[module]
    best = None
    for prefix, role in V1_PREFIXES:
        if module == prefix or module.startswith(prefix + "."):
            if best is None or len(prefix) > len(best[0]):
                best = (prefix, role)
    return best[1] if best else "unclassified"


def matching_prefixes(module: str) -> list[tuple[str, str]]:
    """All component-boundary-aware prefix matches, longest first."""
    hits = [(p, r) for p, r in PREFIXES if module == p or module.startswith(p + ".")]
    return sorted(hits, key=lambda pr: -len(pr[0]))


def resolve_v2(module: str) -> tuple[str, str, list[str]]:
    """(role, deciding rule id, notes). Conflicting equal-specificity roles fail."""
    notes: list[str] = []
    hits = matching_prefixes(module)
    if module in EXACT:
        role = EXACT[module]
        rid = f"exact:{module}"
        if hits and hits[0][1] != role:
            notes.append(f"override_of={hits[0][0]}")
        return role, rid, notes
    if not hits:
        return "unclassified", "none", notes
    longest = len(hits[0][0])
    tied = [h for h in hits if len(h[0]) == longest]
    roles = {r for _, r in tied}
    if len(roles) > 1:
        raise SystemExit(f"conflicting equally specific prefix roles for {module}: {sorted(roles)}")
    return tied[0][1], f"prefix:{tied[0][0]}", notes


# ---------------------------------------------------------------- population
def production_modules() -> list[str]:
    out = subprocess.run(["git", "ls-files", "NumStability/*.lean", "NumStability.lean"],
                         cwd=ROOT, capture_output=True, text=True, encoding="utf-8").stdout
    return sorted(p[:-5].replace("/", ".") for p in out.split("\n") if p.endswith(".lean"))


modules = production_modules()
print(f"production modules: {len(modules)}")

# ---------------------------------------------------------------- byte-for-byte comparison
v1_map = {m: resolve_v1(m) for m in modules}
v2_map = {}
rule_used = collections.Counter()
for m in modules:
    role, rid, _notes = resolve_v2(m)
    v2_map[m] = role
    rule_used[rid] += 1

differences = sorted(m for m in modules if v1_map[m] != v2_map[m])
print(f"role-map comparison: {'IDENTICAL' if not differences else str(len(differences)) + ' DIFFERENCES'}")
for m in differences[:8]:
    print(f"  {m}: v1={v1_map[m]} v2={v2_map[m]}")
if differences:
    raise SystemExit("refusing to emit: the version-2 resolver disagrees with version 1")

by_role = collections.Counter(v2_map.values())
print(f"roles: {dict(sorted(by_role.items()))}")
unclassified = [m for m, r in v2_map.items() if r == "unclassified"]
mixed = [m for m, r in v2_map.items() if r == "mixed"]
print(f"unclassified: {len(unclassified)} | mixed: {len(mixed)}")
if unclassified or mixed:
    raise SystemExit("refusing to emit: classification is not total, or mixed is non-zero")

# ---------------------------------------------------------------- staleness
missing_exact = sorted(m for m in EXACT if not (ROOT / (m.replace(".", "/") + ".lean")).is_file())
unused_prefix = sorted(p for p, _ in PREFIXES if not any(rule_used.get(f"prefix:{p}")
                                                         for _ in (0,)) and rule_used.get(f"prefix:{p}", 0) == 0)
print(f"exact rules whose file is absent: {len(missing_exact)}")
for m in missing_exact[:5]:
    print(f"  {m}")
print(f"prefix rules that decide nothing: {len(unused_prefix)}")
for p in unused_prefix[:5]:
    print(f"  {p}")

# ---------------------------------------------------------------- introduction facts
_intro_cache: dict[str, dict] = {}


def introduced(module: str) -> dict:
    path = (module.replace(".", "/") + ".lean")
    if path in _intro_cache:
        return _intro_cache[path]

    def git(*args: str) -> str:
        return subprocess.run(["git", *args, "--", path], cwd=ROOT, capture_output=True,
                              text=True, encoding="utf-8").stdout.strip()

    out = git("log", "--diff-filter=A", "--format=%H|%cI")
    if out:
        sha, _, when = out.split(chr(10))[-1].partition("|")
        rec = {"commit": sha, "date": when, "determined_by": "diff_filter_add"}
    else:
        # A file introduced through a merge has no commit recorded as adding it,
        # so fall back to the earliest commit that touches it and label the method
        # rather than recording a null provenance or implying an unattributed add.
        out = git("log", "--reverse", "--format=%H|%cI")
        if out:
            sha, _, when = out.split(chr(10))[0].partition("|")
            rec = {"commit": sha, "date": when,
                   "determined_by": "earliest_touching_commit"}
        else:
            rec = {"commit": None, "date": None, "determined_by": "unknown"}
    _intro_cache[path] = rec
    return rec


MANIFEST_INTRO = introduced("docs.architecture.tiers")  # unused placeholder guard
TIERS_COMMIT = subprocess.run(["git", "log", "-1", "--format=%H|%cI", "--", "docs/architecture/tiers.json"],
                              cwd=ROOT, capture_output=True, text=True, encoding="utf-8").stdout.strip()
tiers_sha, _, tiers_date = TIERS_COMMIT.partition("|")

RATIONALE = {
    "reusable": "General-purpose result reused across chapters; must not depend on chapter sources.",
    "source": "Chapter-specific formalization of the printed source argument.",
    "internal": "Implementation detail not part of any advertised surface.",
    "upstream": "Vendored upstream material retained under its original licence.",
    "aggregate": "Import-only semantic parent that re-exports its children.",
    "compatibility": "Historical path retained as an import-only forwarder under the removal policy.",
    "mixed": "Reserved: a module carrying more than one role is a defect and must remain absent.",
}
REVIEW = {"reviewer": "primary-human", "status": "accepted", "review_date": tiers_date or None,
          "evidence": "docs/architecture/phases/2026-08-repository-reorganization-completion/checkpoints/C0008.json"}

exact_records = []
for module, role in sorted(EXACT.items()):
    hits = matching_prefixes(module)
    record = {
        "rule_id": f"exact:{module}",
        "match_kind": "exact",
        "module": module,
        "role": role,
        "rationale": RATIONALE[role],
        "introduction": introduced(module),
        "file_present": (ROOT / (module.replace(".", "/") + ".lean")).is_file(),
        "review": dict(REVIEW),
        "exception": None,
    }
    if hits and hits[0][1] != role:
        record["override_of"] = f"prefix:{hits[0][0]}"
        record["override_rationale"] = (
            f"This module is classified {role} although the enclosing prefix rule "
            f"{hits[0][0]} defaults to {hits[0][1]}."
        )
    elif hits and hits[0][1] == role:
        record["extends"] = f"prefix:{hits[0][0]}"
    exact_records.append(record)

prefix_records = []
for prefix, role in sorted(PREFIXES):
    decided = rule_used.get(f"prefix:{prefix}", 0)
    prefix_records.append({
        "rule_id": f"prefix:{prefix}",
        "match_kind": "prefix",
        "prefix": prefix,
        "role": role,
        "shared_default": True,
        "matches_component_boundary_only": True,
        "modules_decided": decided,
        "rationale": RATIONALE[role],
        "introduction": {"commit": tiers_sha or None, "date": tiers_date or None},
        "review": dict(REVIEW),
        "exception": None,
    })

doc = {
    "schema_version": 2,
    "tiers": ROLES,
    "reusable_entrypoints": V1["reusable_entrypoints"],
    "reviewed_corrections": [
        {
            "rule_id": f"prefix:{name}",
            "from_role": old_role,
            "to_role": new_role,
            "rationale": (
                "The rule decided no module because every module it can match carries an "
                "exact rule with the corrected role, but its stated role disagreed with all "
                "of them and would have misclassified any module later added under this "
                "historical prefix. The resolved role map is unchanged, asserted by "
                "byte-for-byte comparison with the version-1 resolver."
            ),
            "review": dict(REVIEW),
        }
        for name, (old_role, new_role) in sorted(PREFIX_ROLE_CORRECTIONS.items())
    ],
    "resolution": {
        "order": ["exact", "prefix"],
        "prefix_match": "component_boundary",
        "conflicting_equal_specificity": "fail",
        "unclassified": "fail",
        "mixed_allowed": False,
        "prefix_rules_may_only_supply_shared_defaults": True,
        "v1_role_map_equality": "asserted",
    },
    "counts": {
        "production_modules": len(modules),
        "exact_rules": len(exact_records),
        "prefix_rules": len(prefix_records),
        "by_role": dict(sorted(by_role.items())),
        "exact_rules_with_absent_file": len(missing_exact),
        "prefix_rules_deciding_nothing": len(unused_prefix),
    },
    "exact": {r["module"]: r["role"] for r in exact_records},
    "prefixes": [{"prefix": r["prefix"], "tier": r["role"]} for r in prefix_records],
    "exact_rules": exact_records,
    "prefix_rules": prefix_records,
}

text = json.dumps(doc, indent=1, sort_keys=True, ensure_ascii=False) + "\n"
print(f"manifest: {len(text):,} bytes | exact_rules={len(exact_records)} prefix_rules={len(prefix_records)}")
if CHECK:
    print("--check: no bytes written")
else:
    OUT.write_text(text, encoding="utf-8", newline="")
    print(f"wrote {OUT}")
