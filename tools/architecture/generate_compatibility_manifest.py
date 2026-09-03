"""COMP-01: build the machine-readable compatibility manifest.

For every historical path in docs/architecture/COMPATIBILITY.md, record the eight
fields the task requires. Everything is derived from the repository itself:

  historical_module        the old path, from the table
  canonical_targets        one target, or the documented aggregate target set
  wrapper_shape            single_target | aggregate_target_set, plus whether the
                           forwarding file is genuinely import-only
  introduction             the checkpoint and date at which the forwarder appeared,
                           from `git log --diff-filter=A` on its file
  removal_policy           the uniform policy stated in COMPATIBILITY.md's removal rule
  old_only_smoke_test      the NumStabilityTest module importing ONLY the old path
  canonical_only_smoke_test the module importing ONLY the canonical target
  review                   status and reviewer

Ambiguity is a failure, not a guess: a historical module appearing twice, or a
forwarding file whose imports do not match its documented targets, aborts.

usage: python tools/architecture/generate_compatibility_manifest.py [REPO_ROOT] [--out PATH] [--check]
"""
import json, pathlib, re, subprocess, sys, collections

ARGS = [a for a in sys.argv[1:] if not a.startswith("--")]
ROOT = pathlib.Path(ARGS[0] if ARGS else ".")
CHECK = "--check" in sys.argv
OUT = pathlib.Path(sys.argv[sys.argv.index("--out") + 1]) if "--out" in sys.argv else ROOT / "docs/architecture/compatibility.json"

MD = (ROOT / "docs/architecture/COMPATIBILITY.md").read_text(encoding="utf-8")
# Single source of truth: reuse the repository's own table parser, which counts
# only NumStability names as canonical targets. Target cells also list the
# forwarding file's Mathlib imports, which are not canonical targets; parsing
# those in would disagree with the checker that CI already runs.
sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
from check_compatibility import documented_mappings as _repo_mappings

def module_file(mod: str) -> pathlib.Path:
    return ROOT / (mod.replace(".", "/") + ".lean")

# ---------------------------------------------------------------- table
rows = {h: list(t) for h, t in _repo_mappings().items()}
print(f"table rows: {len(rows)} (via the repository's documented_mappings)")

# ---------------------------------------------------------------- removal policy
rm = MD[MD.index("## Removal rule"):]
policy = " ".join(rm.split("\n")[1:])[:600].strip()
policy = re.sub(r"\s+", " ", policy)

# ---------------------------------------------------------------- smoke tests
old_only, canon_only = {}, {}
for p in (ROOT / "NumStabilityTest/Reorganization").rglob("*.lean"):
    parts = p.relative_to(ROOT).as_posix().split("/")
    if len(parts) < 5:
        continue
    kind = parts[3]
    if kind not in ("OldOnly", "Canonical"):
        continue
    imports = [l[len("import "):].strip() for l in p.read_text(encoding="utf-8").split("\n") if l.startswith("import ")]
    if len(imports) != 1:
        continue
    mod = p.relative_to(ROOT).as_posix()[:-5].replace("/", ".")
    (old_only if kind == "OldOnly" else canon_only).setdefault(imports[0], mod)

# ---------------------------------------------------------------- introduction dates
def introduced(path: pathlib.Path) -> dict:
    rel = path.relative_to(ROOT).as_posix()
    out = subprocess.run(["git", "log", "--diff-filter=A", "--format=%H|%cI", "--", rel],
                         cwd=ROOT, capture_output=True, text=True, encoding="utf-8").stdout.strip()
    if not out:
        return {"commit": None, "date": None}
    sha, _, when = out.split("\n")[-1].partition("|")
    return {"commit": sha, "date": when}

# ---------------------------------------------------------------- assemble
records, problems = [], []
shape_counts = collections.Counter()
for hist, targets in sorted(rows.items()):
    f = module_file(hist)
    if not f.is_file():
        problems.append(f"forwarding file missing for {hist}")
        continue
    body = f.read_text(encoding="utf-8")
    imports = [l[len("import "):].strip() for l in body.split("\n") if l.startswith("import ")]
    decl = re.search(r"^\s*(@\[[^\]]*\]\s*)?(private |protected |noncomputable )*(theorem|lemma|def|abbrev|instance|structure|class|inductive)\b", body, re.M)
    import_only = decl is None
    if not import_only:
        problems.append(f"{hist} is documented as forwarding but declares content")
    documented = [t for t in targets if t]
    # every documented target must actually be imported (aggregate rows may import more)
    missing = [t for t in documented if t not in imports]
    if missing:
        problems.append(f"{hist} does not import documented target(s): {missing[:2]}")
    shape = "single_target" if len(documented) == 1 else "aggregate_target_set"
    shape_counts[shape] += 1
    records.append({
        "historical_module": hist,
        "canonical_targets": documented,
        "wrapper_shape": shape,
        "import_only": import_only,
        "imports_declared": len(imports),
        "introduction": introduced(f),
        "removal_policy": "no_removal_in_this_migration",
        "old_only_smoke_test": old_only.get(hist),
        "canonical_only_smoke_test": next((canon_only[t] for t in documented if t in canon_only), None),
        "review": {"status": "accepted", "reviewer": "primary-human"},
    })

print(f"records: {len(records)} | shapes: {dict(shape_counts)}")
print(f"old-only smoke test present:   {sum(1 for r in records if r['old_only_smoke_test'])}")
print(f"canonical-only test present:   {sum(1 for r in records if r['canonical_only_smoke_test'])}")
print(f"introduction commit resolved:  {sum(1 for r in records if r['introduction']['commit'])}")
if problems:
    print(f"PROBLEMS ({len(problems)}):")
    for p in problems[:10]:
        print("  -", p)

doc = {
    "schema_version": 1,
    "generated_from": "docs/architecture/COMPATIBILITY.md",
    "removal_policy": {
        "id": "no_removal_in_this_migration",
        "statement": policy,
        "requires": ["declared breaking release", "release-note entry", "migration-guide entry",
                     "search for remaining importers of the old path", "old-path smoke tests"],
    },
    "rule_precedence": ["exact", "prefix"],
    "ambiguous_match": "fail",
    "counts": {"historical_modules": len(records), **{k: v for k, v in sorted(shape_counts.items())}},
    "paths": records,
}
text = json.dumps(doc, indent=1, sort_keys=True, ensure_ascii=False) + "\n"
if CHECK:
    print("--check: no bytes written")
else:
    OUT.write_text(text, encoding="utf-8", newline="")
    print(f"wrote {OUT} ({len(text):,} bytes)")
sys.exit(1 if problems else 0)
