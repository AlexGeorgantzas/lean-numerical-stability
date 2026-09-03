"""COMP-02 audit: reproduce the packet's isolation census independently.

The packet's claim, at audit revision 8960f2a9, is:

  compatibility mappings   712 historical modules; 645 have a strict one-import
                           declaration-bearing check; gap 67
  strict historical files   1,692 files; 860 contain #check; 831 pure import-only
  canonical surface         2,364 edges to 1,644 unique targets; 1,545 targets
                           have a strict one-import check; gap 99
  strict canonical files    3,129 files; 1,723 contain #check

"Strict one-import" means the test file imports EXACTLY ONE module. "Declaration
bearing" means it contains a #check (or another command exercising a
declaration) rather than being purely an import. Comments are stripped before
classification, per the packet.

usage: python comp02_audit.py [REPO_ROOT] [--json OUT]
"""
import json, pathlib, re, sys, collections

ARGS = [a for a in sys.argv[1:] if not a.startswith("--")]
ROOT = pathlib.Path(ARGS[0] if ARGS else ".")
OUT = pathlib.Path(sys.argv[sys.argv.index("--json") + 1]) if "--json" in sys.argv else None

sys.path.insert(0, str((ROOT / "tools/architecture").resolve()))
from check_compatibility import documented_mappings

BLOCK = re.compile(r"/-.*?-/", re.S)
LINE = re.compile(r"--.*?$", re.M)
CMD = re.compile(r"^\s*#(check|print|eval|guard|reduce)\b", re.M)
OTHER_CMD = re.compile(r"^\s*(example|theorem|lemma|def|instance|abbrev|open|section|namespace)\b", re.M)


def strip_comments(text: str) -> str:
    return LINE.sub("", BLOCK.sub("", text))


def classify(path: pathlib.Path) -> dict:
    raw = path.read_text(encoding="utf-8", errors="replace")
    body = strip_comments(raw)
    imports = [m.group(1) for m in re.finditer(r"^import\s+(\S+)", body, re.M)]
    rest = re.sub(r"^import\s+\S+\s*$", "", body, flags=re.M).strip()
    return {
        "imports": imports,
        "strict": len(imports) == 1,
        "has_check": bool(CMD.search(body)),
        "has_other_command": bool(OTHER_CMD.search(body)),
        "pure_import_only": rest == "",
    }


mappings = documented_mappings()
historical = set(mappings)
edges = [t for ts in mappings.values() for t in ts]
targets = set(edges)

files = sorted((ROOT / "NumStabilityTest").rglob("*.lean"))
strict_hist_files, strict_canon_files = [], []
hist_checked, canon_checked = set(), set()
hist_isolated, canon_isolated = set(), set()
pure_hist, pure_canon = 0, 0
check_hist, check_canon = 0, 0
other_only_hist = 0

for f in files:
    info = classify(f)
    if not info["strict"]:
        continue
    only = info["imports"][0]
    if only in historical:
        strict_hist_files.append(f)
        hist_isolated.add(only)
        if info["has_check"]:
            hist_checked.add(only)
            check_hist += 1
        else:
            if info["pure_import_only"]:
                pure_hist += 1
            elif info["has_other_command"]:
                other_only_hist += 1
    if only in targets:
        strict_canon_files.append(f)
        canon_isolated.add(only)
        if info["has_check"]:
            canon_checked.add(only)
            check_canon += 1
        elif info["pure_import_only"]:
            pure_canon += 1

hist_gap = sorted(historical - hist_checked)
canon_gap = sorted(targets - canon_checked)
canon_no_file = sorted(targets - canon_isolated)
gap_pure_files = sum(
    1 for f in strict_hist_files
    if (lambda i: i["imports"][0] in set(hist_gap) and i["pure_import_only"])(classify(f))
)

rows = [
    ("compatibility mappings", len(historical), len(hist_checked), len(hist_gap), 712, 645, 67),
    ("strict historical files", len(strict_hist_files), check_hist, pure_hist, 1692, 860, 831),
    ("canonical unique targets", len(targets), len(canon_checked), len(canon_gap), 1644, 1545, 99),
    ("strict canonical files", len(strict_canon_files), check_canon, None, 3129, 1723, None),
]
print(f"{'population':26} {'measured':>9} {'checked':>8} {'gap/pure':>9}   {'packet':>7} {'packet':>7} {'packet':>7}")
mismatch = []
for name, m, c, g, pm, pc, pg in rows:
    flag = ""
    if m != pm or c != pc or (g is not None and pg is not None and g != pg):
        flag = "  <-- DIFFERS"
        mismatch.append(name)
    print(f"{name:26} {m:9} {c:8} {str(g):>9}   {pm:7} {pc:7} {str(pg):>7}{flag}")

print(f"\nedges: {len(edges)} (packet 2,364) | unique targets: {len(targets)} (packet 1,644)")
print(f"historical gap modules: {len(hist_gap)} owning {gap_pure_files} pure import-only strict files (packet: 67 owning 101)")
print(f"canonical gap targets: {len(canon_gap)}; with NO isolated file at all: {len(canon_no_file)} (packet: 99 and 5)")
print(f"  no-isolated-file targets: {canon_no_file}")
print(f"overlap of canonical gaps with historical gaps: {len(set(canon_gap) & set(hist_gap))} (packet: 38)")
print(f"historical strict files with another command but no #check: {other_only_hist} (packet: 1)")
if mismatch:
    print(f"\nPOPULATIONS DIFFERING FROM THE PACKET: {mismatch}")
    print("(the packet's audit revision is 8960f2a9; this tree is later, so drift is expected and must be explained)")

if OUT:
    OUT.write_text(json.dumps({
        "historical_gap": hist_gap,
        "canonical_gap": canon_gap,
        "canonical_no_isolated_file": canon_no_file,
        "counts": {
            "historical_modules": len(historical), "historical_checked": len(hist_checked),
            "strict_historical_files": len(strict_hist_files),
            "unique_targets": len(targets), "target_edges": len(edges),
            "canonical_checked": len(canon_checked),
            "strict_canonical_files": len(strict_canon_files),
        },
    }, indent=1), encoding="utf-8")
    print(f"\nwrote {OUT}")
