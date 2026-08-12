#!/usr/bin/env python3
"""Audit the exact B0003/R11 worker diff against the frozen C0001 scope.

Run from anywhere:

    python -B docs/architecture/deliveries/R11/CHECK_SCOPE.py [--control-root DIR]
                                                             [--check-changed-paths]

The B0003/P0003/R0003 records are deliberately absent from the worker branch, so the
control artifacts are read from a separate read-only checkout that contains them. The
default candidates below are tried in order; each is accepted only if the B0003 record
hashes to the value this script pins, so a stale or wrong control root is rejected
rather than silently used.

Exit status is 0 when every changed path is authorized and every invariant holds, and
1 on the first violation, with all violations listed.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = "117aa2bb7e61f41e1531a78452f9f7f6cd5b0771"
BRANCH = "codex/reorg-completion-2026-08-r11-qr-ch19"
ACTIVE_CONTROL = "5e075b947a63e84c784afecd00e1f130e21ea659"
PHASE = "docs/architecture/phases/2026-08-repository-reorganization-completion/"
DELIVERY_PREFIX = "docs/architecture/deliveries/R11/"

CONTROL_CANDIDATES = [
    Path(r"C:\Users\qed_s\higham-worktrees\completion-integrator-c0001"),
    Path(r"C:\Users\qed_s\OneDrive\Documents\QED 94"),
]

PINNED = {
    PHASE + "branches/B0003.json":
        "29E5C9D60EB7B8A19F114ED4570BA9C125A3FDF7960C39796A4DDE45A9062519",
    PHASE + "branches/B0003-declaration-routes.tsv":
        "2454049E9B044E97730D16392B641F7E4850F84BB8508C50EFB38DD28390C5C1",
    PHASE + "branches/B0003-module-routes.tsv":
        "4F6FE07CFE955B9096156949C44CF2D2829E0AD73D9157CD958EB66F3C7D6CA3",
    PHASE + "branches/B0003-private-normalization.tsv":
        "12E4D4F517D3678DABA4A11F57D36E22EE4428BC3598D3CA0FC7E41A9323E70E",
    PHASE + "branches/B0003-private-closure.tsv":
        "74FA741BC9C9CCF802ED9999D64DB81E40F4D027A25351CAFF78F67196822145",
    PHASE + "branches/B0003-test-plan.tsv":
        "69BC1C60E80FA92111B2C30930559B6D364AF784AA692265DD1FA646927F3C68",
    PHASE + "projections/P0003.json":
        "750A4A89F0CF0C9BE9481C87B19E6ECBE8E279CF9480BF4C57F5895BCD9EFD55",
    PHASE + "projections/P0003.tsv.gz":
        "31EC591D949DB6041078C036F0CFF74A0A3EE229B35E351DDF999D15F494D60E",
    PHASE + "requests/R0003.json":
        "12580FECDF07C80FBB279BC5A1C6A8CBFF6A052B92D92895A6CD39E375424FD2",
    PHASE + "requests/R0003.patch":
        "E1BFBF147D61FFE2CA08090B91DE362A2C089709221624AB2F9B36F9F4E2F4D3",
    PHASE + "requests/R0003-postimages.tsv":
        "6799789E9E739095C49E409799F17D723C4EE038E2E341105BD38595F26CC5D2",
    PHASE + "selectors/R11.tsv":
        "461D1A0E09A0EADD02B57F3FEB6E097508D02F769A13A11E1CF6896B289A3F23",
}

# The reviewed source outlier: preserved byte-for-byte, so it must NOT appear as changed.
CORE = "NumStability/Source/Higham/Chapter19/Core.lean"
MATRIX_ALGEBRA = "NumStability/Analysis/MatrixAlgebra.lean"

FINAL_COUNTS = {
    "modified": 64,
    "production": 69,
    "tests": 205,
    "relocated": 412,
    "retained": 1065,
    "owners": 65,
}

FORBIDDEN_SUFFIXES = (".olean", ".ilean", ".pyc", ".trace", ".o", ".obj", ".exe",
                      ".dll", ".so", ".dylib", ".class", ".setup.json")
FORBIDDEN_PARTS = {".lake", "benchmark-results", "__pycache__", ".codex"}

DELIVERY_FILES = {
    "CHANGED_PATHS.md", "CHECK_PROJECTION.py", "CHECK_REQUEST_REPLAY.py",
    "CHECK_SCOPE.py", "CHECK_STATIC.py", "DECLARATION_ROUTES.tsv", "DELIVERY.md",
    "GATE_RESULTS.tsv", "INTEGRATOR_REQUESTS.md", "PRIVATE_CLOSURE.md",
    "PRIVATE_CLOSURE.tsv", "PRIVATE_NORMALIZATION.tsv", "PROJECTION.md",
    "RETENTION.tsv", "ROUTING.md", "TEST_MATRIX.tsv",
}

problems: list[str] = []


def fail(msg: str) -> None:
    problems.append(msg)


def git(*args: str, cwd: Path = ROOT) -> str:
    r = subprocess.run(["git", "-C", str(cwd), *args], capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    if r.returncode != 0:
        raise SystemExit(f"git {' '.join(args)} failed: {r.stderr.strip()}")
    return r.stdout


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest().upper()


def find_control(explicit: str | None) -> Path:
    record = PHASE + "branches/B0003.json"
    cands = [Path(explicit)] if explicit else CONTROL_CANDIDATES
    for c in cands:
        p = c / record
        if p.is_file() and sha_bytes(p.read_bytes()) == PINNED[record]:
            return c
    raise SystemExit(
        "no control root with the pinned B0003 record; pass --control-root DIR "
        f"(tried: {', '.join(str(c) for c in cands)})")


def matches(entry: dict, path: str) -> bool:
    return (entry["path"] == path if entry["match"] == "exact"
            else path.startswith(entry["path"]))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--control-root")
    ap.add_argument("--check-changed-paths", action="store_true",
                    help="also require CHANGED_PATHS.md and the final delivery file set")
    args = ap.parse_args()

    control = find_control(args.control_root)
    print(f"control root: {control}")
    for rel, want in PINNED.items():
        p = control / rel
        if not p.is_file():
            fail(f"control artifact missing: {rel}")
        elif sha_bytes(p.read_bytes()) != want:
            fail(f"control artifact hash mismatch: {rel}")
    print(f"pinned control artifacts verified: {len(PINNED)}")

    b0003 = json.loads((control / (PHASE + "branches/B0003.json")).read_text(encoding="utf-8"))
    owned = b0003["owned_paths"]
    dests = b0003["destination_prefixes"]
    forbidden = b0003["forbidden_paths"]
    if b0003["base_sha"] != BASE:
        fail(f"B0003 base_sha {b0003['base_sha']} != {BASE}")
    if b0003["branch_name"] != BRANCH:
        fail(f"B0003 branch_name {b0003['branch_name']} != {BRANCH}")
    if len(owned) != FINAL_COUNTS["owners"]:
        fail(f"expected {FINAL_COUNTS['owners']} owned paths, got {len(owned)}")

    # --- git position
    head = git("rev-parse", "HEAD").strip()
    branch = git("rev-parse", "--abbrev-ref", "HEAD").strip()
    if branch != BRANCH:
        fail(f"on branch {branch}, expected {BRANCH}")
    parents = git("rev-list", "--parents", "-n", "1", "HEAD").split()
    committed = len(parents) > 1 and parents[1] == BASE
    if head != BASE and not committed:
        fail(f"HEAD {head} is neither the base nor a direct child of {BASE}")
    print(f"branch {branch}; HEAD {head[:12]}; "
          f"{'delivery commit on base' if committed else 'uncommitted on base'}")

    # --- changed paths: committed diff if a delivery commit exists, else worktree status
    if committed:
        raw = [l for l in git("diff", "--name-status", BASE, "HEAD").splitlines() if l.strip()]
        changed = [(l.split("\t")[0], l.split("\t")[-1]) for l in raw]
    else:
        changed = []
        for l in git("status", "--porcelain", "--untracked-files=all").splitlines():
            if not l.strip():
                continue
            st, path = l[:2].strip(), l[3:].strip().strip('"')
            changed.append(("A" if st == "??" else st, path))

    for st, path in changed:
        if st.startswith("D"):
            fail(f"deletion is forbidden: {path}")
        if st.startswith("R"):
            fail(f"git rename is forbidden: {path}")
        if path.endswith(FORBIDDEN_SUFFIXES) or set(path.split("/")) & FORBIDDEN_PARTS:
            fail(f"generated artifact must not be tracked: {path}")
        authorized = (any(matches(e, path) for e in owned)
                      or any(matches(e, path) for e in dests))
        if not authorized:
            fail(f"path outside owned_paths and destination_prefixes: {path}")
        hits = [e["path"] for e in forbidden if matches(e, path)]
        if hits:
            fail(f"forbidden path changed: {path} (matched {hits[0]})")

    paths = {p for _, p in changed}
    if CORE in paths:
        fail(f"{CORE} must be preserved byte-for-byte but appears as changed")
    if MATRIX_ALGEBRA in paths:
        fail(f"{MATRIX_ALGEBRA} is read-only for this wave")

    # --- integrator-owned R0003 paths must be untouched
    r0003 = json.loads((control / (PHASE + "requests/R0003.json")).read_text(encoding="utf-8"))
    shared = set(r0003["paths"])
    if len(shared) != 133:
        fail(f"expected 133 R0003 paths, got {len(shared)}")
    for p in sorted(shared & paths):
        fail(f"integrator-owned R0003 path modified by the worker: {p}")

    prod = sorted(p for _, p in changed
                  if not p.startswith(("NumStabilityTest/", DELIVERY_PREFIX)))
    tests = sorted(p for _, p in changed if p.startswith("NumStabilityTest/"))
    delivery = sorted(p for _, p in changed if p.startswith(DELIVERY_PREFIX))
    mod = sum(1 for st, _ in changed if st == "M")
    print(f"changed {len(changed)} = {mod} modified + {len(changed)-mod} added; "
          f"production={len(prod)} tests={len(tests)} delivery={len(delivery)}")

    if mod != FINAL_COUNTS["modified"]:
        fail(f"modified count {mod} != {FINAL_COUNTS['modified']}")
    if len(prod) != FINAL_COUNTS["production"]:
        fail(f"production count {len(prod)} != {FINAL_COUNTS['production']}")
    if len(tests) != FINAL_COUNTS["tests"]:
        fail(f"test count {len(tests)} != {FINAL_COUNTS['tests']}")

    # every owned path except the retained Core outlier must have been touched
    owned_exact = {e["path"] for e in owned if e["match"] == "exact"}
    missing = sorted(owned_exact - paths - {CORE})
    for p in missing:
        fail(f"owned path was never updated: {p}")

    # --- Core really is byte-identical to the base blob
    base_core = subprocess.run(["git", "-C", str(ROOT), "show", f"{BASE}:{CORE}"],
                               capture_output=True).stdout
    now_core = (ROOT / CORE).read_bytes()
    if sha_bytes(base_core) != sha_bytes(now_core):
        fail(f"{CORE} differs from its C0001 blob")
    else:
        print(f"{CORE}: byte-identical to C0001 ({len(now_core)} bytes)")

    # --- route counts from the frozen contract
    import csv as _csv
    routes = list(_csv.DictReader(
        (control / (PHASE + "branches/B0003-declaration-routes.tsv")).open(encoding="utf-8"),
        delimiter="\t"))
    reloc = sum(1 for r in routes if r["destination_module"] != r["baseline_owner_module"])
    ret = len(routes) - reloc
    if reloc != FINAL_COUNTS["relocated"] or ret != FINAL_COUNTS["retained"]:
        fail(f"frozen route split {reloc}/{ret} != "
             f"{FINAL_COUNTS['relocated']}/{FINAL_COUNTS['retained']}")
    print(f"frozen routes: {len(routes)} = {reloc} relocated + {ret} retained")

    if args.check_changed_paths:
        present = {p.name for p in (ROOT / DELIVERY_PREFIX).iterdir() if p.is_file()}
        for f in sorted(DELIVERY_FILES - present):
            fail(f"delivery artifact missing: {f}")
        for f in sorted(present - DELIVERY_FILES):
            fail(f"unexpected delivery artifact: {f}")
        ledger = (ROOT / DELIVERY_PREFIX / "CHANGED_PATHS.md").read_text(encoding="utf-8")
        for _, p in changed:
            if f"`{p}`" not in ledger and not p.startswith(DELIVERY_PREFIX):
                fail(f"CHANGED_PATHS.md does not list {p}")
        print(f"delivery artifacts: {len(present)}; ledger cross-checked")

    if problems:
        print(f"\nFAIL: {len(problems)} scope violation(s)")
        for p in problems:
            print("   " + p)
        return 1
    print("\nPASS: every changed path is authorized and every scope invariant holds")
    return 0


if __name__ == "__main__":
    sys.exit(main())
