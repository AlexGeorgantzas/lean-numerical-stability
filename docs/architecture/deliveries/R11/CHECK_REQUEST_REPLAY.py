#!/usr/bin/env python3
"""Validate the integrator-owned R0003 shared-file request against the R11 worker tree.

    python -B docs/architecture/deliveries/R11/CHECK_REQUEST_REPLAY.py
        [--control-root DIR] [--full]

R0003 is primary-human property: 133 paths, 129 of them production consumers whose
imports retarget onto the R11 destinations, plus `NumStabilityTest.lean`, `tiers.json`,
`layout-exceptions.json` and `COMPATIBILITY.md`. The worker must not edit any of them.
This script therefore validates the request without applying it to the worker branch:
every replay happens inside a disposable directory that is deleted afterwards.

What is checked:

1. the request, patch and postimage artifacts hash to their pinned values;
2. all 133 preimage blob OIDs are exactly the C0001 blobs;
3. the worker tree modified none of the 133 paths;
4. forward replay of the patch reproduces all 133 pinned postimage SHA-256 values;
5. reverse replay restores all 133 pinned preimage SHA-256 values;
6. the 209 recorded import replacements each occur, with the old import gone and the
   new one present, and the per-path replacement counts match the review evidence.

With `--full` the disposable tree is also checked by `check_layout.py`,
`check_compatibility.py` and `check_provenance.py`, which is how the worker demonstrates
that the layout gate's worker-only failure is closed by the integrator postimage rather
than by weakening anything.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
BASE = "117aa2bb7e61f41e1531a78452f9f7f6cd5b0771"
PHASE = "docs/architecture/phases/2026-08-repository-reorganization-completion/"
CONTROL_CANDIDATES = [
    Path(r"C:\Users\qed_s\higham-worktrees\completion-integrator-c0001"),
    Path(r"C:\Users\qed_s\OneDrive\Documents\QED 94"),
]
PINNED = {
    "requests/R0003.json":
        "12580FECDF07C80FBB279BC5A1C6A8CBFF6A052B92D92895A6CD39E375424FD2",
    "requests/R0003.patch":
        "E1BFBF147D61FFE2CA08090B91DE362A2C089709221624AB2F9B36F9F4E2F4D3",
    "requests/R0003-postimages.tsv":
        "6799789E9E739095C49E409799F17D723C4EE038E2E341105BD38595F26CC5D2",
    "reviews/R11-shared-import-replacements.tsv":
        "7EE5623EB236248C96A8C65A3A4601A6819495A40B3F067BC9A6639836D38611",
}
EXPECTED_PATHS = 133
EXPECTED_CONSUMERS = 129
EXPECTED_REPLACEMENTS = 209
EXPECTED_MULTI = 43          # consumer paths carrying more than one replacement

problems: list[str] = []


def fail(m: str) -> None:
    problems.append(m)


def sha_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest().upper()


def sha_file(p: Path) -> str:
    return sha_bytes(p.read_bytes())


def git(*args: str, cwd: Path = ROOT, binary: bool = False):
    r = subprocess.run(["git", "-C", str(cwd), *args], capture_output=True,
                       text=not binary, encoding=None if binary else "utf-8")
    if r.returncode != 0:
        err = r.stderr if not binary else r.stderr.decode("utf-8", "replace")
        raise SystemExit(f"git {' '.join(args)} failed: {err.strip()}")
    return r.stdout


def find_control(explicit: str | None) -> Path:
    rec = PHASE + "requests/R0003.json"
    for c in ([Path(explicit)] if explicit else CONTROL_CANDIDATES):
        p = c / rec
        if p.is_file() and sha_file(p) == PINNED["requests/R0003.json"]:
            return c
    raise SystemExit("no control root with the pinned R0003 record; pass --control-root")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--control-root")
    ap.add_argument("--full", action="store_true",
                    help="also run the shared architecture checkers on the disposable tree")
    args = ap.parse_args()

    control = find_control(args.control_root)
    print(f"control root: {control}")
    for rel, want in PINNED.items():
        p = control / PHASE / rel
        if not p.is_file():
            fail(f"missing control artifact: {rel}")
        elif sha_file(p) != want:
            fail(f"hash mismatch: {rel}")
    print(f"pinned request artifacts verified: {len(PINNED)}")

    req = json.loads((control / PHASE / "requests/R0003.json").read_text(encoding="utf-8"))
    patch = control / PHASE / "requests/R0003.patch"
    post = list(csv.DictReader((control / PHASE / "requests/R0003-postimages.tsv")
                               .open(encoding="utf-8"), delimiter="\t"))
    repl = list(csv.DictReader((control / PHASE / "reviews/R11-shared-import-replacements.tsv")
                               .open(encoding="utf-8"), delimiter="\t"))

    paths = req["paths"]
    if len(paths) != EXPECTED_PATHS:
        fail(f"R0003 has {len(paths)} paths, expected {EXPECTED_PATHS}")
    if len(post) != EXPECTED_PATHS:
        fail(f"postimage table has {len(post)} rows, expected {EXPECTED_PATHS}")
    if len(repl) != EXPECTED_REPLACEMENTS:
        fail(f"replacement evidence has {len(repl)} rows, expected {EXPECTED_REPLACEMENTS}")
    consumers = {r["consumer_path"] for r in repl}
    if len(consumers) != EXPECTED_CONSUMERS:
        fail(f"{len(consumers)} distinct consumers, expected {EXPECTED_CONSUMERS}")
    multi = sum(1 for c in consumers
                if sum(1 for r in repl if r["consumer_path"] == c) > 1)
    if multi != EXPECTED_MULTI:
        fail(f"{multi} consumers carry >1 replacement, expected {EXPECTED_MULTI}")
    print(f"request: {len(paths)} paths, {len(consumers)} consumers, "
          f"{len(repl)} replacements ({multi} multi-replacement paths)")

    # ---- 2. preimage blob OIDs are the exact C0001 blobs
    bad_oid = 0
    for row in req["preimage_blobs"]:
        want = row["blob_oid"]
        got = git("rev-parse", f"{BASE}:{row['path']}").strip()
        if got != want:
            bad_oid += 1
            fail(f"preimage OID mismatch for {row['path']}: {got} != {want}")
    print(f"preimage blob OIDs matching C0001: {len(req['preimage_blobs']) - bad_oid}"
          f"/{len(req['preimage_blobs'])}")

    # ---- 3. the worker touched none of them
    changed = set()
    for l in git("status", "--porcelain", "--untracked-files=all").splitlines():
        if l.strip():
            changed.add(l[3:].strip().strip('"'))
    head = git("rev-parse", "HEAD").strip()
    if head != BASE:
        for l in git("diff", "--name-only", BASE, "HEAD").splitlines():
            if l.strip():
                changed.add(l.strip())
    overlap = sorted(set(paths) & changed)
    for p in overlap:
        fail(f"worker modified integrator-owned path: {p}")
    print(f"worker edits to R0003 paths: {len(overlap)} (must be 0)")

    # ---- 4/5. forward and reverse replay in a disposable directory
    tmp = Path(tempfile.mkdtemp(prefix="r11-r0003-"))
    try:
        # Materialize only the 133 request paths at their C0001 preimages. The worker's
        # own changes never touch these paths, so the C0001 blob is also the worker-tree
        # content, and a 133-file tree is enough to replay the patch exactly.
        for p in paths:
            d = tmp / p
            d.parent.mkdir(parents=True, exist_ok=True)
            d.write_bytes(git("show", f"{BASE}:{p}", binary=True))
        pre_ok = sum(1 for r in post
                     if sha_file(tmp / r["path"]) == r["preimage_sha256"])
        if pre_ok != len(post):
            fail(f"only {pre_ok}/{len(post)} preimages matched their pinned SHA-256")

        subprocess.run(["git", "init", "-q"], cwd=tmp, check=True,
                       capture_output=True)
        # This machine has core.autocrlf=true at system level, and the disposable repo
        # has none of the project's .gitattributes. Left alone, `git apply` writes CRLF
        # into the working tree: the content is right and every import replacement still
        # verifies, but all 133 postimage SHA-256 values differ and reverse replay cannot
        # restore the preimages byte-exactly. Pin LF so the replay compares real bytes.
        for key, value in (("core.autocrlf", "false"), ("core.eol", "lf"),
                           ("core.safecrlf", "false")):
            subprocess.run(["git", "config", key, value], cwd=tmp, check=True,
                           capture_output=True)
        ap_check = subprocess.run(["git", "apply", "--check", "-p1", str(patch)],
                                  cwd=tmp, capture_output=True, text=True,
                                  encoding="utf-8", errors="replace")
        if ap_check.returncode != 0:
            fail(f"patch does not apply cleanly: {ap_check.stderr.strip()[:300]}")
        else:
            subprocess.run(["git", "apply", "-p1", str(patch)], cwd=tmp, check=True,
                           capture_output=True)
            fwd_ok = sum(1 for r in post
                         if sha_file(tmp / r["path"]) == r["postimage_sha256"])
            print(f"forward replay: {fwd_ok}/{len(post)} postimages match their pinned SHA-256")
            if fwd_ok != len(post):
                fail(f"only {fwd_ok}/{len(post)} postimages matched")

            # ---- 6. exact import replacements on the postimage
            miss = stale = 0
            for r in repl:
                text = (tmp / r["consumer_path"]).read_text(encoding="utf-8")
                if f"import {r['new_import']}\n" not in text:
                    miss += 1
                    fail(f"{r['consumer_path']}: new import missing "
                         f"({r['new_import']})")
                if f"import {r['old_import']}\n" in text:
                    stale += 1
                    fail(f"{r['consumer_path']}: old import still present "
                         f"({r['old_import']})")
            print(f"import replacements verified: {len(repl) - miss - stale}/{len(repl)} "
                  f"(missing new={miss}, surviving old={stale})")

            if args.full:
                run_full(tmp, paths)

            rev = subprocess.run(["git", "apply", "-R", "-p1", str(patch)], cwd=tmp,
                                 capture_output=True, text=True, encoding="utf-8",
                                 errors="replace")
            if rev.returncode != 0:
                fail(f"reverse replay failed: {rev.stderr.strip()[:300]}")
            else:
                rev_ok = sum(1 for r in post
                             if sha_file(tmp / r["path"]) == r["preimage_sha256"])
                print(f"reverse replay: {rev_ok}/{len(post)} preimages restored exactly")
                if rev_ok != len(post):
                    fail(f"only {rev_ok}/{len(post)} preimages restored")
    finally:
        shutil.rmtree(tmp, ignore_errors=True)

    if problems:
        print(f"\nFAIL: {len(problems)} R0003 replay problem(s)")
        for p in problems[:40]:
            print("   " + p)
        return 1
    print("\nPASS: R0003 replays exactly forward and in reverse; the worker edited none of it")
    return 0


def run_full(tmp: Path, paths: list[str]) -> None:
    """Run the shared architecture checkers against worker code + R0003 postimage.

    The disposable tree is the worker tree with the 133 integrator-owned postimages
    overlaid. That is the state the integrator will actually accept, and it is the state
    in which the layout gate must be green.
    """
    full = tmp.parent / (tmp.name + "-full")
    try:
        tracked = [l for l in git("ls-files").splitlines() if l.strip()]
        untracked = [l[3:].strip().strip('"') for l in
                     git("status", "--porcelain", "--untracked-files=all").splitlines()
                     if l.startswith("??")]
        for rel in tracked + untracked:
            if rel.startswith(("benchmark-results/",)) or ".lake" in rel.split("/"):
                continue
            src = ROOT / rel
            if not src.is_file():
                continue
            dst = full / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(src, dst)
        for p in paths:                       # overlay the integrator postimages
            shutil.copyfile(tmp / p, full / p)
        # check_layout.py inspects `git ls-files -z`. Without a real index it aborts with
        # "cannot inspect tracked files" and exits 2, which is a harness artifact rather
        # than a verdict on the tree. Initialize and stage so the checker sees every file.
        for cmd in (["git", "init", "-q"],
                    ["git", "config", "core.autocrlf", "false"],
                    ["git", "config", "core.eol", "lf"],
                    ["git", "config", "user.email", "r11@local"],
                    ["git", "config", "user.name", "r11"],
                    ["git", "add", "-A"]):
            subprocess.run(cmd, cwd=full, check=True, capture_output=True)
        n = len([l for l in subprocess.run(["git", "ls-files"], cwd=full,
                                           capture_output=True, text=True,
                                           check=True).stdout.splitlines() if l.strip()])
        print(f"--full: disposable acceptance tree built at {full} ({n} tracked files)")
        for checker in ("check_layout.py", "check_compatibility.py", "check_provenance.py"):
            r = subprocess.run([sys.executable, "-B", f"tools/architecture/{checker}"],
                               cwd=full, capture_output=True, text=True,
                               encoding="utf-8", errors="replace")
            tail = [l for l in (r.stdout or "").splitlines() if l.strip()][-2:]
            print(f"   {checker}: exit {r.returncode} | " + " / ".join(tail)[:200])
            if r.returncode != 0:
                fail(f"--full: {checker} exit {r.returncode} on the acceptance tree")
                for l in ((r.stdout or "") + (r.stderr or "")).splitlines()[:12]:
                    print("        " + l[:180])
    finally:
        shutil.rmtree(full, ignore_errors=True)


if __name__ == "__main__":
    sys.exit(main())
