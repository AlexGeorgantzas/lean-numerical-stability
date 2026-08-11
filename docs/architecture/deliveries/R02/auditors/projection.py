"""Replay P0002's recorded checker arguments verbatim against the R02 candidate.

The projections README permits exactly one substitution: the candidate placeholder is
replaced by the candidate TSV path; no other recorded argument is changed. The argument
vector is therefore read from P0002.json (at rec["checker"]["arguments"], NOT a
"checker_arguments" key) rather than reconstructed.

Both the checker and the frozen graph are hash-verified before use -- running the right
arguments against the wrong artifact would prove nothing.

Control materialisation: B0012/P0002 were added by the activation commits AFTER C0007,
so they exist neither in the worker checkout (at 9eb534a06) nor in the stale control
worktree. The pinned artifacts are therefore exported read-only from origin/main into a
scratch control tree at their exact repository-relative paths, each hash-checked against
P0002's own record. The checker blob at 9eb534a06 is byte-identical to origin/main's, so
the worker's own copy is used.
"""
from __future__ import annotations

import hashlib
import json
import os
import subprocess
import sys

OUT = os.path.dirname(os.path.abspath(__file__))
WR = r"C:\Users\qed_s\higham-worktrees\completion-r02-claude"
REPO = r"C:\Users\qed_s\OneDrive\Documents\QED 94"
CTRL = os.path.join(OUT, "control")          # read-only export, not a worktree
P0002 = os.path.join(OUT, "P0002.json")
CANDIDATE = os.path.join(WR, "benchmark-results", "R02-candidate.tsv")
PLACEHOLDER = "--candidate=<candidate-format2.tsv>"


def sha_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest().upper()


def sha_file(path: str) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest().upper()


def export(rel: str, want: str) -> str:
    """Materialise one pinned file from origin/main, hash-verified."""
    blob = subprocess.run(["git", "show", f"origin/main:{rel}"], cwd=REPO,
                          capture_output=True, check=True).stdout
    got = sha_bytes(blob)
    if got != want:
        print(f"  MISMATCH {rel}\n    recorded {want}\n    actual   {got}")
        sys.exit(2)
    dst = os.path.join(CTRL, rel.replace("/", os.sep))
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    with open(dst, "wb") as fh:
        fh.write(blob)
    print(f"  OK  {rel}  {got}")
    return dst


def main() -> None:
    rec = json.load(open(P0002, encoding="utf-8"))

    print("== pinned artifacts ==")
    graph_rel = rec["projection_graph"]["path"]
    export(graph_rel, rec["projection_graph"]["sha256"])
    export(rec["selector"]["artifact"]["path"], rec["selector"]["artifact"]["sha256"])
    export(rec["combined_baseline"]["path"], rec["combined_baseline"]["sha256"])

    # The completion phase pins its own checker, check_completion_phase_projection.py,
    # which does not exist in the C0000 worker checkout -- it was added with the phase.
    # Export it from origin/main and hash-verify against the record, exactly as with the
    # other pinned artifacts, rather than assuming a worker copy.
    checker_rel = rec["checker"]["artifact"]["path"]
    export(checker_rel, rec["checker"]["artifact"]["sha256"])

    # The checker also reads files named directly in its recorded arguments (e.g.
    # --private-map). Export every path-bearing argument so the read-only control tree
    # satisfies each one at its exact repository-relative path.
    import re as _re
    for _a in rec["checker"]["arguments"]:
        m = _re.match(r"--[a-z-]+=((?:docs|tools)/[^\s]+)$", _a)
        if m:
            _rel = m.group(1)
            _dst = os.path.join(CTRL, _rel.replace("/", os.sep))
            if not os.path.exists(_dst):
                _blob = subprocess.run(["git", "show", f"origin/main:{_rel}"], cwd=REPO,
                                       capture_output=True, check=True).stdout
                os.makedirs(os.path.dirname(_dst), exist_ok=True)
                open(_dst, "wb").write(_blob)
                print(f"  exported {_rel}  {sha_bytes(_blob)}")

    if not os.path.exists(CANDIDATE):
        print(f"\ncandidate not found: {CANDIDATE}")
        sys.exit(3)
    print(f"\ncandidate  {CANDIDATE}")
    print(f"  sha256   {sha_file(CANDIDATE)}")
    print(f"  bytes    {os.path.getsize(CANDIDATE):,}")

    args = list(rec["checker"]["arguments"])
    subbed = 0
    for i, a in enumerate(args):
        if a == PLACEHOLDER:
            args[i] = "--candidate=" + CANDIDATE
            subbed += 1
    if subbed != 1:
        print(f"\nexpected exactly one candidate placeholder, found {subbed}")
        sys.exit(4)

    print(f"\nrecorded arguments: {len(args)} (1 candidate placeholder substituted, "
          f"{len(args) - 1} verbatim)")
    cmd = [sys.executable, "-B", checker_rel] + args
    print(f"running: python {checker_rel} <{len(args)} recorded args>")
    print(f"  cwd: {CTRL}  (read-only export; -B suppresses __pycache__)\n")
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    proc = subprocess.run(cmd, cwd=CTRL, capture_output=True, text=True,
                          encoding="utf-8", env=env)
    sys.stdout.write(proc.stdout)
    if proc.stderr.strip():
        sys.stdout.write("\n--- stderr ---\n" + proc.stderr)
    print(f"\nexit {proc.returncode}")
    sys.exit(proc.returncode)


if __name__ == "__main__":
    main()
