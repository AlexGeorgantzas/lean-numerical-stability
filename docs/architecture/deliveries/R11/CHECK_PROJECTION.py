#!/usr/bin/env python3
"""Replay the frozen P0003 projection against an R11 candidate graph.

    python -B docs/architecture/deliveries/R11/CHECK_PROJECTION.py \
        benchmark-results/R11-candidate.tsv [--control-root DIR]

This wraps `tools/architecture/check_completion_phase_projection.py` with the exact
argument vector P0003 records: 65 `--allow-module` values, three `--allow-prefix`
values, the hash-pinned projection, and the hash-pinned 17-row private normalization
map. The vector is reproduced here rather than rebuilt from the record so that a silent
edit to either side shows up as a mismatch; the record's own hash is verified first, and
the reproduced vector is then diffed against it.

The private map matters. R11 relocates 16 private declarations, and Lean encodes the
defining module in a private name, so relocation renames them. The preimage replay
recorded in `reviews/R11-R12-projection-replay.md` deliberately omitted the map, because
at C0001 the private names are still the projection names. At delivery the map must be
supplied, or every incident edge of every relocated private reads as missing.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[4]
PHASE = "docs/architecture/phases/2026-08-repository-reorganization-completion/"
CONTROL_CANDIDATES = [
    Path(r"C:\Users\qed_s\higham-worktrees\completion-integrator-c0001"),
    Path(r"C:\Users\qed_s\OneDrive\Documents\QED 94"),
]
CHECKER = "tools/architecture/check_completion_phase_projection.py"
CHECKER_SHA = "0F32935ED1EFDD2BD4D6A4C346F3E8300C86DB1D4A3551A17165479226109220"
P0003_JSON_SHA = "750A4A89F0CF0C9BE9481C87B19E6ECBE8E279CF9480BF4C57F5895BCD9EFD55"
PROJECTION_SHA = "31EC591D949DB6041078C036F0CFF74A0A3EE229B35E351DDF999D15F494D60E"
PRIVATE_MAP_SHA = "12E4D4F517D3678DABA4A11F57D36E22EE4428BC3598D3CA0FC7E41A9323E70E"

EXPECTED_COUNTS = {
    "declarations": 1477,
    "signature_edges": 15172,
    "body_edges": 18056,
    "union_edges": 19873,
}
EXPECTED_RELOCATED = 412
EXPECTED_RETAINED = 1065
# The checker's own `private_normalizations` count is reported but not asserted: the
# tracked map has 17 rows (16 module-prefix rewrites plus the Chapter19.Core identity),
# and whether the checker counts rewrites or all total rows is its business, not a
# number this wave gets to choose. The map's identity and totality are already pinned by
# --private-map-sha256, which the checker enforces itself.

ALLOW_MODULES = [
    "NumStability.Algorithms.LinearSystems.QR.HouseholderApplySupport",
    "NumStability.Algorithms.LinearSystems.QR.HouseholderQRSupport",
    "NumStability.Algorithms.LinearSystems.QR.HouseholderSpecSupport",
    "NumStability.Algorithms.QR.GivensMatrixStep",
    "NumStability.Algorithms.QR.GivensQR",
    "NumStability.Algorithms.QR.GivensSpec",
    "NumStability.Algorithms.QR.GramSchmidt",
    "NumStability.Algorithms.QR.GramSchmidtPolar",
    "NumStability.Algorithms.QR.Higham19",
    "NumStability.Algorithms.QR.Higham19Alg11CGSRounded",
    "NumStability.Algorithms.QR.Higham19Alg12MGSClosure",
    "NumStability.Algorithms.QR.Higham19Alg12MGSNonbreakdown",
    "NumStability.Algorithms.QR.Higham19Alg12MGSPaddedClosure",
    "NumStability.Algorithms.QR.Higham19Alg12MGSRepair",
    "NumStability.Algorithms.QR.Higham19Alg12MGSRounded",
    "NumStability.Algorithms.QR.Higham19Alg12MGSSourceRate",
    "NumStability.Algorithms.QR.Higham19FormedQ",
    "NumStability.Algorithms.QR.Higham19Labels",
    "NumStability.Algorithms.QR.Higham19Lemma3ActualSequence",
    "NumStability.Algorithms.QR.Higham19Lemma7Gamma4",
    "NumStability.Algorithms.QR.Higham19Lemma9DisjointSweep",
    "NumStability.Algorithms.QR.Higham19PolarNearest",
    "NumStability.Algorithms.QR.Higham19Problem19_10",
    "NumStability.Algorithms.QR.Higham19Problem19_9",
    "NumStability.Algorithms.QR.Higham19Problem6ActualStep",
    "NumStability.Algorithms.QR.Higham19Sensitivity",
    "NumStability.Algorithms.QR.Higham19SensitivityClosure",
    "NumStability.Algorithms.QR.Higham19StoredLoop",
    "NumStability.Algorithms.QR.Higham19StoredLoopAllPivots",
    "NumStability.Algorithms.QR.Higham19StoredLoopStrongModel",
    "NumStability.Algorithms.QR.Higham19SunBischof",
    "NumStability.Algorithms.QR.Higham19Theorem10ActualMatrix",
    "NumStability.Algorithms.QR.Higham19Theorem5Nonbreakdown",
    "NumStability.Algorithms.QR.Higham19Theorem5SourceClosure",
    "NumStability.Algorithms.QR.Higham19Theorem6ActualSource",
    "NumStability.Algorithms.QR.Higham19Thm6ColPivot",
    "NumStability.Algorithms.QR.Higham19Thm6ColPivotFull",
    "NumStability.Algorithms.QR.Higham19Thm6CoxHigham",
    "NumStability.Algorithms.QR.Higham19Thm6CoxHighamAssembly",
    "NumStability.Algorithms.QR.Higham19Thm6CoxHighamConcrete",
    "NumStability.Algorithms.QR.Higham19Thm6CoxHighamFull",
    "NumStability.Algorithms.QR.Higham19Thm6Elementwise",
    "NumStability.Algorithms.QR.Higham19Thm6ElementwiseEntry",
    "NumStability.Algorithms.QR.Higham19Thm6ElementwisePackaged",
    "NumStability.Algorithms.QR.Higham19Thm6Final",
    "NumStability.Algorithms.QR.Higham19Thm6Pivoted",
    "NumStability.Algorithms.QR.Higham19Thm6RowSpecific",
    "NumStability.Algorithms.QR.Higham19Thm6StrongModel",
    "NumStability.Algorithms.QR.Higham19TurnbullAitken",
    "NumStability.Algorithms.QR.Higham19WYApplicationClosure",
    "NumStability.Algorithms.QR.HouseholderApply",
    "NumStability.Algorithms.QR.HouseholderApplySupport",
    "NumStability.Algorithms.QR.HouseholderConstruction2",
    "NumStability.Algorithms.QR.HouseholderMatrixStep",
    "NumStability.Algorithms.QR.HouseholderOneStep",
    "NumStability.Algorithms.QR.HouseholderQApply",
    "NumStability.Algorithms.QR.HouseholderQR",
    "NumStability.Algorithms.QR.HouseholderQRSupport",
    "NumStability.Algorithms.QR.HouseholderReflector",
    "NumStability.Algorithms.QR.HouseholderSpec",
    "NumStability.Algorithms.QR.HouseholderSpecSupport",
    "NumStability.Algorithms.QR.QRSolve",
    "NumStability.Source.Higham.Chapter19.Core",
    "NumStability.Source.Higham.Chapter19.Sensitivity",
    "NumStability.Source.Higham.Chapter19.StoredLoop",
]
ALLOW_PREFIXES = [
    "NumStability.Algorithms.LinearSystems.QR.Householder.",
    "NumStability.Source.Higham.Chapter19.Sensitivity.Bounds.",
    "NumStability.Source.Higham.Chapter19.StoredLoop.Perturbation.",
]


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for chunk in iter(lambda: fh.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest().upper()


def find_control(explicit: str | None) -> Path:
    rec = PHASE + "projections/P0003.json"
    for c in ([Path(explicit)] if explicit else CONTROL_CANDIDATES):
        p = c / rec
        if p.is_file() and sha(p) == P0003_JSON_SHA:
            return c
    raise SystemExit("no control root with the pinned P0003 record; pass --control-root")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("candidate")
    ap.add_argument("--control-root")
    args = ap.parse_args()

    control = find_control(args.control_root)
    print(f"control root: {control}")

    checker = ROOT / CHECKER
    if sha(checker) != CHECKER_SHA:
        print(f"FAIL: {CHECKER} does not match the P0003-pinned hash")
        return 1
    proj = control / (PHASE + "projections/P0003.tsv.gz")
    pmap = control / (PHASE + "branches/B0003-private-normalization.tsv")
    for p, want in ((proj, PROJECTION_SHA), (pmap, PRIVATE_MAP_SHA)):
        if sha(p) != want:
            print(f"FAIL: {p.name} hash mismatch")
            return 1
    print(f"checker, projection and private map verified at their pinned hashes")

    record = json.loads((control / (PHASE + "projections/P0003.json")).read_text(encoding="utf-8"))
    if record["expected_counts"] != EXPECTED_COUNTS:
        print(f"FAIL: P0003 expected_counts {record['expected_counts']} != {EXPECTED_COUNTS}")
        return 1

    # The reproduced vector must agree with the record's own argument list.
    recorded = {a for a in record["checker"]["arguments"]
                if a.startswith(("--allow-module=", "--allow-prefix="))}
    mine = ({f"--allow-module={m}" for m in ALLOW_MODULES}
            | {f"--allow-prefix={p}" for p in ALLOW_PREFIXES})
    if recorded != mine:
        print("FAIL: reproduced allow-list differs from the P0003 record")
        for a in sorted(recorded ^ mine):
            print("   " + a)
        return 1
    print(f"allow-list matches the record: {len(ALLOW_MODULES)} modules, "
          f"{len(ALLOW_PREFIXES)} prefixes")

    candidate = Path(args.candidate)
    if not candidate.is_absolute():
        candidate = ROOT / candidate
    if not candidate.is_file():
        print(f"FAIL: candidate not found: {candidate}")
        return 1
    print(f"candidate: {candidate} ({candidate.stat().st_size} bytes, sha256 {sha(candidate)})")

    cmd = [sys.executable, "-B", str(checker),
           "--projection", str(proj), "--projection-sha256", PROJECTION_SHA,
           "--candidate", str(candidate),
           "--private-map", str(pmap), "--private-map-sha256", PRIVATE_MAP_SHA]
    cmd += [f"--allow-module={m}" for m in ALLOW_MODULES]
    cmd += [f"--allow-prefix={p}" for p in ALLOW_PREFIXES]
    r = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True,
                       encoding="utf-8", errors="replace")
    out = (r.stdout or "") + (r.stderr or "")
    print(out.rstrip())
    if r.returncode != 0:
        print(f"\nFAIL: projection replay exit {r.returncode}")
        return 1

    # Parse the checker's own summary and require the frozen numbers.
    got: dict[str, int] = {}
    for line in out.splitlines():
        if ":" in line:
            k, _, v = line.partition(":")
            v = v.strip()
            if v.isdigit():
                got[k.strip()] = int(v)
    problems = []
    for k, want in (("selected_declarations", EXPECTED_COUNTS["declarations"]),
                    ("signature_edges", EXPECTED_COUNTS["signature_edges"]),
                    ("body_edges", EXPECTED_COUNTS["body_edges"]),
                    ("relocated_declarations", EXPECTED_RELOCATED)):
        if k in got and got[k] != want:
            problems.append(f"{k}={got[k]}, expected {want}")
    if "selected_declarations" in got and "relocated_declarations" in got:
        retained = got["selected_declarations"] - got["relocated_declarations"]
        if retained != EXPECTED_RETAINED:
            problems.append(f"retained={retained}, expected {EXPECTED_RETAINED}")
        else:
            print(f"retained declarations: {retained}")
    if problems:
        print("\nFAIL: replay summary disagrees with the frozen counts")
        for p in problems:
            print("   " + p)
        return 1
    print("\nPASS: P0003 replay preserves the frozen graph identity")
    return 0


if __name__ == "__main__":
    sys.exit(main())
