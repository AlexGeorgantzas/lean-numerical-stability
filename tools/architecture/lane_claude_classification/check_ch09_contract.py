#!/usr/bin/env python3
"""Chapter 9 format-2 migration contract: reviewed configuration and gate.

Chapter 9's giant historical owner is routed along the seams the file itself
declares -- its ``/-! ## ... -/`` section blocks -- and the ten satellite
closure modules are routed whole-file. Every destination owns exactly one
contiguous region of exactly one historical module, which is what makes the
destination dependency graph acyclic by construction.

Modes
-----

``--self-test``
    negative tests over the contract primitives (route coverage, cycle
    detection, private-name normalization, typed-edge digests).
``--mode pre``
    the pre-migration gate: exact route coverage, ownership completeness and
    uniqueness against the packaged format-2 baseline, kind/visibility
    preservation, one reviewed rewrite per private declaration, destination DAG
    acyclicity per edge kind, import allowlists, and a frozen acceptance record.
``--mode stage`` / ``--mode post``
    documented interfaces that require a freshly generated candidate format-2
    stream. They deliberately refuse to run here: this lane is preparation
    only and must not fabricate post-migration evidence.
``--emit``
    regenerate the tracked artifacts from the frozen sources and baseline.

Chapter 9 implementation is BLOCKED_ON_BLOCKLU_INTEGRATION.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import chapter_driver as driver


ROOT = Path(__file__).resolve().parents[3]
CH09_DIR = ROOT / "docs/architecture/lane-proposals/claude-classification/ch09"
DEFAULT_BASELINE = ROOT.parent.parent / "baseline/parallel-base-declarations-v2.zip"

CANDIDATES = {
    "NumStability.Algorithms.HighamChapter9":
        "NumStability/Algorithms/HighamChapter9.lean",
    "NumStability.Algorithms.HighamChapter9CompletePivotSharpClosure":
        "NumStability/Algorithms/HighamChapter9CompletePivotSharpClosure.lean",
    "NumStability.Algorithms.HighamChapter9ComplexClosure":
        "NumStability/Algorithms/HighamChapter9ComplexClosure.lean",
    "NumStability.Algorithms.HighamChapter9ComputedCorrection":
        "NumStability/Algorithms/HighamChapter9ComputedCorrection.lean",
    "NumStability.Algorithms.HighamChapter9DoolittleClosure":
        "NumStability/Algorithms/HighamChapter9DoolittleClosure.lean",
    "NumStability.Algorithms.HighamChapter9Theorem914Actual":
        "NumStability/Algorithms/HighamChapter9Theorem914Actual.lean",
    "NumStability.Algorithms.HighamChapter9Theorem914DiagDominant":
        "NumStability/Algorithms/HighamChapter9Theorem914DiagDominant.lean",
    "NumStability.Algorithms.HighamChapter9Theorem914Primitive":
        "NumStability/Algorithms/HighamChapter9Theorem914Primitive.lean",
    "NumStability.Algorithms.HighamChapter9Theorem97Classification":
        "NumStability/Algorithms/HighamChapter9Theorem97Classification.lean",
    "NumStability.Algorithms.HighamChapter9Theorem99Closure":
        "NumStability/Algorithms/HighamChapter9Theorem99Closure.lean",
    "NumStability.Algorithms.HighamChapter9Theorem99ComplexClosure":
        "NumStability/Algorithms/HighamChapter9Theorem99ComplexClosure.lean",
}

# Reviewed seam -> canonical leaf. The order matters: the first matching
# pattern wins, so the narrower Problem 9.14 and Theorem 9.11 readings precede
# their general forms.
SECTION_SEED = (
    (r"Problem 9\.14, first method", "Problem14.FirstMethod"),
    (r"Problem 9\.14", "Problem14.RowReversal"),
    (r"Problem 9\.11", "Problem11"),
    (r"Problem 9\.13", "Problem13"),
    (r"Appendix A, Problem 9\.2\b", "Problem02"),
    (r"Appendix A, Problem 9\.5\b", "Problem05"),
    (r"Appendix A, Problem 9\.6\b", "Problem06"),
    (r"Appendix A, Problem 9\.7\b", "Problem07"),
    (r"Appendix A, Problem 9\.8\b", "Problem08"),
    (r"Theorem 9\.11, `p = 1`", "Theorem11.BohteBandOne"),
    (r"Theorem 9\.11 \(Bohte\)", "Theorem11.BohteGeneral"),
    (r"Equation \(9\.12\)", "Equation12"),
    (r"Equation \(9\.13\)", "Equation13"),
    (r"Foundation for equation \(9\.14\)", "Equation14"),
    (r"Section 9\.4 application, Hadamard", "Equation14"),
    (r"Equation \(9\.16\)", "Equation16"),
    (r"§9\.1 ", "Section01"),
    (r"§9\.2 ", "Section02"),
    (r"§9\.3 ", "Section03"),
    (r"§9\.4 ", "Section04"),
    (r"§9\.5 ", "Section05"),
    (r"§9\.6 Special Tridiagonal Classes", "Section06.SpecialClasses"),
    (r"§9\.6 Tridiagonal Matrices", "Section06.Tridiagonal"),
    (r"§9\.8 ", "Section08"),
    (r"§9\.10 ", "Section10"),
    (r"§9\.11 ", "Section11"),
)

SATELLITES = {
    "NumStability.Algorithms.HighamChapter9CompletePivotSharpClosure":
        "Theorem14.CompletePivotSharp",
    "NumStability.Algorithms.HighamChapter9ComplexClosure": "ComplexDomain",
    "NumStability.Algorithms.HighamChapter9ComputedCorrection":
        "Theorem05.ComputedCorrection",
    "NumStability.Algorithms.HighamChapter9DoolittleClosure": "Theorem03.DoolittleClosure",
    "NumStability.Algorithms.HighamChapter9Theorem914Actual": "Theorem14.Actual",
    "NumStability.Algorithms.HighamChapter9Theorem914DiagDominant":
        "Theorem14.DiagonallyDominant",
    "NumStability.Algorithms.HighamChapter9Theorem914Primitive": "Theorem14.Primitive",
    "NumStability.Algorithms.HighamChapter9Theorem97Classification":
        "Theorem07.Classification",
    "NumStability.Algorithms.HighamChapter9Theorem99Closure": "Theorem09.Closure",
    "NumStability.Algorithms.HighamChapter9Theorem99ComplexClosure":
        "Theorem09.ComplexClosure",
}

SPEC = driver.ChapterSpec(
    chapter="09",
    destination_prefix="NumStability.Source.Higham.Chapter09",
    candidates=CANDIDATES,
    sectioned_module="NumStability.Algorithms.HighamChapter9",
    section_seed=SECTION_SEED,
    satellite_destinations=SATELLITES,
    implementation_status="BLOCKED_ON_BLOCKLU_INTEGRATION",
    blocking_reason=(
        "HighamChapter9.lean imports NumStability.Algorithms.LU.BlockLU and "
        "NumStability.Algorithms.LU.GrowthFactor, both owned by the integrator's "
        "BlockLU/Chapter 13 wave. The Chapter 9 direct-import contract is provisional "
        "until the integrator refreshes HighamChapter9.lean against the accepted "
        "BlockLU checkpoint, and Chapter 9 may not be released before BlockLU/Chapter 13 "
        "is merged and globally verified."
    ),
    required_gates=(
        "python tools/architecture/lane_claude_classification/check_ch09_contract.py --self-test",
        "python tools/architecture/lane_claude_classification/check_ch09_contract.py --mode pre"
        " --baseline-zip <packet>/baseline/parallel-base-declarations-v2.zip",
        "lake build <the 11 historical Chapter 9 candidate modules>",
        "lake env lean NumStabilityTest/Worker/ClassificationAudit/Chapter09Historical.lean",
        "python tools/architecture/check_layout.py",
        "python tools/architecture/check_compatibility.py",
        "python tools/architecture/check_provenance.py",
        "lake build NumStability NumStabilityTest",
        "lake test",
    ),
    notes=(
        "Preparation only: no canonical production module is created, no declaration is "
        "moved, no proof is rewritten, no import is edited, and no wrapper is added.",
        "Each destination owns one contiguous region of one historical module, so the "
        "destination dependency graph inherits Lean's forward-declaration discipline.",
        "Section11 (Sensitivity) and Problem06 are the two largest destinations and are "
        "the natural candidates for a second-level split in a later wave; this contract "
        "routes at the granularity of the seams the file itself declares.",
    ),
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("pre", "stage", "post"))
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--emit", action="store_true")
    parser.add_argument("--baseline-zip", type=Path, default=DEFAULT_BASELINE)
    parser.add_argument("--directory", type=Path, default=CH09_DIR)
    args = parser.parse_args()

    if args.self_test:
        problems = driver.self_test()
        if problems:
            for problem in problems:
                print(f"ERROR: self-test: {problem}", file=sys.stderr)
            return 1
        print("Chapter 9 contract self-test passed: every rejection case is detected.")
        return 0

    if args.mode in {"stage", "post"}:
        print(
            f"ERROR: --mode {args.mode} requires a freshly generated candidate format-2 "
            "stream for the migrated tree. This lane is preparation only and must not "
            "fabricate post-migration evidence; the integrator runs stage/post after the "
            "BlockLU checkpoint lands and the Chapter 9 wave is implemented.",
            file=sys.stderr,
        )
        return 2

    if not args.baseline_zip.is_file():
        print(f"ERROR: missing baseline stream {args.baseline_zip}", file=sys.stderr)
        return 2

    if args.emit:
        failures = driver.emit(ROOT, SPEC, args.directory, args.baseline_zip)
        if failures:
            for failure in failures:
                print(f"ERROR: {failure}", file=sys.stderr)
            return 1
        print(f"Emitted the Chapter 9 contract into {args.directory.relative_to(ROOT)}")
        return 0

    if args.mode != "pre":
        print("ERROR: choose --self-test, --emit, or --mode pre", file=sys.stderr)
        return 2

    failures = driver.validate_pre(ROOT, SPEC, args.directory, args.baseline_zip)
    if failures:
        for failure in failures:
            print(f"ERROR: {failure}", file=sys.stderr)
        return 1
    print(
        "Chapter 9 pre-migration contract verified: routes complete and non-overlapping, "
        "ownership exact against the frozen format-2 baseline, private rewrites complete, "
        "destination graphs acyclic, import allowlists exact. Implementation remains "
        "BLOCKED_ON_BLOCKLU_INTEGRATION."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
