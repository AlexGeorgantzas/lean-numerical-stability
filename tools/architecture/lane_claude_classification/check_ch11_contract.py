#!/usr/bin/env python3
"""Chapter 11 format-2 migration contract: reviewed configuration and gate.

The candidate family is exactly the 66 rows marked ``candidate_production`` in
the packet's ``CH11_PREP_PATHS.tsv``: ``HighamChapter11.lean`` plus the 65
Cholesky files whose basenames contain ``Ch11`` or ``Higham11``.  It is *not*
all of ``NumStability/Algorithms/Cholesky/``.

Three Chapter 11 paths are deliberately excluded and stay read-only context:

* ``Cholesky/BunchTridiagonalCapstoneCh11Closure.lean`` -- an already-migrated
  compatibility wrapper that must not be re-owned;
* ``Source/Higham/Chapter11/Theorem07.lean`` -- the existing canonical
  Theorem 11.7 slice, which no destination here may collide with;
* ``Higham/Chapter11/Theorem11_7Capstone.lean`` -- its compatibility facade.

``HighamChapter11.lean`` is routed along the seams the file itself declares (its
``/-! ## ... -/`` section blocks, which follow §11.1--§11.3 and the problem
surface) and the 65 satellites are routed whole-file to the numbered result each
one closes.  Three ``deriving``-generated instances of
``higham11_4_BunchKaufmanActiveBranch`` have no source declaration anchor and
are therefore covered by explicit ``exact`` routes.

Modes match ``check_ch09_contract.py``: ``--self-test``, ``--mode pre``,
``--emit``, and documented ``stage``/``post`` interfaces that refuse to run
without a freshly generated candidate stream.

Chapter 11 implementation is BLOCKED_ON_CH09_INTEGRATION.  Chapter 11 and
Chapter 9 must never be proposed as parallel implementation waves.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))

import chapter_driver as driver


ROOT = Path(__file__).resolve().parents[3]
CH11_DIR = ROOT / "docs/architecture/lane-proposals/claude-classification/ch11"
DEFAULT_BASELINE = ROOT.parent.parent / "baseline/parallel-base-declarations-v2.zip"

CANDIDATES = {
    "NumStability.Algorithms.Cholesky.Aasen118ReducedCh11Closure":
        "NumStability/Algorithms/Cholesky/Aasen118ReducedCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.AasenAdjacentPivotOperationalMiddleCh11":
        "NumStability/Algorithms/Cholesky/AasenAdjacentPivotOperationalMiddleCh11.lean",
    "NumStability.Algorithms.Cholesky.AasenAdjacentPivotResidualDomainCh11Discrepancy":
        "NumStability/Algorithms/Cholesky/AasenAdjacentPivotResidualDomainCh11Discrepancy.lean",
    "NumStability.Algorithms.Cholesky.AasenAdjacentPivotSourceResidualCh11Closure":
        "NumStability/Algorithms/Cholesky/AasenAdjacentPivotSourceResidualCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.AasenAdjacentPivotTridiagExecutorCh11Closure":
        "NumStability/Algorithms/Cholesky/AasenAdjacentPivotTridiagExecutorCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.AasenAdjacentPivotTridiagForwardCounterexampleCh11":
        "NumStability/Algorithms/Cholesky/AasenAdjacentPivotTridiagForwardCounterexampleCh11.lean",
    "NumStability.Algorithms.Cholesky.AasenCoupledFpCh11Closure":
        "NumStability/Algorithms/Cholesky/AasenCoupledFpCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.AasenDirect118Ch11Closure":
        "NumStability/Algorithms/Cholesky/AasenDirect118Ch11Closure.lean",
    "NumStability.Algorithms.Cholesky.AasenDirectTridiagGEPPSolveCh11Closure":
        "NumStability/Algorithms/Cholesky/AasenDirectTridiagGEPPSolveCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.AasenFactorNormCh11Closure":
        "NumStability/Algorithms/Cholesky/AasenFactorNormCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.AasenFactorResidualCh11Closure":
        "NumStability/Algorithms/Cholesky/AasenFactorResidualCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.AasenGrowthCh11Closure":
        "NumStability/Algorithms/Cholesky/AasenGrowthCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.AasenMiddleGEPPCh11Counterexample":
        "NumStability/Algorithms/Cholesky/AasenMiddleGEPPCh11Counterexample.lean",
    "NumStability.Algorithms.Cholesky.AasenOriginalCoordinateCorrectionCh11":
        "NumStability/Algorithms/Cholesky/AasenOriginalCoordinateCorrectionCh11.lean",
    "NumStability.Algorithms.Cholesky.AasenPermutationSourceCorrectionCh11":
        "NumStability/Algorithms/Cholesky/AasenPermutationSourceCorrectionCh11.lean",
    "NumStability.Algorithms.Cholesky.AasenPrintedCoefficientAlgebraCh11Closure":
        "NumStability/Algorithms/Cholesky/AasenPrintedCoefficientAlgebraCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.AasenSourceSharpFactorResidualCh11Closure":
        "NumStability/Algorithms/Cholesky/AasenSourceSharpFactorResidualCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.AasenTheorem118ScalarEdgeCh11Discrepancy":
        "NumStability/Algorithms/Cholesky/AasenTheorem118ScalarEdgeCh11Discrepancy.lean",
    "NumStability.Algorithms.Cholesky.AasenTridiagGEPPCh11Closure":
        "NumStability/Algorithms/Cholesky/AasenTridiagGEPPCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.AasenUnitOuterSolveCh11Closure":
        "NumStability/Algorithms/Cholesky/AasenUnitOuterSolveCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.BlockLDLTAllOneByOnePrintedCh11Closure":
        "NumStability/Algorithms/Cholesky/BlockLDLTAllOneByOnePrintedCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.BlockLDLTBunchTridiagonalCh11Closure":
        "NumStability/Algorithms/Cholesky/BlockLDLTBunchTridiagonalCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.BlockLDLTMixedPivotCh11Closure":
        "NumStability/Algorithms/Cholesky/BlockLDLTMixedPivotCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.BlockLDLTSolveBackwardCh11Closure":
        "NumStability/Algorithms/Cholesky/BlockLDLTSolveBackwardCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.BunchKaufmanSolveCh11Closure":
        "NumStability/Algorithms/Cholesky/BunchKaufmanSolveCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalActualSolveCh11Closure":
        "NumStability/Algorithms/Cholesky/BunchTridiagonalActualSolveCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalFactorBoundCh11Closure":
        "NumStability/Algorithms/Cholesky/BunchTridiagonalFactorBoundCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalGrowthCh11Closure":
        "NumStability/Algorithms/Cholesky/BunchTridiagonalGrowthCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalGrowthInvariantCh11Closure":
        "NumStability/Algorithms/Cholesky/BunchTridiagonalGrowthInvariantCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalHFactorCh11Closure":
        "NumStability/Algorithms/Cholesky/BunchTridiagonalHFactorCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalSparseFactorCh11Closure":
        "NumStability/Algorithms/Cholesky/BunchTridiagonalSparseFactorCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalSparseSolveCh11Closure":
        "NumStability/Algorithms/Cholesky/BunchTridiagonalSparseSolveCh11Closure.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchActualSharpGrowthClosure":
        "NumStability/Algorithms/Cholesky/Higham11BunchActualSharpGrowthClosure.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchExactTrace":
        "NumStability/Algorithms/Cholesky/Higham11BunchExactTrace.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanActualSelector":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanActualSelector.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExactGrowth":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanExactGrowth.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExactGrowthArithmetic":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanExactGrowthArithmetic.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExactTrace":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanExactTrace.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExplicitInverseSolve":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanExplicitInverseSolve.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExplicitInverseTerminalClosedForm":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanExplicitInverseTerminalClosedForm.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedAccumulated":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanRoundedAccumulated.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedBridge":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanRoundedBridge.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedClosure":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanRoundedClosure.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedExecution":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanRoundedExecution.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedFactors":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanRoundedFactors.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGlobal":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanRoundedGlobal.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGrowth":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanRoundedGrowth.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGrowthSolve":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanRoundedGrowthSolve.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedMiddleSolve":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanRoundedMiddleSolve.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedSolve":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanRoundedSolve.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedTerminal":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanRoundedTerminal.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedTerminalClosedForm":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanRoundedTerminalClosedForm.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanSourceCorrection":
        "NumStability/Algorithms/Cholesky/Higham11BunchKaufmanSourceCorrection.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchSharpGrowthBridge":
        "NumStability/Algorithms/Cholesky/Higham11BunchSharpGrowthBridge.lean",
    "NumStability.Algorithms.Cholesky.Higham11BunchTraceHadamard":
        "NumStability/Algorithms/Cholesky/Higham11BunchTraceHadamard.lean",
    "NumStability.Algorithms.Cholesky.Higham11Chapter9ActualExecutorBridge":
        "NumStability/Algorithms/Cholesky/Higham11Chapter9ActualExecutorBridge.lean",
    "NumStability.Algorithms.Cholesky.Higham11Chapter9BridgeClosure":
        "NumStability/Algorithms/Cholesky/Higham11Chapter9BridgeClosure.lean",
    "NumStability.Algorithms.Cholesky.Higham11RookExactTrace":
        "NumStability/Algorithms/Cholesky/Higham11RookExactTrace.lean",
    "NumStability.Algorithms.Cholesky.Higham11RookExecutorAdapter":
        "NumStability/Algorithms/Cholesky/Higham11RookExecutorAdapter.lean",
    "NumStability.Algorithms.Cholesky.Higham11RookRoundedGap":
        "NumStability/Algorithms/Cholesky/Higham11RookRoundedGap.lean",
    "NumStability.Algorithms.Cholesky.Higham11RookSourceClosure":
        "NumStability/Algorithms/Cholesky/Higham11RookSourceClosure.lean",
    "NumStability.Algorithms.Cholesky.Higham11SkewActualSelector":
        "NumStability/Algorithms/Cholesky/Higham11SkewActualSelector.lean",
    "NumStability.Algorithms.Cholesky.Higham11SkewExactTrace":
        "NumStability/Algorithms/Cholesky/Higham11SkewExactTrace.lean",
    "NumStability.Algorithms.Cholesky.Higham11SkewSourceCorrection":
        "NumStability/Algorithms/Cholesky/Higham11SkewSourceCorrection.lean",
    "NumStability.Algorithms.Cholesky.TwoByTwoSchurStepCh11Closure":
        "NumStability/Algorithms/Cholesky/TwoByTwoSchurStepCh11Closure.lean",
    "NumStability.Algorithms.HighamChapter11":
        "NumStability/Algorithms/HighamChapter11.lean",
}

SATELLITES = {
    "NumStability.Algorithms.Cholesky.Aasen118ReducedCh11Closure":
        "Section02.Aasen.ReducedResidual",
    "NumStability.Algorithms.Cholesky.AasenAdjacentPivotOperationalMiddleCh11":
        "Section02.Aasen.AdjacentPivot.OperationalMiddle",
    "NumStability.Algorithms.Cholesky.AasenAdjacentPivotResidualDomainCh11Discrepancy":
        "Section02.Aasen.AdjacentPivot.ResidualDomain",
    "NumStability.Algorithms.Cholesky.AasenAdjacentPivotSourceResidualCh11Closure":
        "Section02.Aasen.AdjacentPivot.SourceResidual",
    "NumStability.Algorithms.Cholesky.AasenAdjacentPivotTridiagExecutorCh11Closure":
        "Section02.Aasen.AdjacentPivot.TridiagonalExecutor",
    "NumStability.Algorithms.Cholesky.AasenAdjacentPivotTridiagForwardCounterexampleCh11":
        "Section02.Aasen.AdjacentPivot.ForwardCounterexample",
    "NumStability.Algorithms.Cholesky.AasenCoupledFpCh11Closure":
        "Section02.Aasen.CoupledExecutor",
    "NumStability.Algorithms.Cholesky.AasenDirect118Ch11Closure":
        "Section02.Aasen.DirectBackwardError",
    "NumStability.Algorithms.Cholesky.AasenDirectTridiagGEPPSolveCh11Closure":
        "Section02.Aasen.DirectTridiagonalSolve",
    "NumStability.Algorithms.Cholesky.AasenFactorNormCh11Closure":
        "Section02.Aasen.FactorNorm",
    "NumStability.Algorithms.Cholesky.AasenFactorResidualCh11Closure":
        "Section02.Aasen.FactorResidual",
    "NumStability.Algorithms.Cholesky.AasenGrowthCh11Closure":
        "Section02.Aasen.Growth",
    "NumStability.Algorithms.Cholesky.AasenMiddleGEPPCh11Counterexample":
        "Section02.Aasen.MiddleCounterexample",
    "NumStability.Algorithms.Cholesky.AasenOriginalCoordinateCorrectionCh11":
        "Section02.Aasen.OriginalCoordinate",
    "NumStability.Algorithms.Cholesky.AasenPermutationSourceCorrectionCh11":
        "Section02.Aasen.PermutationCorrection",
    "NumStability.Algorithms.Cholesky.AasenPrintedCoefficientAlgebraCh11Closure":
        "Section02.Aasen.PrintedCoefficients",
    "NumStability.Algorithms.Cholesky.AasenSourceSharpFactorResidualCh11Closure":
        "Section02.Aasen.SharpFactorResidual",
    "NumStability.Algorithms.Cholesky.AasenTheorem118ScalarEdgeCh11Discrepancy":
        "Section02.Aasen.ScalarEdgeDiscrepancy",
    "NumStability.Algorithms.Cholesky.AasenTridiagGEPPCh11Closure":
        "Section02.Aasen.TridiagonalGEPP",
    "NumStability.Algorithms.Cholesky.AasenUnitOuterSolveCh11Closure":
        "Section02.Aasen.UnitOuterSolve",
    "NumStability.Algorithms.Cholesky.BlockLDLTAllOneByOnePrintedCh11Closure":
        "Section01.BlockLDLT.AllOneByOne",
    "NumStability.Algorithms.Cholesky.BlockLDLTBunchTridiagonalCh11Closure":
        "Section01.Tridiagonal.BlockLDLT",
    "NumStability.Algorithms.Cholesky.BlockLDLTMixedPivotCh11Closure":
        "Section01.BlockLDLT.MixedPivot",
    "NumStability.Algorithms.Cholesky.BlockLDLTSolveBackwardCh11Closure":
        "Section01.BlockLDLT.SolveBackward",
    "NumStability.Algorithms.Cholesky.BunchKaufmanSolveCh11Closure":
        "Section01.PartialPivoting.SolveBackwardError",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalActualSolveCh11Closure":
        "Section01.Tridiagonal.ActualSolve",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalFactorBoundCh11Closure":
        "Section01.Tridiagonal.FactorBound",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalGrowthCh11Closure":
        "Section01.Tridiagonal.Growth",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalGrowthInvariantCh11Closure":
        "Section01.Tridiagonal.GrowthInvariant",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalHFactorCh11Closure":
        "Section01.Tridiagonal.HFactor",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalSparseFactorCh11Closure":
        "Section01.Tridiagonal.SparseFactor",
    "NumStability.Algorithms.Cholesky.BunchTridiagonalSparseSolveCh11Closure":
        "Section01.Tridiagonal.SparseSolve",
    "NumStability.Algorithms.Cholesky.Higham11BunchActualSharpGrowthClosure":
        "Section01.CompletePivoting.ActualSharpGrowth",
    "NumStability.Algorithms.Cholesky.Higham11BunchExactTrace":
        "Section01.CompletePivoting.ExactTrace",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanActualSelector":
        "Section01.PartialPivoting.ActualSelector",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExactGrowth":
        "Section01.PartialPivoting.ExactGrowth",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExactGrowthArithmetic":
        "Section01.PartialPivoting.ExactGrowthArithmetic",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExactTrace":
        "Section01.PartialPivoting.ExactTrace",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExplicitInverseSolve":
        "Section01.PartialPivoting.ExplicitInverseSolve",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanExplicitInverseTerminalClosedForm":
        "Section01.PartialPivoting.ExplicitInverseTerminal",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedAccumulated":
        "Section01.PartialPivoting.RoundedAccumulated",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedBridge":
        "Section01.PartialPivoting.RoundedBridge",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedClosure":
        "Section01.PartialPivoting.RoundedClosure",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedExecution":
        "Section01.PartialPivoting.RoundedExecution",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedFactors":
        "Section01.PartialPivoting.RoundedFactors",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGlobal":
        "Section01.PartialPivoting.RoundedGlobal",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGrowth":
        "Section01.PartialPivoting.RoundedGrowth",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedGrowthSolve":
        "Section01.PartialPivoting.RoundedGrowthSolve",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedMiddleSolve":
        "Section01.PartialPivoting.RoundedMiddleSolve",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedSolve":
        "Section01.PartialPivoting.RoundedSolve",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedTerminal":
        "Section01.PartialPivoting.RoundedTerminal",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanRoundedTerminalClosedForm":
        "Section01.PartialPivoting.RoundedTerminalClosedForm",
    "NumStability.Algorithms.Cholesky.Higham11BunchKaufmanSourceCorrection":
        "Section01.PartialPivoting.SourceCorrection",
    "NumStability.Algorithms.Cholesky.Higham11BunchSharpGrowthBridge":
        "Section01.CompletePivoting.SharpGrowthBridge",
    "NumStability.Algorithms.Cholesky.Higham11BunchTraceHadamard":
        "Section01.CompletePivoting.TraceHadamard",
    "NumStability.Algorithms.Cholesky.Higham11Chapter9ActualExecutorBridge":
        "Section01.Chapter09Bridge.ActualExecutor",
    "NumStability.Algorithms.Cholesky.Higham11Chapter9BridgeClosure":
        "Section01.Chapter09Bridge.ForwardError",
    "NumStability.Algorithms.Cholesky.Higham11RookExactTrace":
        "Section01.RookPivoting.ExactTrace",
    "NumStability.Algorithms.Cholesky.Higham11RookExecutorAdapter":
        "Section01.RookPivoting.ExecutorAdapter",
    "NumStability.Algorithms.Cholesky.Higham11RookRoundedGap":
        "Section01.RookPivoting.RoundedGap",
    "NumStability.Algorithms.Cholesky.Higham11RookSourceClosure":
        "Section01.RookPivoting.SourceClosure",
    "NumStability.Algorithms.Cholesky.Higham11SkewActualSelector":
        "Section03.SkewSymmetric.ActualSelector",
    "NumStability.Algorithms.Cholesky.Higham11SkewExactTrace":
        "Section03.SkewSymmetric.ExactTrace",
    "NumStability.Algorithms.Cholesky.Higham11SkewSourceCorrection":
        "Section03.SkewSymmetric.SourceCorrection",
    "NumStability.Algorithms.Cholesky.TwoByTwoSchurStepCh11Closure":
        "Section01.BlockLDLT.TwoByTwoSchurStep",
}


# Reviewed seam -> canonical leaf for HighamChapter11.lean.  Only leaves own
# declarations: Section01, Section01.PartialPivoting, Section02.Aasen and the
# other interior nodes stay declaration-free, so no destination becomes a
# declaration-bearing umbrella.
SECTION_SEED = (
    (r"§11\.1\.1 Complete pivoting", "Section01.CompletePivoting.Core"),
    (r"§11\.1\.2 Partial pivoting", "Section01.PartialPivoting.Core"),
    (r"§11\.1\.3 Rook pivoting", "Section01.RookPivoting.Core"),
    (r"§11\.1\.4 Tridiagonal matrices", "Section01.Tridiagonal.Core"),
    (r"Chapter 11 intro and §11\.1 ", "Section01.BlockFactorization"),
    (r"§11\.2 Aasen", "Section02.Aasen.Core"),
    (r"§11\.3 Skew-symmetric", "Section03.SkewSymmetric.Core"),
    (r"Problem proof-completion lemmas", "Problems.ProofCompletion"),
    (r"Problems", "Problems.Statements"),
)

# `deriving DecidableEq, Repr` output for the Theorem 11.4 branch enumeration
# declared at HighamChapter11.lean:2214, inside the §11.1.2 partial-pivoting
# seam.  These have no source declaration anchor of their own.
EXACT_ROUTES = (
    ("NumStability.Algorithms.HighamChapter11",
     "NumStability.instDecidableEqHigham11_4_BunchKaufmanActiveBranch",
     "Section01.PartialPivoting.Core"),
    ("NumStability.Algorithms.HighamChapter11",
     "NumStability.instReprHigham11_4_BunchKaufmanActiveBranch",
     "Section01.PartialPivoting.Core"),
    ("NumStability.Algorithms.HighamChapter11",
     "NumStability.instReprHigham11_4_BunchKaufmanActiveBranch.repr",
     "Section01.PartialPivoting.Core"),
)

SPEC = driver.ChapterSpec(
    chapter="11",
    destination_prefix="NumStability.Source.Higham.Chapter11",
    candidates=CANDIDATES,
    sectioned_module="NumStability.Algorithms.HighamChapter11",
    section_seed=SECTION_SEED,
    satellite_destinations=SATELLITES,
    exact_routes=EXACT_ROUTES,
    implementation_status="BLOCKED_ON_CH09_INTEGRATION",
    blocking_reason=(
        "Chapter 11 has real Chapter 9 dependencies: the equation (11.7) forward-error "
        "bridge and the actual block-LDL^T executor bridge both build on Chapter 9 "
        "material, and the tridiagonal and Aasen closures consume Chapter 9 GEPP results. "
        "Chapter 11 may not be implemented until Chapter 9 is integrated and globally "
        "verified, and Chapter 9 itself is BLOCKED_ON_BLOCKLU_INTEGRATION. Chapter 9 and "
        "Chapter 11 are strictly sequential waves, never parallel ones."
    ),
    cross_chapter_dependency_prefixes=(
        "NumStability.Algorithms.HighamChapter9",
        "NumStability.Source.Higham.Chapter09",
    ),
    required_gates=(
        "python tools/architecture/lane_claude_classification/check_ch11_contract.py --self-test",
        "python tools/architecture/lane_claude_classification/check_ch11_contract.py --mode pre"
        " --baseline-zip <packet>/baseline/parallel-base-declarations-v2.zip",
        "lake build NumStability.Algorithms.HighamChapter11 NumStability.Source.Higham.Chapter11"
        " NumStability.Source.Higham.Chapter11.Theorem07",
        "lake env lean NumStabilityTest/Worker/ClassificationAudit/Chapter11Historical.lean",
        "lake env lean NumStabilityTest/Worker/ClassificationAudit/Chapter11CanonicalExisting.lean",
        "python tools/architecture/check_layout.py",
        "python tools/architecture/check_compatibility.py",
        "python tools/architecture/check_provenance.py",
        "lake build NumStability NumStabilityTest",
        "lake test",
    ),
    notes=(
        "Preparation only: no canonical production module is created, no declaration is "
        "moved, no proof is rewritten, no import is edited, and no wrapper is added.",
        "The candidate family is exactly the 66 candidate_production rows of "
        "CH11_PREP_PATHS.tsv, not all of NumStability/Algorithms/Cholesky/.",
        "Cholesky.BunchTridiagonalCapstoneCh11Closure, Source.Higham.Chapter11.Theorem07 "
        "and Higham.Chapter11.Theorem11_7Capstone are read-only context and are never "
        "re-owned; no destination collides with the existing canonical Theorem07 slice.",
        "Each destination owns one contiguous region of one historical module, and no "
        "declaration-owning destination is a prefix of another.",
    ),
)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("pre", "stage", "post"))
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--emit", action="store_true")
    parser.add_argument("--baseline-zip", type=Path, default=DEFAULT_BASELINE)
    parser.add_argument("--directory", type=Path, default=CH11_DIR)
    args = parser.parse_args()

    if args.self_test:
        problems = driver.self_test()
        if problems:
            for problem in problems:
                print(f"ERROR: self-test: {problem}", file=sys.stderr)
            return 1
        print("Chapter 11 contract self-test passed: every rejection case is detected.")
        return 0

    if args.mode in {"stage", "post"}:
        print(
            f"ERROR: --mode {args.mode} requires a freshly generated candidate format-2 "
            "stream for the migrated tree. This lane is preparation only and must not "
            "fabricate post-migration evidence; the integrator runs stage/post after "
            "Chapter 9 is integrated and the Chapter 11 wave is implemented.",
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
        print(f"Emitted the Chapter 11 contract into {args.directory.relative_to(ROOT)}")
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
        "Chapter 11 pre-migration contract verified: routes complete and non-overlapping, "
        "ownership exact against the frozen format-2 baseline, private rewrites complete, "
        "destination graphs acyclic, import allowlists exact, Chapter 9 dependency edges "
        "recorded. Implementation remains BLOCKED_ON_CH09_INTEGRATION."
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
