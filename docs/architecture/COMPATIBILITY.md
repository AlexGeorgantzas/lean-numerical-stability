# Compatibility policy and path map

This migration changes canonical module paths without changing declaration
names or the historical meaning of `import NumStability`. Every old path in
the table remains an import-only forwarding module.

## Current forwarding paths

| Historical path | Canonical path |
| --- | --- |
| `NumStability.Algorithms.RecursiveSum` | `NumStability.Algorithms.Summation.Recursive` |
| `NumStability.Algorithms.PairwiseSum` | `NumStability.Algorithms.Summation.Pairwise` |
| `NumStability.Algorithms.InsertionSum` | `NumStability.Algorithms.Summation.Insertion` |
| `NumStability.Algorithms.SumTree` | `NumStability.Algorithms.Summation.Tree` |
| `NumStability.Algorithms.PlusMinusSum` | `NumStability.Algorithms.Summation.PlusMinus` |
| `NumStability.Algorithms.CompensatedSum` | `NumStability.Algorithms.Summation.Compensated` |
| `NumStability.Algorithms.DoublyCompensatedSum` | `NumStability.Algorithms.Summation.DoublyCompensated` |
| `NumStability.Algorithms.AccumulatorSum` | `NumStability.Algorithms.Summation.Accumulator` |
| `NumStability.Algorithms.TriangularSolveCombined` | `NumStability.Algorithms.LinearSystems.Triangular.Combined` |
| `NumStability.Analysis.Problem2_4` | `NumStability.Higham.Chapter02.Problem04` |
| `NumStability.Analysis.Problem2_7` | `NumStability.FloatingPoint.OperationLaws` and `NumStability.Higham.Chapter02.Problem07` |
| `NumStability.Analysis.Problem2_22` | `NumStability.Higham.Chapter02.Problem22` |
| `NumStability.Algorithms.HighamChapter8Lemma88SourceDiscrepancy` | `NumStability.Higham.Chapter08.Lemma8_8Discrepancy` |
| `NumStability.Algorithms.Cholesky.Higham10Theorem10_7Source` | `NumStability.Higham.Chapter10.Theorem10_7` |
| `NumStability.Algorithms.Cholesky.BunchTridiagonalCapstoneCh11Closure` | `NumStability.Higham.Chapter11.Theorem11_7Capstone` |
| `NumStability.Algorithms.LU.BlockLUTable13_1Families` | `NumStability.Higham.Chapter13.Table13_1` |
| `NumStability.Algorithms.Ch14SourceCorrections` | `NumStability.Higham.Chapter14.Discrepancies` |
| `NumStability.Algorithms.LeastSquares.Higham20SourceAliases` | `NumStability.Higham.Chapter20.SourceAliases` |
| `NumStability.Algorithms.HighamChapter3NoGuardDotBridge` | `NumStability.Higham.CrossChapter.Chapter02To03NoGuardDot` |
| `NumStability.Algorithms.HighamChapter15Ch7PracticalBoundBridge` | `NumStability.Higham.CrossChapter.Chapter07To15PracticalBound` |
| `NumStability.Algorithms.HighamChapter12Ch9GenericSolverBridge` | `NumStability.Higham.CrossChapter.Chapter09To12GenericSolver` |
| `NumStability.Algorithms.HighamChapter12Ch9SolverBridge` | `NumStability.Higham.CrossChapter.Chapter09To12Solver` |
| `NumStability.Analysis.NonrandomRounding` | `NumStability.Analysis.NonrandomRounding.Conclusions` |

The historical nonrandom-rounding path remains the complete compatibility
import through the transitive layer chain; new code may select its narrower
semantic submodules.

CI runs `tools/architecture/check_compatibility.py` to require that every
tabled historical file contains only its documented imports and that
production modules use no tabled old path. Old-only and canonical-only Lean
smoke modules compile the two surfaces independently; summation wrappers and
the Chapter 9-to-12 bridge pair also have isolated per-wrapper checks where
sibling dependencies could otherwise mask a regression.

## Removal rule

No forwarding module is removed in this migration. A future removal requires a
declared breaking release, release-note and migration-guide entries, a search
showing production consumers use canonical paths, and an explicit update to
the old-path smoke tests. Until then, CI compiles both curated entry points and
representative historical imports.
