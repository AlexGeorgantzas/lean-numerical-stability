# Compatibility policy and path map

This migration changes canonical module paths without changing declaration
names or the historical meaning of `import NumStability`. Every old path in
the table remains an import-only forwarding module.

## Current forwarding paths

| Historical path | Canonical path |
| --- | --- |
| `NumStability.Higham` | `NumStability.Source.Higham` |
| `NumStability.Higham.Chapter02.Problem04` | `NumStability.Source.Higham.Chapter02.Problem04` |
| `NumStability.Higham.Chapter02.Problem07` | `NumStability.Source.Higham.Chapter02.Problem07` |
| `NumStability.Higham.Chapter02.Problem22` | `NumStability.Source.Higham.Chapter02.Problem22` |
| `NumStability.Higham.Chapter08.Lemma8_8Discrepancy` | `NumStability.Source.Higham.Chapter08.Lemma08Discrepancy` |
| `NumStability.Higham.Chapter10.Theorem10_7` | `NumStability.Source.Higham.Chapter10.Theorem07` |
| `NumStability.Higham.Chapter11.Theorem11_7Capstone` | `NumStability.Source.Higham.Chapter11.Theorem07` |
| `NumStability.Higham.Chapter13.Table13_1` | `NumStability.Source.Higham.Chapter13.Equation25` and `NumStability.Source.Higham.Chapter13.Table01` |
| `NumStability.Higham.Chapter14.Discrepancies` | `NumStability.Source.Higham.Chapter14.Discrepancies` |
| `NumStability.Higham.Chapter20.SourceAliases` | `NumStability.Source.Higham.Chapter20.Equation32`, `NumStability.Source.Higham.Chapter20.Lemma06`, and `NumStability.Source.Higham.Chapter20.Theorem01` |
| `NumStability.Higham.CrossChapter.Chapter02To03NoGuardDot` | `NumStability.Algorithms.Arithmetic.DotProduct.NoGuard` and `NumStability.Source.Higham.CrossChapter.NoGuardDotProduct` |
| `NumStability.Higham.CrossChapter.Chapter07To15PracticalBound` | `NumStability.Source.Higham.CrossChapter.PracticalConditionBound` |
| `NumStability.Higham.CrossChapter.Chapter09To12GenericSolver` | `NumStability.Source.Higham.CrossChapter.LUSolverWeights.Factorization` |
| `NumStability.Higham.CrossChapter.Chapter09To12Solver` | `NumStability.Source.Higham.CrossChapter.LUSolverWeights.Doolittle` |
| `NumStability.Algorithms.RecursiveSum` | `NumStability.Algorithms.Summation.Recursive` |
| `NumStability.Algorithms.PairwiseSum` | `NumStability.Algorithms.Summation.Pairwise` |
| `NumStability.Algorithms.InsertionSum` | `NumStability.Algorithms.Summation.Insertion` |
| `NumStability.Algorithms.SumTree` | `NumStability.Algorithms.Summation.Tree` |
| `NumStability.Algorithms.Summation.Tree.RecursiveBridge` | `NumStability.Algorithms.Summation.Tree.Chain` |
| `NumStability.Algorithms.PlusMinusSum` | `NumStability.Algorithms.Summation.PlusMinus` |
| `NumStability.Algorithms.CompensatedSum` | `NumStability.Algorithms.Summation.Compensated` |
| `NumStability.Algorithms.KahanCompensatedFiniteFormat` | `NumStability.Source.Higham.Chapter04.Section03.FiniteFormat` |
| `NumStability.Algorithms.DoublyCompensatedSum` | `NumStability.Algorithms.Summation.DoublyCompensated` |
| `NumStability.Algorithms.AccumulatorSum` | `NumStability.Algorithms.Summation.Accumulator` |
| `NumStability.Algorithms.TriangularSolve` | `NumStability.Algorithms.LinearSystems.Triangular.BackSubstitution` |
| `NumStability.Algorithms.ForwardSub` | `NumStability.Algorithms.LinearSystems.Triangular.ForwardSubstitution` |
| `NumStability.Algorithms.TriangularForwardBound` | `NumStability.Algorithms.LinearSystems.Triangular.DiagonalDominance` |
| `NumStability.Algorithms.InverseBounds` | `NumStability.Algorithms.LinearSystems.Triangular.InverseBounds` |
| `NumStability.Algorithms.TriangularForwardComparison` | `NumStability.Algorithms.LinearSystems.Triangular.ComparisonBounds` |
| `NumStability.Algorithms.TriangularSolveCombined` | `NumStability.Algorithms.LinearSystems.Triangular.Combined` |
| `NumStability.Analysis.Problem2_4` | `NumStability.Source.Higham.Chapter02.Problem04` |
| `NumStability.Analysis.Problem2_7` | `NumStability.FloatingPoint.OperationLaws` and `NumStability.Source.Higham.Chapter02.Problem07` |
| `NumStability.Analysis.Problem2_22` | `NumStability.Source.Higham.Chapter02.Problem22` |
| `NumStability.Algorithms.HighamChapter8Lemma88SourceDiscrepancy` | `NumStability.Source.Higham.Chapter08.Lemma08Discrepancy` |
| `NumStability.Algorithms.Cholesky.Higham10Theorem10_7Source` | `NumStability.Source.Higham.Chapter10.Theorem07` |
| `NumStability.Algorithms.Cholesky.BunchTridiagonalCapstoneCh11Closure` | `NumStability.Source.Higham.Chapter11.Theorem07` |
| `NumStability.Algorithms.HighamChapter12` | `NumStability.Source.Higham.Chapter12.IterativeRefinement` |
| `NumStability.Algorithms.HighamChapter12OmegaDiscontinuity` | `NumStability.Source.Higham.Chapter12.OmegaDiscontinuity` |
| `NumStability.Algorithms.HighamChapter12Problem12_2` | `NumStability.Source.Higham.Chapter12.Problem02` |
| `NumStability.Algorithms.LU.BlockLUTable13_1Families` | `NumStability.Source.Higham.Chapter13.Equation25` and `NumStability.Source.Higham.Chapter13.Table01` |
| `NumStability.Algorithms.LU.Higham13DemmelSharpMultiplier` | `NumStability.Source.Higham.Chapter13.DemmelSharpMultiplier` |
| `NumStability.Algorithms.Ch14SchulzIteration` | `NumStability.Source.Higham.Chapter14.Section05.SquareIteration` |
| `NumStability.Algorithms.Ch14SchulzRectangular` | `NumStability.Source.Higham.Chapter14.Section05.RectangularIteration` |
| `NumStability.Algorithms.Ch14SchulzSpectralConvergence` | `NumStability.Source.Higham.Chapter14.Section05.SpectralConvergence` |
| `NumStability.Algorithms.Ch14SourceCorrections` | `NumStability.Source.Higham.Chapter14.Discrepancies` |
| `NumStability.Algorithms.Ch4KahanFiniteFamily` | `NumStability.Source.Higham.Chapter04.Equation08.FiniteFamily` |
| `NumStability.Algorithms.LeastSquares.Higham20SourceAliases` | `NumStability.Source.Higham.Chapter20.Equation32`, `NumStability.Source.Higham.Chapter20.Lemma06`, and `NumStability.Source.Higham.Chapter20.Theorem01` |
| `NumStability.Algorithms.Vandermonde.Higham22` | `NumStability.Source.Higham.Chapter22.VandermondeSystems` |
| `NumStability.Algorithms.Vandermonde.Higham22MonomialClosure` | `NumStability.Source.Higham.Chapter22.MonomialResidual` |
| `NumStability.Algorithms.Vandermonde.Higham22Problem22_7` | `NumStability.Source.Higham.Chapter22.Problem07` |
| `NumStability.Algorithms.Vandermonde.Higham22Ch12RefinementBridge` | `NumStability.Source.Higham.Chapter22.Section03.RealRefinement` |
| `NumStability.Algorithms.Vandermonde.Higham22ComplexConfluentRefinementBridge` | `NumStability.Source.Higham.Chapter22.Section03.ComplexConfluentRefinement` |
| `NumStability.Algorithms.FastMatMul.Higham23` | `NumStability.Algorithms.FastMatMul.Internal.LegacyBounds`, `NumStability.Source.Higham.Chapter23.BalancedScaling`, `NumStability.Source.Higham.Chapter23.BilinearAlgorithm`, `NumStability.Source.Higham.Chapter23.BlockAlgorithms`, `NumStability.Source.Higham.Chapter23.ConventionalMultiplication`, `NumStability.Source.Higham.Chapter23.ErrorRecurrences`, `NumStability.Source.Higham.Chapter23.GammaAsymptotics`, `NumStability.Source.Higham.Chapter23.ThreeM`, and `NumStability.Source.Higham.Chapter23.WinogradInnerProduct` |
| `NumStability.Algorithms.FastMatMul.Higham23Bini` | `NumStability.Algorithms.FastMatMul.Internal.LegacyBounds`, `NumStability.Source.Higham.Chapter23.BalancedScaling`, `NumStability.Source.Higham.Chapter23.BilinearAlgorithm`, `NumStability.Source.Higham.Chapter23.BiniLotti`, `NumStability.Source.Higham.Chapter23.BlockAlgorithms`, `NumStability.Source.Higham.Chapter23.ConventionalMultiplication`, `NumStability.Source.Higham.Chapter23.Equation11`, `NumStability.Source.Higham.Chapter23.ErrorRecurrences`, `NumStability.Source.Higham.Chapter23.GammaAsymptotics`, `NumStability.Source.Higham.Chapter23.Theorem02`, `NumStability.Source.Higham.Chapter23.Theorem03`, `NumStability.Source.Higham.Chapter23.ThreeM`, and `NumStability.Source.Higham.Chapter23.WinogradInnerProduct` |
| `NumStability.Algorithms.FastMatMul.Higham23Problem23_8` | `NumStability.Algorithms.FastMatMul.Internal.LegacyBounds`, `NumStability.Source.Higham.Chapter23.BalancedScaling`, `NumStability.Source.Higham.Chapter23.BilinearAlgorithm`, `NumStability.Source.Higham.Chapter23.BlockAlgorithms`, `NumStability.Source.Higham.Chapter23.ConventionalMultiplication`, `NumStability.Source.Higham.Chapter23.ErrorRecurrences`, `NumStability.Source.Higham.Chapter23.GammaAsymptotics`, `NumStability.Source.Higham.Chapter23.Problem08`, `NumStability.Source.Higham.Chapter23.Theorem02`, `NumStability.Source.Higham.Chapter23.Theorem03.Execution`, `NumStability.Source.Higham.Chapter23.ThreeM`, and `NumStability.Source.Higham.Chapter23.WinogradInnerProduct` |
| `NumStability.Algorithms.FastMatMul.Higham23Recursive` | `NumStability.Algorithms.FastMatMul.Internal.LegacyBounds`, `NumStability.Source.Higham.Chapter23.BalancedScaling`, `NumStability.Source.Higham.Chapter23.BilinearAlgorithm`, `NumStability.Source.Higham.Chapter23.BlockAlgorithms`, `NumStability.Source.Higham.Chapter23.ConventionalMultiplication`, `NumStability.Source.Higham.Chapter23.ErrorRecurrences`, `NumStability.Source.Higham.Chapter23.GammaAsymptotics`, `NumStability.Source.Higham.Chapter23.Theorem02`, `NumStability.Source.Higham.Chapter23.Theorem03.Execution`, `NumStability.Source.Higham.Chapter23.ThreeM`, and `NumStability.Source.Higham.Chapter23.WinogradInnerProduct` |
| `NumStability.Algorithms.FastMatMul.Higham23Remaining` | `NumStability.Algorithms.FastMatMul.Internal.LegacyBounds`, `NumStability.Source.Higham.Chapter23.BalancedScaling`, `NumStability.Source.Higham.Chapter23.BilinearAlgorithm`, `NumStability.Source.Higham.Chapter23.BlockAlgorithms`, `NumStability.Source.Higham.Chapter23.ConventionalMultiplication`, `NumStability.Source.Higham.Chapter23.Equation11`, `NumStability.Source.Higham.Chapter23.ErrorRecurrences`, `NumStability.Source.Higham.Chapter23.GammaAsymptotics`, `NumStability.Source.Higham.Chapter23.Theorem02`, `NumStability.Source.Higham.Chapter23.Theorem03`, `NumStability.Source.Higham.Chapter23.ThreeM`, and `NumStability.Source.Higham.Chapter23.WinogradInnerProduct` |
| `NumStability.Algorithms.FastMatMul.Higham23ThreeMStrassen` | `NumStability.Algorithms.FastMatMul.Internal.LegacyBounds`, `NumStability.Source.Higham.Chapter23.BalancedScaling`, `NumStability.Source.Higham.Chapter23.BilinearAlgorithm`, `NumStability.Source.Higham.Chapter23.BiniLotti`, `NumStability.Source.Higham.Chapter23.BlockAlgorithms`, `NumStability.Source.Higham.Chapter23.ConventionalMultiplication`, `NumStability.Source.Higham.Chapter23.Equation11`, `NumStability.Source.Higham.Chapter23.ErrorRecurrences`, `NumStability.Source.Higham.Chapter23.GammaAsymptotics`, `NumStability.Source.Higham.Chapter23.Theorem02`, `NumStability.Source.Higham.Chapter23.Theorem03`, `NumStability.Source.Higham.Chapter23.ThreeM`, `NumStability.Source.Higham.Chapter23.ThreeMStrassen`, and `NumStability.Source.Higham.Chapter23.WinogradInnerProduct` |
| `NumStability.Algorithms.FFT.Higham24` | `NumStability.Source.Higham.Chapter24.FourierTransform` |
| `NumStability.Algorithms.FFT.Higham24Radix2` | `NumStability.Source.Higham.Chapter24.Radix2FFT` |
| `NumStability.Algorithms.Circulant.Higham24` | `NumStability.Source.Higham.Chapter24.CirculantSystems` |
| `NumStability.Algorithms.Circulant.Higham24ForwardPerturbation` | `NumStability.Source.Higham.Chapter24.ForwardFFTPerturbation` |
| `NumStability.Algorithms.Circulant.Higham24Rounded` | `NumStability.Source.Higham.Chapter24.RoundedDiagonalSolve` |
| `NumStability.Algorithms.Circulant.Higham24InverseFFT` | `NumStability.Source.Higham.Chapter24.InverseFFT` |
| `NumStability.Algorithms.Circulant.Higham24LiteralSolver` | `NumStability.Source.Higham.Chapter24.RoundedCirculantSolver` |
| `NumStability.Algorithms.Circulant.Higham24BackwardStability` | `NumStability.Source.Higham.Chapter24.FFTBackwardStability` |
| `NumStability.Algorithms.Circulant.Higham24Structured` | `NumStability.Source.Higham.Chapter24.StructuredMixedStability` |
| `NumStability.Algorithms.Circulant.Higham24ForwardError` | `NumStability.Source.Higham.Chapter24.CirculantForwardError` |
| `NumStability.Algorithms.Nonlinear.Higham25` | `NumStability.Source.Higham.Chapter25.NonlinearSystems` |
| `NumStability.Algorithms.Nonlinear.Higham25EigenClosure` | `NumStability.Source.Higham.Chapter25.Eigenproblem` |
| `NumStability.Algorithms.Nonlinear.Higham25Problem25_1` | `NumStability.Source.Higham.Chapter25.Problem01` |
| `NumStability.Algorithms.SoftwareIssues.Higham27` | `NumStability.Source.Higham.Chapter27.SoftwareEnvironment` |
| `NumStability.Algorithms.SoftwareIssues.Higham27Pythag` | `NumStability.Source.Higham.Chapter27.Problem06` |
| `NumStability.Algorithms.HighamChapter3NoGuardDotBridge` | `NumStability.Algorithms.Arithmetic.DotProduct.NoGuard` and `NumStability.Source.Higham.CrossChapter.NoGuardDotProduct` |
| `NumStability.Algorithms.HighamChapter15Ch7PracticalBoundBridge` | `NumStability.Source.Higham.CrossChapter.PracticalConditionBound` |
| `NumStability.Algorithms.HighamChapter12Ch9GenericSolverBridge` | `NumStability.Source.Higham.CrossChapter.LUSolverWeights.Factorization` |
| `NumStability.Algorithms.HighamChapter12Ch9SolverBridge` | `NumStability.Source.Higham.CrossChapter.LUSolverWeights.Doolittle` |
| `NumStability.Algorithms.AutomaticErrorAnalysis.Higham26` | `NumStability.Source.Higham.Chapter26.AlternatingDirections.ExactExecution`, `NumStability.Source.Higham.Chapter26.CubicRoots.DepressedCubic`, `NumStability.Source.Higham.Chapter26.CubicRoots.MonicCubic`, `NumStability.Source.Higham.Chapter26.Equation01`, `NumStability.Source.Higham.Chapter26.Equation02`, `NumStability.Source.Higham.Chapter26.Equation03`, `NumStability.Source.Higham.Chapter26.Equation04`, `NumStability.Source.Higham.Chapter26.Equation05.CardanoRoots`, `NumStability.Source.Higham.Chapter26.Equation05.ComplexBranches`, `NumStability.Source.Higham.Chapter26.Equation05.RealBranches`, `NumStability.Source.Higham.Chapter26.Equation05.ZeroBranchDiscrepancy`, `NumStability.Source.Higham.Chapter26.Equation06`, `NumStability.Source.Higham.Chapter26.Equation07`, `NumStability.Source.Higham.Chapter26.Equation08`, `NumStability.Source.Higham.Chapter26.IntervalArithmetic.DependencyExamples`, `NumStability.Source.Higham.Chapter26.IntervalArithmetic.DirectedRounding`, `NumStability.Source.Higham.Chapter26.IntervalArithmetic.ExactOperations`, `NumStability.Source.Higham.Chapter26.MultidirectionalSearch.Execution`, and `NumStability.Source.Higham.Chapter26.MultidirectionalSearch.Simplex` |
| `NumStability.Algorithms.AutomaticErrorAnalysis.Higham26SourceSearch` | `NumStability.Source.Higham.Chapter26` |
| `NumStability.Algorithms.HighamChapter4KaoWangScope` | `NumStability.Source.Higham.Chapter04.Section02.KaoWangCitationDiscrepancy` |
| `NumStability.Algorithms.Problem44SixTerm` | `NumStability.Source.Higham.Chapter04.Problem04` |
| `NumStability.Algorithms.StationaryIterationSeries` | `NumStability.Source.Higham.Chapter17.Equation08`, `NumStability.Source.Higham.Chapter17.Equation12`, `NumStability.Source.Higham.Chapter17.Equation15`, `NumStability.Source.Higham.Chapter17.Equation16`, `NumStability.Source.Higham.Chapter17.Equation17`, `NumStability.Source.Higham.Chapter17.Equation20`, and `NumStability.Source.Higham.Chapter17.Problem01` |
| `NumStability.Analysis.Ch17SemiconvergentBlockFormSourceClosure` | `NumStability.Source.Higham.Chapter17.Equation22` |
| `NumStability.Analysis.NonrandomRounding` | `NumStability.Source.Higham.Chapter01.Section17` |
| `NumStability.Analysis.NonrandomRounding.Conclusions` | `NumStability.Source.Higham.Chapter01.Section17.ErrorSpread` |
| `NumStability.Analysis.NonrandomRounding.Core` | `NumStability.Source.Higham.Chapter01.Section17.HornerEvaluation` |
| `NumStability.Analysis.NonrandomRounding.GridVariation` | `NumStability.Source.Higham.Chapter01.Section17.GridVariation` |
| `NumStability.Analysis.NonrandomRounding.SourceInterval` | `NumStability.Source.Higham.Chapter01.Section17.SourceInterval` |
| `NumStability.Analysis.NonrandomRounding.StoredGrid` | `NumStability.Source.Higham.Chapter01.Section17.StoredGrid` |

The fourteen Chapter 12, 13, 14, 22, and 27 rows above are exact one-to-one
forwarders. The canonical chapter aggregates are discovery entry points, not
wrapper targets: `NumStability.Source.Higham.Chapter12`,
`NumStability.Source.Higham.Chapter14.Section05`,
`NumStability.Source.Higham.Chapter22`,
`NumStability.Source.Higham.Chapter22.Section03`, and
`NumStability.Source.Higham.Chapter27` contain only documentation and imports.
The compatibility inventory now contains 89 wrappers with 187 direct canonical
targets.

The historical nonrandom-rounding path remains the complete compatibility
import for the canonical Section 1.17 aggregate. Its five historical child
paths are exact import-only wrappers for the corresponding semantic leaves;
new code should import the canonical Chapter 1 paths directly.

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
