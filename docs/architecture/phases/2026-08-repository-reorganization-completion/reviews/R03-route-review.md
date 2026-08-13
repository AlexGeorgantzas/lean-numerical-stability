# R03 exact-C0002 semantic route review

Authority: `primary-human`

Planning branch: `B0005` / wave `R03` / projection `P0005`.

All classifications and routes in this review are frozen against accepted C0002
code commit `9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd`. The exact inventory is
`checkpoints/C0002-inventory.tsv`, SHA-256
`BB5AE8029CC3DC547BA1E4C8B581BA11948E527810AC29F0EBE8E1CC5D81BF02`.
The reviewed format-2 graph is `benchmark-results/C0002-combined.tsv`, SHA-256
`E03DB7A24886AD0B45C7371FE30ACE3AD135B3C4CC9866D65186753CD14FAD4C`.
No declaration graph was regenerated for this review.

## Exact scope and classification

The selector is every and only C0002 inventory row with `wave_id = R03`: 47
owners and an exhaustive 2,595-owner forbidden complement. The selected debt
counts recompute to 23 unclassified modules, 9 mixed modules, 13 missing-module
docstrings, 24 noncanonical modules, 2 declaration-bearing umbrellas, and 0
unsorted aggregate imports. The format-2 projection contains 2,389 declarations:
1,987 public, 398 private, and 4 internal.

The fresh owner classification is complete:

- The 31 all-source relocation owners are
  `NumStability.Algorithms.Ch5DerivativeError`,
  `NumStability.Algorithms.Ch5SourceClosure`,
  `NumStability.Algorithms.Higham5FastPolynomialEvaluation`,
  `NumStability.Algorithms.Higham5PatersonStockmeyer`,
  `NumStability.Algorithms.Higham726Rump`,
  `NumStability.Algorithms.HighamChapter5ComplexAlgorithm51`,
  `NumStability.Algorithms.HighamChapter8`,
  `NumStability.Algorithms.HighamChapters1To9SourceClosure`,
  `NumStability.Algorithms.KahanAbsolute`,
  `NumStability.Algorithms.WilkinsonAttainability`,
  `NumStability.Analysis.CancellationOfRoundingErrors`,
  `NumStability.Analysis.DoubleRounding`,
  `NumStability.Analysis.HighamChapter2ElementaryFunctions`,
  `NumStability.Analysis.HighamChapter2FmaDiscriminant`,
  `NumStability.Analysis.HighamChapter2Lindemann`,
  `NumStability.Analysis.HighamChapter7`,
  `NumStability.Analysis.HighamChapter7Rectangular`,
  `NumStability.Analysis.IncreasingPrecision`,
  `NumStability.Analysis.InstabilityWithoutCancellation`,
  `NumStability.Analysis.Problem2_10`,
  `NumStability.Analysis.Problem2_12`,
  `NumStability.Analysis.Problem2_13`,
  `NumStability.Analysis.Problem2_14`,
  `NumStability.Analysis.Problem2_17`,
  `NumStability.Analysis.Problem2_20`,
  `NumStability.Analysis.Problem2_24`,
  `NumStability.Analysis.Problem2_27`,
  `NumStability.Analysis.Problem2_3`,
  `NumStability.Source.Higham.Chapter06.Theorem05.DistanceToSingularity.Chapter07Equation26`,
  `NumStability.Source.Higham.Chapter12.IterativeRefinement`, and
  `NumStability.Source.Higham.Chapter12.IterativeRefinement.Chapter12Bounds`.
- The 3 all-reusable relocation owners are
  `NumStability.Algorithms.Horner`,
  `NumStability.Algorithms.LU.Doolittle`, and
  `NumStability.Analysis.FloatingPointArithmetic`.
- `NumStability.Analysis.AccuracyTests` and
  `NumStability.Analysis.SampleVariance` receive the exact reusable/source
  declaration splits below.
- The 8 reusable document-only owners retain their exact modules:
  `NumStability.Algorithms.LinearSystems.IterativeRefinement.Core`, the five
  selected `NumStability.Algorithms.LinearSystems.LU.Doolittle.*` leaves,
  `NumStability.Algorithms.Summation.Tree.ArbitraryOrderError.PivotNormalized`,
  and `NumStability.FloatingPoint.Model`.
- The 3 source document-only owners retain their exact modules:
  `NumStability.Source.Higham.Chapter08.Equation15.GlobalEnvelopeCounterexample.RawCube`,
  `NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.ArbitraryOrder`,
  and `NumStability.Source.Higham.Chapter12.IterativeRefinement.LegacyChapter11Surface`.
  The last owner retains 17 public source declarations and 4 internal
  historical-surface declarations and receives an explicit historical-numbering
  module docstring.

The exact owner-to-destination contract, declaration counts, compatibility
behavior, and approval state are frozen in
`branches/B0005-module-routes.tsv`. Its 47 rows are sorted by owner module and
contain no deferred action.

## Destination declaration counts

The 257 declarations in the 11 document-only owners remain at their exact
owners. The other 2,132 declarations relocate to these 48 exact destinations:

```text
NumStability.Algorithms.LinearSystems.LU.Doolittle.Assembly.Core	14
NumStability.Algorithms.PolynomialEvaluation.DerivativeEvaluation.ErrorBounds	6
NumStability.Analysis.Approximation.SineTaylor.OddDegreeFiveError.Theorems	3
NumStability.Analysis.FloatingPointArithmetic.IeeeSpecialValueOperations.Results	234
NumStability.Analysis.Statistics.SampleVariance.RoundingErrorBounds.Theorems	8
NumStability.Source.Higham.Chapter01.Problem10.TwoPassSampleVariance.RemainderBound.Theorem	2
NumStability.Source.Higham.Chapter01.Section09.SampleVariance.IeeeSingleOnePassCounterexample.Results	66
NumStability.Source.Higham.Chapter01.Section12.InstabilityWithoutCancellation.PivotingExample	6
NumStability.Source.Higham.Chapter01.Section13.IncreasingPrecision.BinaryStorageExamples	34
NumStability.Source.Higham.Chapter01.Section14.CancellationOfRoundingErrors.Algorithm02RoundedCore	27
NumStability.Source.Higham.Chapter02.Problem03.AdjacentPrecisionValues.Results.Theorems	41
NumStability.Source.Higham.Chapter02.Problem09.DoubleRounding.Counterexample.Results	15
NumStability.Source.Higham.Chapter02.Problem10.DivisionRoundTrip.ExhaustiveBinary64.Results	1114
NumStability.Source.Higham.Chapter02.Problem12.ReciprocalProduct.Results.Theorems	8
NumStability.Source.Higham.Chapter02.Problem13.ReciprocalProductThreshold.Results.Theorems	72
NumStability.Source.Higham.Chapter02.Problem14.UnitRoundoffProbe.IeeeExamples.Results	20
NumStability.Source.Higham.Chapter02.Problem21.HypotenuseNormalization.StandardModelCounterexample.Results	5
NumStability.Source.Higham.Chapter02.Problem25.NonzeroEvaluation.IeeeFiniteSystems.Results	30
NumStability.Source.Higham.Chapter02.Problem28.IterativeDivisionTermination.UnderflowAwareConvergence.Results	14
NumStability.Source.Higham.Chapter02.Section06.Discriminant.FusedMultiplyAdd.Counterexample.Results	10
NumStability.Source.Higham.Chapter02.Section06.Discriminant.StandardModel.Counterexample.Results	6
NumStability.Source.Higham.Chapter02.Section10.ArctangentRange.Counterexample.Results	7
NumStability.Source.Higham.Chapter02.Section10.Tablemaker.FiniteSeparation.Results.Theorems	4
NumStability.Source.Higham.Chapter02.Section11.AccuracyTests.CodySineResults.Theorems	8
NumStability.Source.Higham.Chapter03.Problem11.KahanAbsoluteValue.IeeeDoubleTrace.Results	123
NumStability.Source.Higham.Chapter04.Problem02.WilkinsonAttainability.IeeeDoubleTrace.Results	26
NumStability.Source.Higham.Chapter05.Algorithm01.ComplexHorner.ErrorBounds.Theorems	8
NumStability.Source.Higham.Chapter05.Section02.BidiagonalDerivativeAnalysis.Results.Theorems	16
NumStability.Source.Higham.Chapter05.Section02.DerivativeError.Results.Theorems	4
NumStability.Source.Higham.Chapter05.Section04.PatersonStockmeyer.Results.Theorems	6
NumStability.Source.Higham.Chapter05.Section05.FastPolynomialEvaluation.Results.Theorems	4
NumStability.Source.Higham.Chapter07.Equation17.KahanConditioningExample	10
NumStability.Source.Higham.Chapter07.Equation26.DistanceToSingularity.Results	1
NumStability.Source.Higham.Chapter07.Equation26.RumpCycle.Results.Theorems	12
NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem03.RectangularResults	3
NumStability.Source.Higham.Chapter07.LinearSystemsConditioning.Theorem05.RowInfinityScaleCounterexample.Theorems	7
NumStability.Source.Higham.Chapter08.Equation02.TriangularSubstitution.RelativeInfinityNormBounds.Theorems	5
NumStability.Source.Higham.Chapter08.Equation15.FanInExecutor.FirstOrderResidual	1
NumStability.Source.Higham.Chapter08.Equation15.GlobalEnvelopeCounterexample.LocalCancellationResults.Theorems	4
NumStability.Source.Higham.Chapter08.Equation18.FanInExecutor.FirstOrderForwardError	2
NumStability.Source.Higham.Chapter08.Problem02.ComparisonMatrixWitness.ArbitraryRatios.Theorems	8
NumStability.Source.Higham.Chapter08.Problem07.DiagonalScaling.Results.Theorems	5
NumStability.Source.Higham.Chapter08.Problem08.SingleEntrySingularity.Results.Theorems	7
NumStability.Source.Higham.Chapter08.Problem09.KahanSingularValues.Results.Theorems	54
NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.ComparisonConditioningResults.Theorems	12
NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseNormResults.Theorems	27
NumStability.Source.Higham.Chapter12.IterativeRefinement.ForwardErrorBounds.Results	5
NumStability.Source.Higham.Chapter12.IterativeRefinement.Results.Theorems	28
```

The five reusable destinations receive 265 relocated declarations. The 43
source destinations receive 1,867 relocated declarations. Together with the
210 retained reusable declarations, 43 retained public source declarations,
and 4 retained internal declarations, this accounts for all 2,389 declarations.

## Exact mixed-owner splits

The C0002 `mixed` label reflects pre-W12 ownership as well as current content.
Private declarations are internal proof support and must move with their exact
public reverse-dependency component; no private helper becomes an independent
API module.

| C0002 mixed owner | reusable declarations | source declarations | internal/private support | frozen decision |
| --- | ---: | ---: | ---: | --- |
| `NumStability.Algorithms.HighamChapter8` | 0 | 55 public | 67 private | Eight source dependency components, enumerated below. |
| `NumStability.Analysis.CancellationOfRoundingErrors` | 0 | 23 public | 4 private | One Section 1.14 Algorithm 2 source closure. |
| `NumStability.Analysis.DoubleRounding` | 0 | 6 public | 9 private | One printed Problem 2.9 source closure. |
| `NumStability.Analysis.FloatingPointArithmetic` | 232 public | 0 | 2 private reusable support | One reusable IEEE special-value-operation closure; the old umbrella becomes declaration-free. |
| `NumStability.Analysis.HighamChapter7` | 0 | 2 public | 15 private | A 10-declaration Equation 7.17 closure and a 7-declaration Theorem 7.5 closure. |
| `NumStability.Analysis.HighamChapter7Rectangular` | 0 | 2 public | 1 private | One Theorem 7.3 source closure. |
| `NumStability.Analysis.IncreasingPrecision` | 0 | 19 public | 15 private | One Section 1.13 source closure. |
| `NumStability.Analysis.InstabilityWithoutCancellation` | 0 | 6 public | 0 | One Section 1.12 source closure. |
| `NumStability.Analysis.SampleVariance` | 7 public | 45 public | 1 reusable-support private plus 23 source-support private | Reusable 8, Problem 1.10 source 2, and Section 1.9 binary32 source 66. |

Only `SampleVariance` remains a genuine reusable/source mixture after fresh
declaration review. The other eight mixed owners resolve wholly to source or
wholly to reusable mathematics, with private support co-located.

The eight undirected declaration-dependency components of
`NumStability.Algorithms.HighamChapter8` are exact in the C0002 graph:

| component anchor and source locator | total | public | private | destination |
| --- | ---: | ---: | ---: | --- |
| `higham8_problem8_9_kahan_secondSmallestSingularValue` / Problem 8.9 | 54 | 23 | 31 | `NumStability.Source.Higham.Chapter08.Problem09.KahanSingularValues.Results.Theorems` |
| `higham8_12_WInv_le_ZInvFormula` / Theorems 8.12, 8.14 and Problem 8.6 shared inverse-norm closure | 27 | 11 | 16 | `NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.InverseNormResults.Theorems` |
| `higham8_4_upperTriangularMMatrix_condAtSolution_le` / Problem 8.4 and Lemma 8.9 shared comparison closure | 12 | 5 | 7 | `NumStability.Source.Higham.Chapter08.Section03.TriangularSystems.ComparisonConditioningResults.Theorems` |
| `higham8_2_comparisonInverseRatios_arbitrarily_large` / Problem 8.2 | 8 | 3 | 5 | `NumStability.Source.Higham.Chapter08.Problem02.ComparisonMatrixWitness.ArbitraryRatios.Theorems` |
| `higham8_8_bestRankOneSingularUpdate_exists` / Problem 8.8 | 7 | 5 | 2 | `NumStability.Source.Higham.Chapter08.Problem08.SingleEntrySingularity.Results.Theorems` |
| `higham8_2_backSub_relative_infNorm_bound` / Equation 8.2 | 5 | 4 | 1 | `NumStability.Source.Higham.Chapter08.Equation02.TriangularSubstitution.RelativeInfinityNormBounds.Theorems` |
| `higham8_7_scaledStrictRowDiagDominant_invInfNorm_le` / Problem 8.7 | 5 | 3 | 2 | `NumStability.Source.Higham.Chapter08.Problem07.DiagonalScaling.Results.Theorems` |
| `higham8_14_local_envelope_not_relative_after_cancellation` / local-cancellation result | 4 | 1 | 3 | `NumStability.Source.Higham.Chapter08.Equation15.GlobalEnvelopeCounterexample.LocalCancellationResults.Theorems` |

`AccuracyTests`, although C0002-unclassified rather than C0002-mixed, also has
an exact fresh role split: `sineTaylorOdd5_abs_error_le_next` and its two
private series helpers form the 3-declaration reusable destination; the four
public `codySine*` declarations and four private Cody helpers form the
8-declaration source destination.

`SampleVariance` routes the seven public generic `flPrefix*` and
`flSampleVarianceUpdate*` bounds plus private helper
`abs_error_add_perturbed_term_rounding` to the reusable destination. The
public `flSampleVarianceTwoPassProblem110Remainder_le_quadratic_bound`
declaration and its private support
`gamma_le_two_mul_nu_of_mul_u_le_half` route together to Problem 1.10. Every
other declaration in that owner is the exact 66-declaration binary32 one-pass
source closure.

`HighamChapter7` routes `eq_7_17_kahan_symbolic_example` and all nine private
`ch7_kahan_*` helpers to Equation 7.17. It routes
`theorem7_5_literal_printed_row_inf_scale_counterexample` and all six private
`theorem7_5_literalRowInfCounterexample_*` helpers to Theorem 7.5.

## Stale-route corrections

`NumStability.Algorithms.Higham726Rump` is unambiguously Chapter 7, Equation
26. It imports the accepted canonical
`NumStability.Source.Higham.Chapter07.Equation26.RumpCycle.Basic`, and all ten
public plus two private residual declarations concern the Equation 7.26 Rump
sign cycle, eigenpair, componentwise distance, and source sandwich. Its only
approved route is
`NumStability.Source.Higham.Chapter07.Equation26.RumpCycle.Results.Theorems`.
`NumStability.Source.Higham.Chapter72` is invalid and is explicitly rejected.

The selected declaration currently nested at
`Chapter06.Theorem05.DistanceToSingularity.Chapter07Equation26` instead moves
to `NumStability.Source.Higham.Chapter07.Equation26.DistanceToSingularity.Results`.
This is a separate Equation 7.26 route, not Chapter 72 and not a child of
Chapter 6.

The Chapter 2 coverage ledger records a historical numbering offset. Therefore:

- `Problem2_17` is a Section 2.6 body claim, not printed Problem 17;
- `Problem2_20` routes to printed Problem 21;
- `Problem2_24` routes to printed Problem 25; and
- `Problem2_27` routes to printed Problem 28.

The existing canonical `Problem25.NonzeroEvaluation.Basic` and
`Problem28.IterativeDivisionTermination.Basic` modules corroborate the last
two corrections. No historical numeric owner is reused as a canonical source
locator.

The frozen broad `Review` proposals are also resolved: `KahanAbsolute` is
Chapter 3 Problem 11, `WilkinsonAttainability` is Chapter 4 Problem 2, and
`HighamChapters1To9SourceClosure` splits exactly between Equation 8.15 and
Equation 8.18. The frozen `AccuracyTests -> Chapter01` proposal is rejected in
favor of reusable Taylor mathematics plus Chapter 2 Section 11 Cody material.
Fresh residual review classifies `Horner` wholly reusable and
`HighamChapter5ComplexAlgorithm51` wholly source-specific after the accepted
W12 basic splits.

## Problem 2.10 outlier decision

`NumStability.Analysis.Problem2_10` is a 1,309,739-byte, 25,596-line source
owner with 1,114 declarations: 956 public and 158 private. Its declarations
form one exhaustive binary64 division-round-trip audit. R03 moves that complete
dependency closure to
`NumStability.Source.Higham.Chapter02.Problem10.DivisionRoundTrip.ExhaustiveBinary64.Results`.
This is an approved semantic outlier exception. An arbitrary line-count split
would multiply private normalization and obscure the single exhaustive audit,
so it is forbidden in this wave.

## Private normalization and compatibility

All 398 selected private declarations relocate. None of the 257 retained
declarations is private; the four retained non-public declarations in
`LegacyChapter11Surface` have `internal` visibility. The declaration-route
artifact must enumerate every private route, and the private-normalization map
must give every exact old mangled name, exact new mangled name, and destination
module. Basename inference is not evidence. The full-graph reverse closure and
post-build format-2 graph must be hash-pinned before activation and acceptance.

Every relocated owner remains as a documented, declaration-free, complete
import-only compatibility wrapper. Public declaration names and signatures are
preserved; no alias declarations are introduced. The two declaration-bearing
umbrellas receive stronger cleanup:

- `NumStability.Analysis.FloatingPointArithmetic` becomes a sorted complete
  import-only aggregate/compatibility facade over its existing reusable and
  source surface plus `IeeeSpecialValueOperations.Results`.
- `NumStability.Source.Higham.Chapter12.IterativeRefinement` moves its 28
  declarations to `Results.Theorems` and becomes a sorted complete import-only
  aggregate over `All` and `Results.Theorems`.

The 11 document-only owners retain every declaration in place. Their only
production change is an honest module docstring; they do not receive aliases,
new declaration modules, or compatibility indirection.

## Selected-owner import DAG and cycle constraints

The exact C0002 selected-owner imports that affect cutover are:

```text
Ch5DerivativeError -> Horner
Ch5SourceClosure -> Horner; FloatingPoint.Model
Higham5FastPolynomialEvaluation -> Horner
Higham726Rump -> HighamChapters1To9SourceClosure
HighamChapter8 -> Chapter08.Section03.TriangularSystems.ArbitraryOrder
Horner -> FloatingPointArithmetic; FloatingPoint.Model
KahanAbsolute -> InstabilityWithoutCancellation
LU.Doolittle -> Doolittle.BackwardError; Doolittle.Basic; Doolittle.Budgets; Doolittle.Certificates; Doolittle.RoundedEntries; FloatingPoint.Model
Doolittle.Budgets -> Doolittle.RoundedEntries; FloatingPoint.Model
Doolittle.Certificates -> Doolittle.Budgets; Doolittle.RoundedEntries; FloatingPoint.Model
WilkinsonAttainability -> Problem2_10
DoubleRounding -> FloatingPointArithmetic
HighamChapter2ElementaryFunctions -> FloatingPointArithmetic
HighamChapter2Lindemann -> FloatingPointArithmetic
HighamChapter7 -> Chapter06.Theorem05.DistanceToSingularity.Chapter07Equation26
Problem2_10 -> DoubleRounding
Problem2_12 -> Problem2_10
Problem2_13 -> Problem2_12
Problem2_14 -> Problem2_13
Problem2_24 -> Problem2_10
Problem2_27 -> Problem2_14
Problem2_3 -> FloatingPointArithmetic
SampleVariance -> FloatingPointArithmetic
Chapter08.Section03.TriangularSystems.ArbitraryOrder -> PivotNormalized; FloatingPoint.Model
Chapter12.IterativeRefinement.Chapter12Bounds -> IterativeRefinement.Core; FloatingPoint.Model
Chapter12.IterativeRefinement.LegacyChapter11Surface -> IterativeRefinement.Core; FloatingPoint.Model
```

Canonical destinations must retarget these edges to canonical destinations or
retained canonical owners. A canonical destination must never import its old
compatibility wrapper. In particular:

- reusable Horner error bounds import reusable floating-point leaves or the new
  reusable IEEE result module, never the old mixed aggregate;
- the new IEEE special-value module imports reusable leaves only and never the
  old `FloatingPointArithmetic` facade or a `Source` module;
- `Doolittle.Assembly.Core` imports canonical Doolittle leaves, while the old
  facade imports `Assembly.Core`, never conversely;
- Problem 2.10 imports the canonical Problem 2.9 result, and Problems 2.12,
  2.13, 2.14, 2.24, and 2.27 follow the canonical dependency chain rather than
  compatibility wrappers;
- the Chapter 7 routes import the corrected Equation 7.26 canonical modules;
  and
- Chapter 12 `Results.Theorems` may import `IterativeRefinement.All`, while the
  old umbrella imports `Results.Theorems`; `Results.Theorems` must not import
  the old umbrella.

Canonical-only tests must fail if an old wrapper is required. Old-only tests
must prove that every historical import still exposes the same public names.

## Destination-prefix vacancy

Each relocated module is a child of one exact fresh directory prefix. Adding
the R03 test and delivery prefixes gives this 50-prefix branch set, sorted by
ordinal path order:

```text
NumStability/Algorithms/LinearSystems/LU/Doolittle/Assembly/
NumStability/Algorithms/PolynomialEvaluation/DerivativeEvaluation/
NumStability/Analysis/Approximation/SineTaylor/OddDegreeFiveError/
NumStability/Analysis/FloatingPointArithmetic/IeeeSpecialValueOperations/
NumStability/Analysis/Statistics/SampleVariance/RoundingErrorBounds/
NumStability/Source/Higham/Chapter01/Problem10/TwoPassSampleVariance/RemainderBound/
NumStability/Source/Higham/Chapter01/Section09/SampleVariance/IeeeSingleOnePassCounterexample/
NumStability/Source/Higham/Chapter01/Section12/InstabilityWithoutCancellation/
NumStability/Source/Higham/Chapter01/Section13/IncreasingPrecision/
NumStability/Source/Higham/Chapter01/Section14/CancellationOfRoundingErrors/
NumStability/Source/Higham/Chapter02/Problem03/AdjacentPrecisionValues/Results/
NumStability/Source/Higham/Chapter02/Problem09/DoubleRounding/Counterexample/
NumStability/Source/Higham/Chapter02/Problem10/DivisionRoundTrip/ExhaustiveBinary64/
NumStability/Source/Higham/Chapter02/Problem12/ReciprocalProduct/Results/
NumStability/Source/Higham/Chapter02/Problem13/ReciprocalProductThreshold/Results/
NumStability/Source/Higham/Chapter02/Problem14/UnitRoundoffProbe/IeeeExamples/
NumStability/Source/Higham/Chapter02/Problem21/HypotenuseNormalization/StandardModelCounterexample/
NumStability/Source/Higham/Chapter02/Problem25/NonzeroEvaluation/IeeeFiniteSystems/
NumStability/Source/Higham/Chapter02/Problem28/IterativeDivisionTermination/UnderflowAwareConvergence/
NumStability/Source/Higham/Chapter02/Section06/Discriminant/FusedMultiplyAdd/Counterexample/
NumStability/Source/Higham/Chapter02/Section06/Discriminant/StandardModel/Counterexample/
NumStability/Source/Higham/Chapter02/Section10/ArctangentRange/Counterexample/
NumStability/Source/Higham/Chapter02/Section10/Tablemaker/FiniteSeparation/Results/
NumStability/Source/Higham/Chapter02/Section11/AccuracyTests/CodySineResults/
NumStability/Source/Higham/Chapter03/Problem11/KahanAbsoluteValue/IeeeDoubleTrace/
NumStability/Source/Higham/Chapter04/Problem02/WilkinsonAttainability/IeeeDoubleTrace/
NumStability/Source/Higham/Chapter05/Algorithm01/ComplexHorner/ErrorBounds/
NumStability/Source/Higham/Chapter05/Section02/BidiagonalDerivativeAnalysis/Results/
NumStability/Source/Higham/Chapter05/Section02/DerivativeError/Results/
NumStability/Source/Higham/Chapter05/Section04/PatersonStockmeyer/Results/
NumStability/Source/Higham/Chapter05/Section05/FastPolynomialEvaluation/Results/
NumStability/Source/Higham/Chapter07/Equation17/
NumStability/Source/Higham/Chapter07/Equation26/DistanceToSingularity/
NumStability/Source/Higham/Chapter07/Equation26/RumpCycle/Results/
NumStability/Source/Higham/Chapter07/LinearSystemsConditioning/Theorem03/
NumStability/Source/Higham/Chapter07/LinearSystemsConditioning/Theorem05/RowInfinityScaleCounterexample/
NumStability/Source/Higham/Chapter08/Equation02/TriangularSubstitution/RelativeInfinityNormBounds/
NumStability/Source/Higham/Chapter08/Equation15/FanInExecutor/
NumStability/Source/Higham/Chapter08/Equation15/GlobalEnvelopeCounterexample/LocalCancellationResults/
NumStability/Source/Higham/Chapter08/Equation18/FanInExecutor/
NumStability/Source/Higham/Chapter08/Problem02/ComparisonMatrixWitness/ArbitraryRatios/
NumStability/Source/Higham/Chapter08/Problem07/DiagonalScaling/Results/
NumStability/Source/Higham/Chapter08/Problem08/SingleEntrySingularity/Results/
NumStability/Source/Higham/Chapter08/Problem09/KahanSingularValues/Results/
NumStability/Source/Higham/Chapter08/Section03/TriangularSystems/ComparisonConditioningResults/
NumStability/Source/Higham/Chapter08/Section03/TriangularSystems/InverseNormResults/
NumStability/Source/Higham/Chapter12/IterativeRefinement/ForwardErrorBounds/
NumStability/Source/Higham/Chapter12/IterativeRefinement/Results/
NumStabilityTest/Reorganization/R03/
docs/architecture/deliveries/R03/
```

The canonical UTF-8 payload is this exact list with LF after every row. It is
3,895 bytes and has SHA-256
`54A191899D91EC5390DB01D5C5D417CEDF1F763324ABD265B039D8FE43D944AF`.
The 48 production-only rows are 3,824 bytes with SHA-256
`87AADE3774C5141C348091B00745E2E6A2D2F15B802B0571967566BEE2278FD1`.

The exact C0002 tree replay reports 0 casefold-occupied prefixes and 0 internal
equal/ancestor intersections. Same-stem existing leaves such as
`Counterexample.lean` do not occupy a new `Counterexample/` directory, and
every destination is below its directory-owned prefix rather than beside it.

Reproduction uses only accepted C0002 data:

```powershell
$base = '9d2334d77f1a38f8a4caa81fe53eeb11a8e3e7cd'
$inventory = Import-Csv -Delimiter ([char]9) -LiteralPath `
  'docs/architecture/phases/2026-08-repository-reorganization-completion/checkpoints/C0002-inventory.tsv'
$selected = @($inventory | Where-Object wave_id -eq 'R03')
if ($selected.Count -ne 47) { throw 'wrong R03 selector size' }
foreach ($row in $selected) {
  $actual = git rev-parse ($base + ':' + $row.path)
  if ($actual -ne $row.base_blob_oid) { throw "blob mismatch: $($row.path)" }
}
$basePaths = @(git ls-tree -r --name-only $base)
# For every exact prefix P above, require no base path equal to P or beginning P + '/'.
# For every pair P,Q, require neither equal to nor an ancestor of the other.
```

This review leaves no semantic route, compatibility behavior, mixed-role split,
numbering correction, private-support placement, or destination-prefix choice
deferred to the worker.
