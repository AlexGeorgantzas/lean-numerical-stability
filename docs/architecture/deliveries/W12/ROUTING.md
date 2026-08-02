# W12 declaration routing table

Wave `W12`, branch `codex/reorg-2026-08-w12-ch01-ch02-ch05`, base
`e6ef0107edb873f7a05ad8282df7efdf41a986d3` (checkpoint `C0002`).

Every one of the 4,197 declarations selected by `W12.tsv` appears in exactly one
row below. A row whose destination equals the owner is a *retained* declaration:
it stays in the historical module. Retention is inside the projection contract --
`P0003` lists all 42 owners under `--allow-module`, so a retained declaration keeps
its name, kind, visibility and every incident edge.

## Why 1,550 declarations are retained

Lean mangles a private declaration to `_private.<defining module>.<n>.<name>`.
The defining module is part of the name, so relocating a private renames it and
every incident edge is reported missing against the frozen graph. W12 selects 257
private declarations. Anything referring to one must stay with it, in two steps:

* a same-module user cannot see the private from anywhere else, so it is retained;
* a *different*-owner user would force its canonical destination to import the
  owner's compatibility facade, inverting the architecture the strict-source gate
  enforces, so it is retained too (58 declarations).

The closure fixes 1,550 of 4,197 declarations (36.9%). The remaining 2,647 relocate.

## Per-owner routing

### `NumStability.Algorithms.Ch5DerivativeError`

13 declarations selected; 4 retained, 9 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter05.Section02.DerivativeError.Basic` | 9 |
| `NumStability.Algorithms.Ch5DerivativeError` *(retained)* | 4 |

### `NumStability.Algorithms.Ch5LejaProducer`

25 declarations selected; 0 retained, 25 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter05.Problem04.LejaOrdering.Basic` | 25 |

### `NumStability.Algorithms.Ch5NewtonForm`

29 declarations selected; 0 retained, 29 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter05.Section03.NewtonEvaluation.Basic` | 29 |

### `NumStability.Algorithms.Ch5SourceClosure`

48 declarations selected; 16 retained, 32 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter05.Section02.BidiagonalDerivativeAnalysis.Basic` | 26 |
| `NumStability.Algorithms.Ch5SourceClosure` *(retained)* | 16 |
| `NumStability.Source.Higham.Chapter05.Section03.ResidualUnwind.Basic` | 6 |

### `NumStability.Algorithms.Higham5FastPolynomialEvaluation`

40 declarations selected; 4 retained, 36 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter05.Section05.FastPolynomialEvaluation.Basic` | 36 |
| `NumStability.Algorithms.Higham5FastPolynomialEvaluation` *(retained)* | 4 |

### `NumStability.Algorithms.Higham5PatersonStockmeyer`

28 declarations selected; 6 retained, 22 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter05.Section04.PatersonStockmeyer.Basic` | 22 |
| `NumStability.Algorithms.Higham5PatersonStockmeyer` *(retained)* | 6 |

### `NumStability.Algorithms.Higham726Rump`

56 declarations selected; 12 retained, 44 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter07.Equation26.RumpCycle.Basic` | 44 |
| `NumStability.Algorithms.Higham726Rump` *(retained)* | 12 |

### `NumStability.Algorithms.HighamChapter5ComplexAlgorithm51`

26 declarations selected; 8 retained, 18 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter05.Algorithm01.ComplexHorner.Basic` | 18 |
| `NumStability.Algorithms.HighamChapter5ComplexAlgorithm51` *(retained)* | 8 |

### `NumStability.Algorithms.HighamChapters1To9SourceClosure`

152 declarations selected; 3 retained, 149 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter04.Algorithm03.SourceClosure.Basic` | 41 |
| `NumStability.Source.Higham.Chapter07.Corollary06.Equilibration.Basic` | 32 |
| `NumStability.Source.Higham.Chapter07.Equation26.ComponentwiseDistance.Basic` | 32 |
| `NumStability.Source.Higham.Chapter07.Equation25.SourceEndpoint.Basic` | 17 |
| `NumStability.Source.Higham.Chapter08.Equation14.FanInProduct.Basic` | 10 |
| `NumStability.Source.Higham.Chapter08.Section03.BidiagonalComparison.Basic` | 5 |
| `NumStability.Source.Higham.Chapter08.Section04.FanInAsymptotics.Basic` | 5 |
| `NumStability.Algorithms.HighamChapters1To9SourceClosure` *(retained)* | 3 |
| `NumStability.Source.Higham.Chapter09.Theorem15.Sun.Basic` | 3 |
| `NumStability.Source.Higham.Chapter08.Equation10.ColumnPivotedQR.Basic` | 2 |
| `NumStability.Source.Higham.Chapter09.Theorem15.Barrlund.Basic` | 2 |

### `NumStability.Algorithms.HighamLemma88Entrywise`

4 declarations selected; 0 retained, 4 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter08.Lemma08.Entrywise.Basic` | 4 |

### `NumStability.Algorithms.Horner`

424 declarations selected; 6 retained, 418 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter05.Section03.DividedDifferences.Basic` | 89 |
| `NumStability.Source.Higham.Chapter05.Section01.Horner.Basic` | 85 |
| `NumStability.Source.Higham.Chapter05.Problem06.MatrixPolynomialHorner.Basic` | 74 |
| `NumStability.Source.Higham.Chapter05.Problem01.DifferentiatedHorner.Basic` | 62 |
| `NumStability.Source.Higham.Chapter05.Section02.DerivativeEvaluation.SyntheticDivision` | 27 |
| `NumStability.Algorithms.PolynomialEvaluation.MatrixNorms` | 14 |
| `NumStability.Source.Higham.Chapter05.Problem02.PowerBuilding.Basic` | 13 |
| `NumStability.Source.Higham.Chapter05.Section03.LejaOrdering.Basic` | 11 |
| `NumStability.Source.Higham.Chapter05.Equation14.MatrixPolynomialForms.Basic` | 10 |
| `NumStability.Source.Higham.Chapter05.Problem03.EvenOddSplitting.Basic` | 8 |
| `NumStability.Algorithms.Horner` *(retained)* | 6 |
| `NumStability.Source.Higham.Chapter05.Section02.DerivativeEvaluation.Bidiagonal` | 6 |
| `NumStability.Algorithms.PolynomialEvaluation.RootProduct` | 5 |
| `NumStability.Source.Higham.Chapter05.Section01.RelativeError.Basic` | 5 |
| `NumStability.Source.Higham.Chapter05.Section03.NewtonEvaluation.HornerBasis` | 5 |
| `NumStability.Algorithms.PolynomialEvaluation.ElementaryErrorBounds` | 4 |

### `NumStability.Algorithms.KahanAbsolute`

206 declarations selected; 123 retained, 83 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Algorithms.KahanAbsolute` *(retained)* | 123 |
| `NumStability.Source.Higham.Chapter03.Problem11.KahanAbsoluteValue.Basic` | 83 |

### `NumStability.Algorithms.OrderingExamples`

333 declarations selected; 0 retained, 333 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter04.Equation05.OrderingExamples.Basic` | 333 |

### `NumStability.Algorithms.WilkinsonAttainability`

68 declarations selected; 26 retained, 42 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter04.Problem02.WilkinsonAttainability.Basic` | 42 |
| `NumStability.Algorithms.WilkinsonAttainability` *(retained)* | 26 |

### `NumStability.Analysis.Accumulation`

45 declarations selected; 0 retained, 45 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter01.Section11.Accumulation.Basic` | 38 |
| `NumStability.Source.Higham.Chapter01.Problem05.CompensatedLogarithm.Basic` | 7 |

### `NumStability.Analysis.AccuracyTests`

54 declarations selected; 11 retained, 43 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Section11.AccuracyTests.Basic` | 43 |
| `NumStability.Analysis.AccuracyTests` *(retained)* | 11 |

### `NumStability.Analysis.CalculatorWords`

50 declarations selected; 0 retained, 50 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter01.Problem06.CalculatorWords.Basic` | 50 |

### `NumStability.Analysis.Counting`

25 declarations selected; 0 retained, 25 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Problem01.FloatingPointCounts.Basic` | 25 |

### `NumStability.Analysis.HighamChapter2ElementaryFunctions`

12 declarations selected; 7 retained, 5 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Analysis.HighamChapter2ElementaryFunctions` *(retained)* | 7 |
| `NumStability.Source.Higham.Chapter02.Section10.ArctangentRange.Basic` | 5 |

### `NumStability.Analysis.HighamChapter2FmaDiscriminant`

16 declarations selected; 10 retained, 6 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Analysis.HighamChapter2FmaDiscriminant` *(retained)* | 10 |
| `NumStability.Source.Higham.Chapter02.Section06.Discriminant.FusedMultiplyAdd.Basic` | 6 |

### `NumStability.Analysis.HighamChapter2GradualUnderflowExact`

6 declarations selected; 0 retained, 6 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Problem19.GradualUnderflowExactness.Basic` | 6 |

### `NumStability.Analysis.HighamChapter2Lindemann`

15 declarations selected; 4 retained, 11 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Section10.Tablemaker.HermiteLindemann.Basic` | 11 |
| `NumStability.Analysis.HighamChapter2Lindemann` *(retained)* | 4 |

### `NumStability.Analysis.HighamChapter2Tablemaker`

8 declarations selected; 0 retained, 8 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Section10.Tablemaker.FiniteSeparation.Basic` | 8 |

### `NumStability.Analysis.MullerRecurrence`

32 declarations selected; 0 retained, 32 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter01.Problem08.MullerRecurrence.Basic` | 32 |

### `NumStability.Analysis.NearInteger`

21 declarations selected; 0 retained, 21 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter01.Problem02.NearIntegerTable.Basic` | 21 |

### `NumStability.Analysis.Problem2_10`

1705 declarations selected; 1114 retained, 591 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Analysis.Problem2_10` *(retained)* | 1114 |
| `NumStability.Source.Higham.Chapter02.Problem10.DivisionRoundTrip.Basic` | 591 |

### `NumStability.Analysis.Problem2_12`

16 declarations selected; 8 retained, 8 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Analysis.Problem2_12` *(retained)* | 8 |
| `NumStability.Source.Higham.Chapter02.Problem12.ReciprocalProduct.Basic` | 8 |

### `NumStability.Analysis.Problem2_13`

114 declarations selected; 72 retained, 42 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Analysis.Problem2_13` *(retained)* | 72 |
| `NumStability.Source.Higham.Chapter02.Problem13.ReciprocalProductThreshold.Basic` | 42 |

### `NumStability.Analysis.Problem2_14`

22 declarations selected; 20 retained, 2 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Analysis.Problem2_14` *(retained)* | 20 |
| `NumStability.Source.Higham.Chapter02.Problem14.UnitRoundoffProbe.Basic` | 2 |

### `NumStability.Analysis.Problem2_15_16`

92 declarations selected; 0 retained, 92 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Problems15And16.SpecialValueProbes.Basic` | 92 |

### `NumStability.Analysis.Problem2_17`

11 declarations selected; 6 retained, 5 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Analysis.Problem2_17` *(retained)* | 6 |
| `NumStability.Source.Higham.Chapter02.Section06.Discriminant.StandardModel.Basic` | 5 |

### `NumStability.Analysis.Problem2_18`

8 declarations selected; 0 retained, 8 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Problem18.ExactSubtractionCounterexample.Basic` | 8 |

### `NumStability.Analysis.Problem2_19`

6 declarations selected; 0 retained, 6 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Problem20.SquareRootIdentities.Basic` | 6 |

### `NumStability.Analysis.Problem2_20`

31 declarations selected; 5 retained, 26 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Problem21.HypotenuseNormalization.Basic` | 26 |
| `NumStability.Analysis.Problem2_20` *(retained)* | 5 |

### `NumStability.Analysis.Problem2_23`

13 declarations selected; 0 retained, 13 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Problem24.GuardDigitCancellation.Basic` | 13 |

### `NumStability.Analysis.Problem2_24`

218 declarations selected; 30 retained, 188 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Problem25.NonzeroEvaluation.Basic` | 188 |
| `NumStability.Analysis.Problem2_24` *(retained)* | 30 |

### `NumStability.Analysis.Problem2_25`

20 declarations selected; 0 retained, 20 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Problem27.KahanDeterminant.Basic` | 20 |

### `NumStability.Analysis.Problem2_26`

56 declarations selected; 0 retained, 56 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Section06.ReciprocalIteration.Basic` | 56 |

### `NumStability.Analysis.Problem2_27`

26 declarations selected; 14 retained, 12 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Analysis.Problem2_27` *(retained)* | 14 |
| `NumStability.Source.Higham.Chapter02.Problem28.IterativeDivisionTermination.Basic` | 12 |

### `NumStability.Analysis.Problem2_3`

104 declarations selected; 41 retained, 63 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Problem03.AdjacentPrecisionValues.Basic` | 63 |
| `NumStability.Analysis.Problem2_3` *(retained)* | 41 |

### `NumStability.Analysis.Problem2_5`

6 declarations selected; 0 retained, 6 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Problem05.BinaryOneTenth.Basic` | 6 |

### `NumStability.Analysis.Problem2_6`

13 declarations selected; 0 retained, 13 relocated.

| destination | declarations |
| --- | ---: |
| `NumStability.Source.Higham.Chapter02.Problem06.IntegerRepresentability.Basic` | 13 |

## Totals

| | declarations |
| --- | ---: |
| selected by `W12.tsv` | 4197 |
| relocated to canonical destinations | 2647 |
| retained in the historical module | 1550 |
| canonical destination modules written | 67 |
| destination roots in `B0003` covered | 63 / 63 |
