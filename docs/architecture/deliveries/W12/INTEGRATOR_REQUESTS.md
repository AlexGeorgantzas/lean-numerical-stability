# W12 integrator requests

W12 is not authorized to edit shared or forbidden paths, so each item below is
recorded rather than applied.

## 1. The 17 direct W12-to-W02 imports

`B0003-overlap-review.md` requires the integrator to rewrite these to accepted
W02 canonical leaves after both waves land. W12 preserves them exactly as they
are today and invents no W02 API. They are enumerated here so the rewrite has an
exact worklist.

| W12 owner | imports W02 owner |
| --- | --- |
| `NumStability.Algorithms.HighamChapter5ComplexAlgorithm51` | `NumStability.Analysis.ComplexArithmetic` |
| `NumStability.Algorithms.HighamChapters1To9SourceClosure` | `NumStability.Algorithms.HighamChapter8FanInClosure` |
| `NumStability.Algorithms.HighamChapters1To9SourceClosure` | `NumStability.Algorithms.PriestFiniteFormat` |
| `NumStability.Algorithms.HighamChapters1To9SourceClosure` | `NumStability.Analysis.HighamChapter7` |
| `NumStability.Algorithms.HighamLemma88Entrywise` | `NumStability.Algorithms.HighamChapter8` |
| `NumStability.Algorithms.Horner` | `NumStability.Algorithms.MatMul` |
| `NumStability.Algorithms.KahanAbsolute` | `NumStability.Analysis.DoubleRounding` |
| `NumStability.Analysis.Accumulation` | `NumStability.Analysis.Error` |
| `NumStability.Analysis.AccuracyTests` | `NumStability.Analysis.Nonassociativity` |
| `NumStability.Analysis.AccuracyTests` | `NumStability.Analysis.RoundingProductBounds` |
| `NumStability.Analysis.HighamChapter2FmaDiscriminant` | `NumStability.Analysis.FusedMultiplyAdd` |
| `NumStability.Analysis.Problem2_10` | `NumStability.Analysis.DoubleRounding` |
| `NumStability.Analysis.Problem2_17` | `NumStability.Analysis.Nonassociativity` |
| `NumStability.Analysis.Problem2_18` | `NumStability.Analysis.Nonassociativity` |
| `NumStability.Analysis.Problem2_19` | `NumStability.Analysis.Midpoint` |
| `NumStability.Analysis.Problem2_25` | `NumStability.Analysis.CramersRule` |
| `NumStability.Analysis.Problem2_25` | `NumStability.Analysis.FusedMultiplyAdd` |

All 17 survive in the compatibility modules, which re-state their original
imports. Canonical destinations inherit the same imports minus wave owners, so
the rewrite must cover both the facade and the destinations derived from it.

## 2. Shared Chapter 8 umbrella

The overlap review records that the integrator updates the shared Chapter 8
umbrella after both source families land. W12 contributes five Chapter 8
destinations:

- `NumStability.Source.Higham.Chapter08.Equation10.ColumnPivotedQR.Basic`
- `NumStability.Source.Higham.Chapter08.Equation14.FanInProduct.Basic`
- `NumStability.Source.Higham.Chapter08.Lemma08.Entrywise.Basic`
- `NumStability.Source.Higham.Chapter08.Section03.BidiagonalComparison.Basic`
- `NumStability.Source.Higham.Chapter08.Section04.FanInAsymptotics.Basic`

## 3. Manifests and aggregates W12 may not edit

| file | required change |
| --- | --- |
| `docs/architecture/tiers.json` | classify the 67 new canonical modules; the reusable `NumStability.Algorithms.PolynomialEvaluation.*` leaves are reusable tier, the `Source.Higham.*` leaves are source correspondence |
| `docs/architecture/layout-exceptions.json` | record the 23 declaration-bearing compatibility facades |
| `NumStability/Algorithms.lean`, `NumStability/Analysis.lean` | unchanged: they import the historical paths, which still resolve |
| chapter aggregates under `NumStability/Source.lean` | add the 67 new canonical leaves |
| `NumStabilityTest.lean` | import the 109 focused test modules under `NumStabilityTest/Reorganization/W12/` |

## 4. Residual unclassified debt

23 of the 42 owners remain declaration-bearing facades rather than pure import
shims, because they still define private declarations and their user closures.
They cannot be classified as pure compatibility paths and should stay reviewed
unclassified debt until a later wave promotes or relocates those privates. The
remaining 19 owners are pure import shims.
