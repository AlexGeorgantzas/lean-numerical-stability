# W11 declaration routing

W11 routes exactly the declarations selected by `B0010` and `W11.tsv`.  The
declaration ledger is `DECLARATION_ROUTES.tsv`; this document summarizes that
ledger without broadening its authority.

## Exact totals

| Disposition | Reusable | Source-specific | Compatibility retention | Total |
| --- | ---: | ---: | ---: | ---: |
| Relocated | 2,322 | 807 | 0 | 3,129 |
| Retained for private reverse closure | 0 | 0 | 225 | 225 |
| **Total** | **2,322** | **807** | **225** | **3,354** |

The selected declarations comprise 2,469 theorems, 813 definitions, 24
inductives, 24 constructors, and 24 recursors.  There are 3,351 public and
three private declarations.  All declaration names, namespaces, kinds,
visibility, statements, proofs, generated families, attributes, section
context, options, local instances, and ambient imports are preserved.

## Historical owners

`NumStability.Algorithms.RandNLA` remains an import-only umbrella over the 17
physical owners below.

| Physical owner | Selected | Retained | Reusable | Source |
| --- | ---: | ---: | ---: | ---: |
| `ElementwiseSampling` | 84 | 0 | 82 | 2 |
| `ElementwiseSpectral` | 308 | 17 | 91 | 200 |
| `ElementwiseTraceMGF` | 11 | 0 | 1 | 10 |
| `HitCountConcentration` | 95 | 3 | 55 | 37 |
| `LeastSquaresSketch` | 140 | 8 | 75 | 57 |
| `LowRankApprox` | 805 | 0 | 466 | 339 |
| `Preconditioning` | 1,179 | 66 | 1,082 | 31 |
| `RowSampling` | 77 | 0 | 73 | 4 |
| `RowSamplingGram` | 96 | 23 | 69 | 4 |
| `RowSamplingLeverage` | 20 | 2 | 15 | 3 |
| `RowSamplingLeverageComputedBasis` | 43 | 0 | 36 | 7 |
| `RowSamplingLeverageMGF` | 32 | 0 | 12 | 20 |
| `RowSamplingTraceMGF` | 11 | 0 | 1 | 10 |
| `UniformRowSampling` | 33 | 10 | 22 | 1 |
| `UniformRowSamplingComposition` | 11 | 1 | 6 | 4 |
| `UniformRowSamplingFP` | 377 | 95 | 204 | 78 |
| `UniformRowSamplingMGF` | 32 | 0 | 32 | 0 |

Nine historical owners remain declaration-bearing because they contain the
private reverse closure; the other eight are pure import shims.  Every facade
directly imports every canonical module receiving one of its declarations.

## Reusable destinations

The 2,322 reusable declarations are routed to these 19 reviewed B0010
destinations:

- `Concentration.HitCounts.Bounds` (55)
- `Concentration.SpectralTransfer.Elementwise` (91)
- `Concentration.TraceMGF.Elementwise` (1)
- `Concentration.TraceMGF.LeverageScore` (12)
- `Concentration.TraceMGF.RowNorm` (1)
- `Concentration.TraceMGF.UniformRows` (32)
- `LeastSquaresSketching.Objectives.Core` (72)
- `LeastSquaresSketching.RowSampling.Core` (3)
- `LowRankApproximation.ColumnSketches.Core` (301)
- `LowRankApproximation.RankFactorizations.Core` (165)
- `Preconditioning.ExactTransforms.Core` (1,082)
- `Preconditioning.ExactTransforms.UniformRowComposition` (6)
- `Sampling.Elementwise.Core` (82)
- `Sampling.LeverageScore.ComputedBasis` (36)
- `Sampling.LeverageScore.Core` (15)
- `Sampling.RowNorm.Core` (73)
- `Sampling.RowNorm.Gram` (69)
- `Sampling.UniformRows.Core` (22)
- `Sampling.UniformRows.FloatingPoint` (204)

Every module above is below
`NumStability.Algorithms.RandomizedLinearAlgebra`.  The canonical import graph
is acyclic, resolves completely, and has zero transitive paths to
`NumStability.Source` or to a historical W11 facade.

The initially reviewed semantic subcategories in preconditioning,
least-squares sketching, and low-rank approximation contain typed strongly
connected components.  Commands in each component were therefore coalesced
into the smallest B0010-approved acyclic modules rather than cutting a typed
edge or fabricating an API.  In particular, exact preconditioning transforms
coalesce in `ExactTransforms.Core`; the mutually dependent least-squares
objective commands coalesce in `Objectives.Core`; and low-rank commands split
only at the acyclic `RankFactorizations.Core` / `ColumnSketches.Core` boundary.

## Reviewed source destinations

The 807 source-specific declarations are routed declaration-by-declaration to
these 18 exact Drineas--Mahoney endpoints:

- Algorithm 01: `ElementwiseSampling.Sampling` (2),
  `ElementwiseSampling.TraceMGF` (10), and
  `ElementwiseSampling.HitCountConcentration` (37)
- Algorithm 02: `RowSampling.Endpoints` (3)
- Algorithm 03: `RandomProjectionPreconditioning.UniformRows` (1),
  `UniformRowComposition` (4), `Preconditioning` (31), and
  `FloatingPoint` (78)
- Equation 02: `SpectralApproximation.ElementwiseSpectral` (200)
- Equation 04: `RowSamplingProbability.Normalization` (1)
- Equation 05: `GramApproximation.Bounds` (4)
- Equation 06: `LeverageProbability.Normalization` (1)
- Equation 07: `SubspaceEmbedding.Leverage` (2), `ComputedBasis` (7),
  `RowNormTraceMGF` (10), and `LeverageTraceMGF` (20)
- Equation 08: `LeastSquaresSketch.Endpoints` (57)
- Equation 09: `LowRankApproximation.Endpoints` (339)

This separation is declaration-level for both `ElementwiseSpectral` and
`LowRankApprox`: generic spectral/low-rank APIs are reusable, while numbered
equations, algorithm correspondence, and source certificates live only under
the reviewed source prefix.

## Dependency handling

`LeastSquaresSketch.Endpoints` retains the accepted
`Source.Higham.Chapter20.Theorem03.QRSolve` dependency because the retained
Equation 08 solver closure has no accepted canonical replacement.  No reusable
W11 module imports Chapter 20.

All four W11 low-rank surfaces (the two canonical destinations, Equation 09,
and the historical facade) import exactly these three C0006 modules:

- `Algorithms.MatrixInversion.LUFactors.ErrorAnalysis.MatrixInversion`
- `Algorithms.MatrixInversion.LUFactors.Methods.MatrixInversion`
- `Algorithms.MatrixInversion.Residuals.MatrixInversion`

The historical `NumStability.Algorithms.MatrixInversion` umbrella is not
restored anywhere in W11.
