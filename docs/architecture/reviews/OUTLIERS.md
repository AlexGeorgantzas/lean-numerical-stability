# Compilation-outlier review

## Current C0007 review queue

At audited revision `8960f2a980be22166f321c4ba452eb547529b1fd`, the
current review threshold finds 22 modules above 10,000 nonblank lines and nine
directories above the direct-child fanout threshold. Seventeen modules have a
planned semantic split or source extraction; five require comparable isolated
clean/warm profiles and human review before any retain or split decision. No
retain exception is approved. The family names below are provisional routing
owners, not substitutes for an accountable principal and distinct reviewer.

| Module or group | Current disposition | Provisional mathematical owner |
| --- | --- | --- |
| `Source.Higham.Chapter11.Section01.Tridiagonal` | Split by pivot, step, update, execution, and error seams | Chapter 11 symmetric-indefinite factorization |
| `Analysis.Perturbation.LeastSquares.Equality.RowwiseBackwardError` | Split and move numbered source claims | Chapter 20 Theorem 07; Analysis wrapper retained |
| `Source.Higham.Chapter11.Section02.Aasen` | Split specification, recurrences, execution, growth, solve, and error | Chapter 11 symmetric-indefinite factorization |
| `Source.Higham.Chapter09.Section11` | Split numbered results and generic/source boundary | Chapter 9 Section 11 |
| `Source.Higham.Chapter19.Core` | Split after the two retained compatibility imports are removed | Chapter 19 QR |
| `Source.Higham.Chapter11.Section01.PartialPivoting` | Split pivot, update, factorization, rounded-error, and backward-error seams | Chapter 11 symmetric-indefinite factorization |
| `Source.Higham.Chapter09.Problems` | Split by numbered problem | Chapter 9 problems |
| `Source.Higham.Chapter20.Theorem03.QRSolve` | Split normal equations, inverse action, QR execution/error, and residual quality | Chapter 20 Theorem 03 |
| `Analysis.Perturbation.LeastSquares.Equality.Perturbation` | Split reusable definitions from numbered source claims | Least-squares analysis and Chapter 20 |
| `Analysis.Perturbation.LeastSquares.Basic` | Split definitions, normal equations, augmented system, conditioning, and refinement | Reusable least-squares analysis |
| `Algorithms.RandomizedLinearAlgebra.Preconditioning.ExactTransforms.Core` | Split exact certificates, vector/matrix embeddings, and composition | Reusable randomized linear algebra |
| `Source.Higham.Chapter01.FloatingPointArithmetic.InstabilityWithoutCancellation` | Split by the four existing case studies | Chapter 1 floating-point arithmetic |
| `Source.Higham.Chapter09.Section06` | Split numbered theorem, growth, and special-matrix material | Chapter 9 Section 06 |
| `Analysis.Perturbation.LeastSquares.Equality.MixedStability` | Move numbered claims and retain an Analysis wrapper | Chapter 20 Theorem 10 |
| `Source.DrineasMahoney.RandNLA2016.Equation09.LowRankApproximation.Endpoints` | Split norm API, SVD-tail certificates, and residual results | RandNLA Equation 09 |
| `Source.DrineasMahoney.RandNLA2016.Equation02.SpectralApproximation.ElementwiseSpectral` | Split prerequisites, transfer, and final probability results | RandNLA Equation 02 |
| `Algorithms.LinearSystems.LeastSquares.Equality.Basic` | Extract generic primitives and move Chapter 20/21 claims | Reusable least squares plus Chapters 20/21 |
| `Source.Higham.Chapter02.Problem10.DivisionRoundTrip.ExhaustiveBinary64.Results` | Profile and human review; no retain decision | Chapter 2 Problem 10 |
| `Analysis.Perturbation.LeastSquares.BackwardError` | Profile and human review; no retain decision | Reusable least-squares analysis |
| `Analysis.FloatingPointArithmetic.RoundToEvenLocalError` | Profile and human review; no retain decision | Reusable floating-point analysis |
| `Source.DrineasMahoney.RandNLA2016.Equation08.LeastSquaresSketch.Endpoints` | Profile and human review; no retain decision | RandNLA Equation 08 |
| `Analysis.MatrixAlgebra` | Profile and human review; no retain decision | Reusable analysis foundations |

The current fanout queue is `Algorithms` (183 direct files/23
declaration-bearing), `Analysis` (147/26), `Algorithms/Cholesky` (82/4),
`Algorithms/TestMatrices` (76/1), `Source/Higham/Chapter11` (60/27),
`Algorithms/QR` (59/0), `Algorithms/LeastSquares` (42/0),
`Source/Higham/Chapter13` (36/23), and `Algorithms/Underdetermined` (32/0).
Compatibility graveyards are provisionally retained to a declared breaking
release at those exact ceilings; Chapter 11 requires owner routing; and the
Algorithms, Analysis, and Chapter 13 fanouts require profile-backed human
dispositions. Any increase reopens review.

## Archived pre-C0007 outlier review

The table and dependency order below are retained as superseded design
evidence. In particular, its LSQR/LSE “next” language is not a current queue.

The older report's timing queue was reviewed together with current import
fan-in and semantic headings. This is an ordered extraction backlog, not a
line-count ranking.

| Module | Fan-in / role | Recommended semantic seams | Current decision |
| --- | --- | --- | --- |
| `Analysis.Norms.Core` | **Resolved in Phase 11B1:** declaration-free reusable aggregate; only the historical `Analysis.Norms` facade imports it directly in production | `Asymptotics`, `LinearOperators`, `OperatorNorms`, `VectorNorms`, `MatrixNorms`, `SingularValues`, and `Conditioning`; Problems 6.1/6.5/6.9/6.10 under `Source.Higham.Chapter06` | The manifest-checked split preserves all 1,783 constants across 20 reusable and four source owners. Core is classified as an aggregate and removed from the unclassified queue. Phase 11B2 separately preserves the other 69 audited Chapter 6 constants across nine source leaves; their four former owners are exact wrappers. |
| `Algorithms.HighamChapter9` | 18 consumers; 113,808 lines | Sections 9.1–9.6, scaling, posteriori tests, sensitivity, problems, Bohte/rook/Foster | Source tier; split by existing sections after generic block/matrix primitives are extracted. Preserve the old path as an umbrella. |
| `Algorithms.HighamChapter11` | 10 consumers; 137,119 lines | Base, complete pivoting, partial/Bunch–Kaufman, rook, tridiagonal, Aasen, skew, problems | Source tier; sectional split is acyclic. Defer compression of generated tridiagonal/Aasen chains. |
| `Algorithms.LU.BlockLU` | **Resolved in Phase 12:** declaration-free two-target compatibility facade; all ten declaration-bearing siblings are also wrappers | Fifteen declaration-bearing reusable leaves plus the `VaryingBlocks` subaggregate over five leaves, and an exact 82-member Chapter 13 source aggregate | The monolith contract preserves 1,990 declarations across its semantic owners; the sibling contract preserves another 287 across 22 follow-on destinations. |
| `Algorithms.LeastSquares.LSQRSolve` | 13 consumers; mixed reusable LS basics and Chapter 20 | Basic, augmented system/conditioning, normwise error, Wedin, MGS, stored-QR wrappers, row budgets, source closures, forward error | Extract a small reusable basics module first; consolidate Wedin concepts; source closures remain above. |
| `Algorithms.LeastSquares.LSE` | Depends on several broad Higham 19/20 surfaces | Weighted Theorem 20.7, reusable LSE basic/rank/GQR/KKT, Theorems 20.8 and 20.10 | Split LSQR first, then isolate numbered source theorems from reusable LSE/GQR structures. |
| `Analysis.Problem2_10` | Four source-facing consumers; low reuse | Parameterized numeric core versus named source specializations | Reclassify into Higham Chapter 2 now; defer proof compression until parameterized lemmas are designed. |
| `Algorithms.Cholesky.Higham10Theorem10_7Source` | Cohesive 1,633-line source theorem with a broad import | No content split | Moved intact into Higham Chapter 10. A tested `CholeskyFl`-only import failed because five certificate, quadratic-form, and eigenvalue support declarations still live in `HighamChapter10`; extract those first, then narrow this import. |
| `Analysis.InstabilityWithoutCancellation` | Chapter 1 source case study | no-pivot LU, HP48G, exact inverse square, single-precision stagnation | Move to Higham Chapter 1 and split at its existing headings; defer the long generated final chain. |

The dependency order remains foundations first. The `Norms.Core`, Chapter 6,
historical BlockLU-owner, and ten-module BlockLU sibling splits are complete.
Next split LSQR and LSE; finally split the large Chapter 9 and 11 source
monoliths. Moving a source monolith first would
preserve the same unwanted low-level dependencies under a cleaner pathname.
