# Compilation-outlier review

The older report's timing queue was reviewed together with current import
fan-in and semantic headings. This is an ordered extraction backlog, not a
line-count ranking.

| Module | Fan-in / role | Recommended semantic seams | Current decision |
| --- | --- | --- | --- |
| `Analysis.Norms` | 22 direct consumers; reusable foundation mixed with Higham 6.4 | Vector, duality, basic matrix norms, mixed subordinate norms, interpolation, matrix `Lᵖ`, singular values/operator 2-norm, attainment, conditioning, inverse perturbation; move the ambient-radius source layer beginning near line 23622 | Extract the source tail first; require signature-graph checks before splitting the high-fan-in reusable core. |
| `Algorithms.HighamChapter9` | 18 consumers; 113,808 lines | Sections 9.1–9.6, scaling, posteriori tests, sensitivity, problems, Bohte/rook/Foster | Source tier; split by existing sections after generic block/matrix primitives are extracted. Preserve the old path as an umbrella. |
| `Algorithms.HighamChapter11` | 10 consumers; 137,119 lines | Base, complete pivoting, partial/Bunch–Kaufman, rook, tridiagonal, Aasen, skew, problems | Source tier; sectional split is acyclic. Defer compression of generated tridiagonal/Aasen chains. |
| `Algorithms.LU.BlockLU` | Mixed reusable block algebra and Chapter 13 proof chains | `Basic`, `ErrorModel`, `Factorization`, `FactorizationError`, `SolveError`, diagonal dominance, SPD, Problem 13.4, source chains | First move generic `FirstOrderLe`, max-entry norms, and operation specifications downward; then extract source capstones. |
| `Algorithms.LeastSquares.LSQRSolve` | 13 consumers; mixed reusable LS basics and Chapter 20 | Basic, augmented system/conditioning, normwise error, Wedin, MGS, stored-QR wrappers, row budgets, source closures, forward error | Extract a small reusable basics module first; consolidate Wedin concepts; source closures remain above. |
| `Algorithms.LeastSquares.LSE` | Depends on several broad Higham 19/20 surfaces | Weighted Theorem 20.7, reusable LSE basic/rank/GQR/KKT, Theorems 20.8 and 20.10 | Split LSQR first, then isolate numbered source theorems from reusable LSE/GQR structures. |
| `Analysis.Problem2_10` | Four source-facing consumers; low reuse | Parameterized numeric core versus named source specializations | Reclassify into Higham Chapter 2 now; defer proof compression until parameterized lemmas are designed. |
| `Algorithms.Cholesky.Higham10Theorem10_7Source` | Cohesive 1,633-line source theorem with a broad import | No content split | Moved intact into Higham Chapter 10. A tested `CholeskyFl`-only import failed because five certificate, quadratic-form, and eigenvalue support declarations still live in `HighamChapter10`; extract those first, then narrow this import. |
| `Analysis.InstabilityWithoutCancellation` | Chapter 1 source case study | no-pivot LU, HP48G, exact inverse square, single-precision stagnation | Move to Higham Chapter 1 and split at its existing headings; defer the long generated final chain. |

The dependency order is foundations first: narrow `Norms` and extract generic
vocabulary from `BlockLU`; then split BlockLU, LSQR, and LSE; finally split the
large Chapter 9 and 11 source monoliths. Moving a source monolith first would
preserve the same unwanted low-level dependencies under a cleaner pathname.
