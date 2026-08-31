# Compilation-outlier review

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

## Superseding dispositions (2026-08-30)

Audited at revision `cca0621da6c2b0f19836aec67aa736ef9a06a838` (main, after
the R0014/R0015 integration). Every module still queued above has since been
canonicalized under the repository reorganization: each historical path now
survives as a declaration-free, import-only module classified in the
`compatibility` tier of `docs/architecture/tiers.json`, with its canonical
owners recorded in `docs/architecture/COMPATIBILITY.md` and its forwarding
contract enforced by `tools/architecture/check_compatibility.py`, which also
verifies that production code contains zero imports of these historical
paths. Verified live at the audited revision:

- `Algorithms.HighamChapter9`: 16-line import umbrella over the ten
  canonical `Source.Higham.Chapter09` section/problem modules.
- `Algorithms.HighamChapter11`: 12-line import wrapper over the eight
  canonical `Source.Higham.Chapter11` section/problem modules.
- `Algorithms.LeastSquares.LSQRSolve`: 44-line import-only wrapper whose
  declarations moved unchanged to canonical
  `Algorithms.LinearSystems.LeastSquares`/`QR`/`Triangular`,
  `Analysis.Perturbation.LeastSquares`, and
  `Source.Higham.Chapter20.Theorem03` owners.
- `Algorithms.LeastSquares.LSE`: 34-line import-only wrapper over the
  canonical `Algorithms.LinearSystems.LeastSquares.Equality`,
  `Analysis.Perturbation.LeastSquares.Equality`, and
  `Source.Higham.Chapter20.Theorem08.LSE` owners.
- `Analysis.Problem2_10`: 20-line import-only wrapper (retained by wave
  R03) over the canonical `Source.Higham.Chapter02` Problem09/Problem10
  owners.
- `Algorithms.Cholesky.Higham10Theorem10_7Source`: 8-line import wrapper
  over the canonical `Source.Higham.Chapter10.Theorem07` owner.
- `Analysis.InstabilityWithoutCancellation`: 27-line import-only wrapper
  (retained by wave R03) over the canonical `Source.Higham.Chapter01`
  owners.

This section supersedes the remaining "Current decision" rows and the
closing dependency-order paragraph, including the present-tense plan to
split LSQR and LSE next: those splits and the Chapter 9 and 11 monolith
splits are done, and no open extraction queue remains from this review. The
original table and paragraph are retained verbatim above as immutable review
history.
