# Higham Split 4 Formalization Report

## Scope and audit basis

Split 4 owns Chapters 20-28 of Nicholas J. Higham, *Accuracy and Stability of
Numerical Algorithms*, second edition, together with Appendix A solution rows
whose labels begin `20.x` through `28.x`. The audit used the chapter PDFs and
Appendix PDF under `References/`, the complete Problems sections, rendered
checks of formula-heavy pages, and the repository chapter-formalization skill
in core mode.

The local skill formerly described the assignment as Chapter 20 only. It now
states the full Chapters 20-28 plus Appendix A partition in both maintained
skill copies. The shared planning ledgers remain authoritative for exact source
labels and were corrected when visual inspection disagreed with them.

## Per-chapter selected-scope result

The aggregate selected-scope gate is **FAIL**. Chapters 20, 22, 23, 24, 25,
and 28 retain selected nonterminal rows. Terminal
citation-dependent or implementation-facing rows use visible
explicit domains whose hypotheses are upstream identities, local operation
budgets, law properties, or remainder estimates and whose nonvacuity is
demonstrated where practical; target-bearing certificates are not counted as
closure.

| Chapter | Gate | Principal local result | Remaining selected-scope boundary |
|---|---|---|---|
| 20, least squares | **FAIL** | Theorem 20.4's actual QR/RHS/two-solve total perturbations and common witness; Theorem 20.7's literal pivoted QR/RHS/back-substitution producer with pivot-position `(j+1)^2` | The precise p. 395 row-sorting cap for `alpha_i`/`beta_i` and invariance of `phi` lack an executable row-order producer and proof |
| 21, underdetermined systems | **PASS** | Previously completed and re-audited source-facing theory, algorithms, and explicit-domain rounded results | No selected row open; documented source corrections and domains remain visible |
| 22, Vandermonde systems | **FAIL** | Literal Algorithms 22.1-22.3 loop/state definitions, symbolic/table/confluent algebra, and several exact recurrence and refinement results | Table 22.1 V1-V6, the Stage-I interpolation/factor-product/final-solve route, rounded factor perturbations, Theorems 22.4/22.6, Corollaries 22.5/22.7, and Problem 22.8 remain open |
| 23, fast matrix multiplication | **FAIL** | Actual rounded conventional and one-level 3M paths, exact one-level Strassen/Winograd algebra, operation counts, and scalar coefficient recurrences | Miller's (23.11), recursively rounded Strassen/Winograd/Bini-Lotti error inductions, and the combined 3M-Strassen Problem 23.6 endpoint remain open |
| 24, FFT and applications | **FAIL** | Literal Theorems 24.1-24.2; complete (24.3)-(24.7); actual rounded forward FFTs, diagonal division, inverse FFT, and composed four-stage solver; exact (24.8); backward-stability transfer | Theorem 24.3's structured generator/RHS perturbation split and first-order reduction have not been derived from the actual four-stage execution |
| 25, nonlinear systems | **FAIL** | Newton/error predicates; literal feasible (25.11) supremum and Taylor-to-limit theorem from a genuine derivative; literal rounded (25.13); stopping algebra; Problem 25.1 | The source-facing implicit-function producer of the local unique solution map and derivative `-F_x⁻¹ F_d` for (25.11) remains open |
| 26, automatic error analysis | **PASS** | General MDS best-vertex/reorder, reflection, expansion, contraction/retry, and finite run semantics plus stopping/cubic foundations and concrete finite directed-rounding producers for `+`, `-`, `*`, and `/` | No selected row open; MDS assumes no optimizer correctness or termination, while empirical examples remain correctly skipped |
| 27, software issues | **PASS** | Exact/rounded two-pass scaled norm, Smith division branch safety, and explicit source-range audit including the overbroad universal claim's counterexample | No selected row open; Blue's underspecified prose is terminal deferred |
| 28, test matrices | **FAIL** | Exact Hilbert/Pascal/Green-inverse algebra; normalized Gaussian/Stewart producer; all-orders Pascal cube and singular-kernel proofs; symmetric Toeplitz DST diagonalization; companion eigenvector, left Krylov basis, scalar-shift rank bound, and exact Gram identity | Hilbert/Cauchy total positivity and asymptotics, Ginibre/Perron and Stewart-Haar producers, randsvd prescribed-spectrum/condition, rank-2, and symmetric-adaptation claims, Pascal moment/palindromic/spectral/optimality/sign-change claims, general Toeplitz spectrum/asymptotic, and companion characteristic/eigenvalue/similarity/SVD endpoints remain open; the printed complex companion-normality iff is a source discrepancy, while undefined `approx`, cost, and LU-convergence rows are terminal deferred |

The source-order count audit is:

| Chapter | Named results | Numbered equations | Problems | Appendix A rows |
|---|---:|---:|---:|---:|
| 20 | 12 | 36 | 13 | 11 |
| 21 | 4 | 11 | 1 | 1 |
| 22 | 8 | 26 | 11 | 7 |
| 23 | 4 | 25 | 10 | 6 |
| 24 | 3 | 8 | 1 | 0 |
| 25 | 2 | 14 | 2 | 1 |
| 26 | 0 | 8 | 4 | 1 |
| 27 | 0 | 1 | 8 | 6 |
| 28 | 1 | 11 | 2 | 0 |

Each verdict is supported by four chapter artifacts:

- `docs/chapterNN/CHAPTERNN_SOURCE_INVENTORY.md`
- `docs/chapterNN/CHAPTERNN_NOT_PROVED_LEDGER.md`
- `docs/chapterNN/CHAPTERNN_PROOF_SOURCE_LEDGER.md`
- `docs/chapterNN/CHAPTERNN_FORMALIZATION_REPORT.md`

Source-coverage summaries are under `docs/source_coverage/higham_chNN.md`.

## New public Lean modules

- `LeanFpAnalysis/FP/Algorithms/LeastSquares/Higham20Theorem20_4Absorption.lean`
- `LeanFpAnalysis/FP/Algorithms/LeastSquares/Higham20MinimumNormBackwardError.lean`
- `LeanFpAnalysis/FP/Algorithms/Vandermonde/Higham22.lean`
- `LeanFpAnalysis/FP/Algorithms/FastMatMul/Higham23.lean`
- `LeanFpAnalysis/FP/Algorithms/FFT/Higham24.lean`
- `LeanFpAnalysis/FP/Algorithms/FFT/Higham24Radix2.lean`
- `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24.lean`
- `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24ForwardPerturbation.lean`
- `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24Rounded.lean`
- `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24InverseFFT.lean`
- `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24LiteralSolver.lean`
- `LeanFpAnalysis/FP/Algorithms/Circulant/Higham24BackwardStability.lean`
- `LeanFpAnalysis/FP/Algorithms/Nonlinear/Higham25.lean`
- `LeanFpAnalysis/FP/Algorithms/Nonlinear/Higham25Problem25_1.lean`
- `LeanFpAnalysis/FP/Algorithms/AutomaticErrorAnalysis/Higham26.lean`
- `LeanFpAnalysis/FP/Algorithms/SoftwareIssues/Higham27.lean`
- `LeanFpAnalysis/FP/Algorithms/TestMatrices/Higham28.lean`
- `LeanFpAnalysis/FP/Algorithms/TestMatrices/Higham28Exact.lean`
- `LeanFpAnalysis/FP/Algorithms/TestMatrices/Higham28Probability.lean`
- `LeanFpAnalysis/FP/Algorithms/TestMatrices/Higham28Asymptotics.lean`
- `LeanFpAnalysis/FP/Algorithms/TestMatrices/Higham28Contracts.lean`
- `LeanFpAnalysis/FP/Algorithms/TestMatrices/Higham28Stewart.lean`
- `LeanFpAnalysis/FP/Algorithms/TestMatrices/Higham28Pascal.lean`

All are re-exported by `LeanFpAnalysis.FP.Algorithms`; representative entry
points are checked by `examples/LibraryLookup.lean`.

## Source-ledger corrections

Visual inspection corrected these ignored/local planning records:

- Split 4 is Chapters 20-28, not Chapter 20 alone.
- Chapter 22 has 26 actual equation labels; plain `(22.6)` is only a group
  cross-reference to `(22.6a)` and `(22.6b)`.
- Chapter 23 has 25 actual equation labels; plain `(23.7)` is only a group
  cross-reference, and the chapter has ten Problems including 23.5 plus its
  Appendix solution.
- Chapter 25 has six numbered sections including Section 25.2 and two Problems,
  25.1 and 25.2; Appendix A contains solution 25.1.
- Appendix A also contains solutions 22.9 and 27.4. Both local planning ledgers
  now include them; their chapter inventories retain them as optional,
  unselected rows rather than silently promoting them into core proof targets.

The Appendix A ownership audit found 185 unique solution labels in total. The
revised split counts are 63, 46, 22, 21, and 33 respectively; Split 4 owns the
33 labels whose prefixes are `20.x` through `28.x`.

The `chapter_splitting/` tree and `References/` remain local-only and are not
part of the tracked commit.

## Classification corrections made during integration

- Standard `O(u^2)` and asymptotic-equivalence `~` notation remain selected
  mathematical content with an explicit limiting filter; they are not treated
  like undefined `approx` prose.
- Chapter 20 p.386 MGS prose and Appendix 20.5's unspecified `c_(m,n) u`
  exercise are qualitative/optional rather than an invented `c3 u` theorem.
- Chapter 20 p.396 prints no residual inequality, constants, norm, or remainder
  and is deferred for lack of a precise statement.
- Chapter 20 p.404 overextends a strict-tall, matrix-only cited result to the
  chapter's square edge. An exact `1`-by-`1` nonzero-data counterexample proves
  the printed unqualified invariance false, so that row is a source discrepancy
  rather than an impossible open theorem.
- Chapter 24 now has actual producers for both forward FFTs, rounded diagonal
  division, the inverse FFT, and their exact composition. Theorem 24.3 remains
  open because its structured first-order generator/RHS split is still only a
  conditional execution-family input.
- Chapter 25 (25.11) is implemented as the preceding literal feasible
  limit-supremum, not merely the right-hand scalar; its Taylor-to-limit route
  is proved from a genuine derivative, but the source-facing implicit-function
  producer and derivative identity remain open. Equation (25.13) is produced
  from a literal rounded evaluation.

## Verification and trust

The final Chapter 28 focused build passed all 3,138 jobs, the Algorithms
umbrella passed all 4,036 jobs, and the complete repository build passed all
4,087 jobs. `examples/LibraryLookup.lean` compiled successfully. A
representative cross-chapter `#print axioms` audit, including actual producers
from Chapters 20-28, reported only `propext`, `Classical.choice`, and
`Quot.sound`. Forbidden-token, merge-marker, deleted-name, import/lookup,
Appendix-ownership, stale-gate, and `git diff --check` audits passed (the latter
emitted only line-ending notices). Three independent read-only audits corrected
stale gate claims and rejected target-bearing transfer assumptions as closure.
No source theorem is accepted as a Lean axiom, and no forbidden proof token or
target-equivalent assumption is counted as closure.
