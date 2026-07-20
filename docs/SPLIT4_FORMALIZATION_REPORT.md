# Higham Split 4 Formalization Report

## 2026-07-18 strict-audit supersession

This file preserves the 2026-07-16 Split 4 audit. Its aggregate and per-chapter
gate claims are superseded by the [fresh Chapters 1–28 audit](source_coverage/AUDIT_ch01-28_2026-07-18.md).
Current Split 4 status is **FAIL**: Chapters 20, 22, 25, and 28 are **FAIL**;
Chapters 21, 23, 24, 26, and 27 are **PASS**. The historical report below
remains for provenance and must not be treated as the current closure gate.

## Scope and audit basis

Split 4 owns Chapters 20-28 of Nicholas J. Higham, *Accuracy and Stability of
Numerical Algorithms*, second edition, together with Appendix A solution rows
whose labels begin `20.x` through `28.x`. The audit used the chapter PDFs and
Appendix PDF under `References/`, the complete Problems sections, rendered
checks of formula-heavy pages, and the repository chapter-formalization skill
in core mode.

At this final audit, the local skill already stated the full Chapters 20-28
plus Appendix A partition in both maintained skill copies, so it required no
further edit. The shared planning ledgers remain authoritative for exact source
labels and were corrected when visual inspection disagreed with them.

## Per-chapter selected-scope result

The aggregate selected-scope gate is **FAIL solely because Chapter 28 row
28-P3 remains PARTIAL/OPEN**. Chapters 20-27 are PASS with no selected
nonterminal row. Terminal citation-dependent or implementation-facing rows use visible
explicit domains whose hypotheses are upstream identities, local operation
budgets, law properties, or remainder estimates and whose nonvacuity is
demonstrated where practical; target-bearing certificates are not counted as
closure.

| Chapter | Gate | Principal local result | Remaining selected-scope boundary |
|---|---|---|---|
| 20, least squares | **PASS** | Theorem 20.4's actual QR/RHS/two-solve total perturbations and common witness; Theorem 20.7's literal pivoted QR/RHS/back-substitution producer; executable decreasing-row-norm sorting with the printed `alpha_i`/`beta_i` cap and `phi` invariance | No selected row open; qualitative or coefficient-free prose and documented source discrepancies remain terminal |
| 21, underdetermined systems | **PASS** | Previously completed and re-audited source-facing theory, algorithms, and explicit-domain rounded results | No selected row open; documented source corrections and domains remain visible |
| 22, Vandermonde systems | **PASS** | Exact Hermite factorization and Algorithms 22.1--22.3, including the literal Algorithm 22.3 executor-to-factor bridge and solve; actual rounded (22.19)--(22.21), Theorems 22.4/22.6, checkerboard Corollary 22.5, Problem 22.8 and Corollary 22.7, Algorithm 22.8 | Table 22.1 V1--V6 are citation-only literature-summary rows; empirical/editorial rows are stably skipped |
| 23, fast matrix multiplication | **PASS** | Literal rounded conventional, Miller, recursive Strassen/Winograd--Strassen/Bini--Lotti, and combined 3M--Strassen evaluators; printed coefficients and `O(u²)` remainders | No selected row open; empirical experiments and optional benchmark problems remain correctly skipped |
| 24, FFT and applications | **PASS** | Literal Theorems 24.1-24.2; complete (24.3)-(24.7); actual rounded four-stage solver; Theorem 24.3's constructed structured `Δc`, `Δb`, and `Δx`, exact equation, printed first-order radius, and explicit quadratic remainder | No selected row open; coefficient-free forward-error prose remains stably deferred |
| 25, nonlinear systems | **PASS** | Newton/error predicates; source-facing implicit-function producer for the local unique solution map and derivative `-F_x⁻¹ F_d`; literal feasible (25.11) supremum; literal rounded (25.13); stopping algebra; Problem 25.1 | No selected row open; undefined approximation/decrease claims and underspecified cited constants remain stably deferred |
| 26, automatic error analysis | **PASS** | General MDS best-vertex/reorder, reflection, expansion, contraction/retry, and finite run semantics plus stopping/cubic foundations and concrete finite directed-rounding producers for `+`, `-`, `*`, and `/` | No selected row open; MDS assumes no optimizer correctness or termination, while empirical examples remain correctly skipped |
| 27, software issues | **PASS** | Exact/rounded two-pass scaled norm, Smith division branch safety, and explicit source-range audit including the overbroad universal claim's counterexample | No selected row open; Blue's underspecified prose is terminal deferred |
| 28, test matrices | **FAIL** | Exact Hilbert/Cauchy/Pascal algebra and condition results; Stewart's concrete normalized-Haar producer; Ginibre density, incidence, expectation, determinant-moment, and characteristic-product reductions; prescribed-spectrum randsvd constructions; Pascal total-positivity and spectral endpoints; general Toeplitz spectrum/condition endpoints; companion characteristic, similarity, and SVD endpoints | The sole selected nonterminal row is 28-P3: the premise-free real-Ginibre expected-count formula for every positive dimension, or an equivalent unconditional limit theorem. The current general limit bridge assumes `RealGinibreFiniteExpectationFormula`. The printed complex companion-normality iff is a terminal source discrepancy, while undefined `approx`, cost, and LU-convergence rows are terminal deferred |

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

- `NumStability/Algorithms/LeastSquares/Higham20Theorem20_4Absorption.lean`
- `NumStability/Algorithms/LeastSquares/Higham20MinimumNormBackwardError.lean`
- `NumStability/Algorithms/Vandermonde/Higham22.lean`
- `NumStability/Algorithms/FastMatMul/Higham23.lean`
- `NumStability/Algorithms/FFT/Higham24.lean`
- `NumStability/Algorithms/FFT/Higham24Radix2.lean`
- `NumStability/Algorithms/Circulant/Higham24.lean`
- `NumStability/Algorithms/Circulant/Higham24ForwardPerturbation.lean`
- `NumStability/Algorithms/Circulant/Higham24Rounded.lean`
- `NumStability/Algorithms/Circulant/Higham24InverseFFT.lean`
- `NumStability/Algorithms/Circulant/Higham24LiteralSolver.lean`
- `NumStability/Algorithms/Circulant/Higham24BackwardStability.lean`
- `NumStability/Algorithms/Nonlinear/Higham25.lean`
- `NumStability/Algorithms/Nonlinear/Higham25Problem25_1.lean`
- `NumStability/Algorithms/AutomaticErrorAnalysis/Higham26.lean`
- `NumStability/Algorithms/SoftwareIssues/Higham27.lean`
- `NumStability/Algorithms/TestMatrices/Higham28.lean`
- `NumStability/Algorithms/TestMatrices/Higham28Exact.lean`
- `NumStability/Algorithms/TestMatrices/Higham28Probability.lean`
- `NumStability/Algorithms/TestMatrices/Higham28Asymptotics.lean`
- `NumStability/Algorithms/TestMatrices/Higham28Ginibre.lean`
- `NumStability/Algorithms/TestMatrices/Higham28GinibreMeasure.lean`
- `NumStability/Algorithms/TestMatrices/Higham28GinibreIncidence.lean`
- `NumStability/Algorithms/TestMatrices/Higham28GinibreExpectationGlue.lean`
- `NumStability/Algorithms/TestMatrices/Higham28GinibreDeterminantMoment.lean`
- `NumStability/Algorithms/TestMatrices/Higham28GinibreCharacteristicProduct.lean`
- `NumStability/Algorithms/TestMatrices/Higham28Contracts.lean`
- `NumStability/Algorithms/TestMatrices/Higham28Stewart.lean`
- `NumStability/Algorithms/TestMatrices/Higham28Cauchy.lean`
- `NumStability/Algorithms/TestMatrices/Higham28RandsvdNorm.lean`
- `NumStability/Algorithms/TestMatrices/Higham28Pascal.lean`
- `NumStability/Algorithms/TestMatrices/Higham28PascalCondition.lean`
- `NumStability/Algorithms/TestMatrices/Higham28PascalTotalPositivity.lean`
- `NumStability/Algorithms/TestMatrices/Higham28PascalSpectral.lean`
- `NumStability/Algorithms/TestMatrices/Higham28PascalOscillation.lean`
- `NumStability/Algorithms/TestMatrices/Higham28PascalOscillationCore.lean`
- `NumStability/Algorithms/TestMatrices/Higham28PascalDualFlag.lean`
- `NumStability/Algorithms/TestMatrices/Higham28PascalOscillationExact.lean`
- `NumStability/Algorithms/TestMatrices/Higham28ToeplitzGeneral.lean`
- `NumStability/Algorithms/TestMatrices/Higham28ToeplitzSpectrum.lean`
- `NumStability/Algorithms/TestMatrices/Higham28ToeplitzCondition.lean`
- `NumStability/Algorithms/TestMatrices/Higham28Companion.lean`
- `NumStability/Algorithms/TestMatrices/Higham28CompanionSpectral.lean`

All are re-exported by `NumStability.Algorithms`; representative entry
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
  division, the inverse FFT, and their exact composition. Theorem 24.3 is
  closed by the constructed structured generator/RHS perturbations, exact
  equation, printed first-order radius, and explicit quadratic remainder.
- Chapter 25 (25.11) is implemented as the preceding literal feasible
  limit-supremum, not merely the right-hand scalar; its Taylor-to-limit route
  is proved from a genuine derivative. The source-facing implicit-function
  producer and derivative identity are closed, and Equation (25.13) is
  produced from a literal rounded evaluation.

## Verification and trust

The fresh Algorithms umbrella build passed all 4,246 jobs and the complete
repository build passed all 4,296 jobs. `examples/LibraryLookup.lean` compiled
successfully. A
representative cross-chapter `#print axioms` audit, including actual producers
from Chapters 20-28, reported only `propext`, `Classical.choice`, and
`Quot.sound`. Forbidden-token, merge-marker, deleted-name, import/lookup,
Appendix-ownership, stale-gate, and `git diff --check` audits passed (the latter
emitted only line-ending notices). Three independent read-only audits corrected
stale gate claims and rejected target-bearing transfer assumptions as closure.
No source theorem is accepted as a Lean axiom, and no forbidden proof token or
target-equivalent assumption is counted as closure.
