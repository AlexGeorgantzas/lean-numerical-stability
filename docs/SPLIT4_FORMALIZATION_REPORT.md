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

The aggregate selected-scope gate is **PASS**. Every precise selected row is
terminal. Citation-dependent or implementation-facing rows use visible
explicit domains whose hypotheses are upstream identities, local operation
budgets, law properties, or remainder estimates and whose nonvacuity is
demonstrated where practical; target-bearing certificates are not counted as
closure.

| Chapter | Gate | Principal local result | Remaining selected-scope boundary |
|---|---|---|---|
| 20, least squares | **PASS (EXPLICIT-DOMAIN)** | Theorem 20.4's actual QR/RHS/two-solve total perturbations and common witness; Theorem 20.7's literal pivoted QR/RHS/back-substitution producer with pivot-position `(j+1)^2`; complete named/equation/prose audit including source discrepancies | No selected row open; implementation assumptions are visible and underspecified prose is terminal deferred |
| 21, underdetermined systems | **PASS** | Previously completed and re-audited source-facing theory, algorithms, and explicit-domain rounded results | No selected row open; documented source corrections and domains remain visible |
| 22, Vandermonde systems | **PASS** | Actual Algorithms 22.1–22.3 loops, symbolic/table/confluent algebra, explicit-domain factor/solve/error named results with producers, Problem 22.8, and genuine refinement convergence | No selected row open; cited condition estimates and rounded factor analyses expose nonvacuous upstream domains |
| 23, fast matrix multiplication | **PASS** | Actual rounded Winograd/conventional/3M paths, exact operation counts and recurrences, normwise/first-order bounds, and explicit-domain recursive Theorems 23.2–23.4 plus Problem 23.6 | No selected row open; citation-only constants/recursive graphs use constructive first-order domains |
| 24, FFT and applications | **PASS** | Literal Theorem 24.1 factorization; complete (24.3)-(24.4); rounded butterfly primitive bound; nonvacuous explicit stage, matrix-perturbation, and solver domains closing Theorem 24.2 and (24.6)-(24.7); exact (24.8); explicit `IsBigO` family closing Theorem 24.3 | No precise selected row open; one under-specified prose claim is deferred and the optional exercise excluded |
| 25, nonlinear systems | **PASS** | Newton/error predicates; literal feasible (25.11) supremum and limit on an explicit unique-solution-map/Taylor domain with nonvacuity; literal rounded (25.13); stopping algebra; complete Problem 25.1 | Undefined `≈` theorems and other under-specified citation prose are deferred separately |
| 26, automatic error analysis | **PASS** | Exact search/stopping/cubic foundations plus concrete finite directed-rounding producers and outward interval containment for `+`, `-`, `*`, and `/` | No selected row open; empirical examples remain correctly skipped |
| 27, software issues | **PASS** | Exact/rounded two-pass scaled norm, Smith division branch safety, and explicit source-range audit including the overbroad universal claim's counterexample | No selected row open; Blue's underspecified prose is terminal deferred |
| 28, test matrices | **PASS** | Unconditional Hilbert/Pascal/Toeplitz algebra plus explicit-domain Cauchy, Haar, probability, asymptotic, Toeplitz-spectrum, and companion transfers with producers | No selected row open; undefined `approx` rows are terminal deferred |

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
- `LeanFpAnalysis/FP/Algorithms/Nonlinear/Higham25.lean`
- `LeanFpAnalysis/FP/Algorithms/Nonlinear/Higham25Problem25_1.lean`
- `LeanFpAnalysis/FP/Algorithms/AutomaticErrorAnalysis/Higham26.lean`
- `LeanFpAnalysis/FP/Algorithms/SoftwareIssues/Higham27.lean`
- `LeanFpAnalysis/FP/Algorithms/TestMatrices/Higham28.lean`
- `LeanFpAnalysis/FP/Algorithms/TestMatrices/Higham28Exact.lean`
- `LeanFpAnalysis/FP/Algorithms/TestMatrices/Higham28Probability.lean`
- `LeanFpAnalysis/FP/Algorithms/TestMatrices/Higham28Asymptotics.lean`
- `LeanFpAnalysis/FP/Algorithms/TestMatrices/Higham28Contracts.lean`

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
- Chapter 24's rounded claims are closed only at visible nonvacuous execution
  domains; local stage/matrix/asymptotic obligations are not hidden as final
  conclusions.
- Chapter 25 (25.11) is implemented as the preceding literal feasible
  limit-supremum, not merely the right-hand scalar; (25.13) is produced from a
  literal rounded evaluation.

## Verification and trust

Focused module builds and representative axiom checks were run throughout the
chapter work. After rebasing the Split 4 integration commit over the latest 13
Chapter 11 commits from `origin/main`, the combined full `lake build` passed all
4073 jobs and `examples/LibraryLookup.lean` compiled successfully. A final
ten-endpoint axiom audit spanning Chapters 20-28 reported only `propext`,
`Classical.choice`, and `Quot.sound`. The independent integration audit found
all 16 new modules reachable from `LeanFpAnalysis.FP.Algorithms`, all 66 added
public lookup names present, and no scratch files, forbidden proof tokens,
merge markers, trailing whitespace, stale gate text, or `git diff --check`
failures. No source theorem is accepted as a Lean axiom, and no `sorry`,
`admit`, `unsafe`, or target-equivalent assumption is counted as closure.
