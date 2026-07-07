# Higham Chapter 14 Formalization Report

## Source and scope

- Edition: 2nd ed., SIAM, 2002, verified from repository metadata, README, PDF chapter title/numbering, and the DOI-named chapter files.
- Chapter: 14, "Matrix Inversion"
- Printed pages: 259--285
- Source file: `References/1.9780898718027.ch14.pdf`
- Mode: core
- Parallel split: 3A
- Planning documents consulted: blueprint, Split 3A contracts, chapter index
- Inventory path: `docs/chapter14/CHAPTER14_SOURCE_INVENTORY.md`
- Not-proved ledger: `docs/chapter14/CHAPTER14_NOT_PROVED_LEDGER.md`
- Proof-source ledger: `docs/chapter14/CHAPTER14_PROOF_SOURCE_LEDGER.md`
- Selected-scope gate: FAIL, because several selected source-strength bounds are still represented by conditional interfaces or remain unstarted.

## Progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 14 | core | 100 | 82 | 60 | 50 | 74 | 71 | about 23 selected rows/classes | Conditional floating-point interfaces for Method 2/2C, Method D, and GJE second-stage accumulation; signed determinant parity, Hadamard/Hyman/problem rows still partly open | medium |

## Completed selected targets

| Source label | Lean declaration | File | Theorem surface | Notes |
|---|---|---|---|---|
| (14.1) | `ideal_right_residual` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Exact componentwise right-residual bound from an explicit perturbation and right-inverse equation. | Proved. |
| (14.2) | `ideal_left_residual` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Exact componentwise left-residual bound from an explicit perturbation and left-inverse equation. | Proved. |
| (14.4) | `triInv_method1_right_residual_matrix` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Method 1 right-residual bound via Ch8 triangular solve. | Proved from existing triangular solve theorem. |
| (14.5) | `triInv_method1_forward_error` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Componentwise forward-error bound for Method 1. | Proved. |
| (14.7) | `triInv_method1_normwise_error` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Legacy infinity-norm wrapper. | Proved. |
| (14.15)--(14.17) | `methodA_column_backward_error*`, `methodA_right_residual*`, `methodA_forward_error*` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Method A column, residual, and forward-error wrappers. | Proved from explicit specs/budgets. |
| (14.18) | `methodB_left_residual` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Method B left-residual bound from supplied triangular-inverse/solve specs. | Conditional but internally proved from stated hypotheses. |
| (14.19) | `methodC_mixed_residual`, `methodC_forward_error` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Mixed-residual interface and forward-error consequence. | Mixed residual is assumed; forward consequence proved. |
| (14.24) | `left_right_residual_comparison` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Exact comparison of left and right residuals through a left inverse. | Proved. |
| Problem 14.3 | `higham14_problem14_3_right_over_left_residual_infNorm_le_kappa`, `higham14_problem14_3_left_over_right_residual_infNorm_le_kappa`, `higham14_problem14_3_max_residual_ratio_infNorm_le_kappa` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Infinity-norm residual-ratio bound by `kappaInf`; includes exact identities `AX-I = A(XA-I)A_inv` and `XA-I = A_inv(AX-I)A`. | New after the initial milestone; denominators are explicit positivity hypotheses. |
| Problem 14.5 residual, forward, and first-order comparison bounds | `higham14_problem14_5_right_inverse_solve_residual_bound`, `higham14_problem14_5_left_inverse_solve_residual_bound`, `higham14_problem14_5_forward_error_of_residual_bound`, `higham14_problem14_5_right_inverse_solve_forward_error_bound`, `higham14_problem14_5_left_inverse_solve_forward_error_bound`, `higham14_problem14_5_right_inverse_solve_forward_error_firstorder_replacement`, `higham14_problem14_5_left_inverse_solve_forward_error_firstorder_replacement`, `higham14_problem14_5_left_firstorder_envelope_le_right_exact_rhs_envelope` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Right- and left-approximate-inverse residual bounds, residual-to-forward-error transfer, exact right/left forward envelopes, explicit `|X|`/`|Y|` replacement wrappers, and the exact envelope comparison showing the right first-order exact-RHS envelope is the left envelope after one extra `|A_inv||A|` amplification. | Source comparison layer closed at explicit bounded-replacement strength; full asymptotic `O(u^2)` calculus remains open. |
| Problem 14.7 | `higham14_problem14_7_inverse_entries_sum_eq_one_of_row_ones`, `higham14_problem14_7_inverse_entries_sum_eq_one_of_col_ones` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Sum of all inverse entries is one when A has a row or column of ones. | New in this pass; proved. |
| (14.34) partial | `higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec`, `higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_LUFactSpec`, `higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_PermutedLUFactSpec` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Determinant/product-of-pivots identity for exact no-pivot/unit-lower LU certificates and absolute-value determinant product for row-permuted LU certificates. | Partial closure; signed row-interchange parity and `psi(A)` remain open. |
| Problem 14.10 | `higham14_problem14_10_det_entry_perturb_eq`, `higham14_problem14_10_det_entry_independent_iff_adjugate_eq_zero` | `LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean` | Exact determinant entry-perturbation formula and iff condition for determinant independence from `a_ij`. | New after Problem 14.3; cofactor/adjugate condition is explicit. |
| Theorem 14.5 composition | `gje_overall_residual`, `gje_overall_forward_error` | `LeanFpAnalysis/FP/Algorithms/GaussJordan.lean` | Composition from explicit GE and GJE second-stage hypotheses. | Partial source closure; printed constants still open. |

## Reused from repository or Mathlib

| Source concept/result | Existing declaration | File/module |
|---|---|---|
| Legacy inverse predicates | `IsLeftInverse`, `IsRightInverse`, `IsInverse` | `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` |
| Matrix multiplication and identity | `matMul`, `idMatrix` | `LeanFpAnalysis.FP.Analysis.MatrixAlgebra` |
| Triangular solve backward-error infrastructure | `forwardSub_backward_error`, related triangular solve APIs | `LeanFpAnalysis.FP.Algorithms.ForwardSub`, `TriangularSolve` |
| LU backward-error interface | `LUBackwardError` | `LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination` |
| Floating-point gamma model | `gamma`, `gammaValid` | `LeanFpAnalysis.FP.Model` |

## New dependencies

| Declaration | Why needed | Used by | Feasibility status |
|---|---|---|---|
| `inverseRightResidual`, `inverseLeftResidual` | Stable source-facing names for `AX-I` and `XA-I`. | Problem 14.3; later Problems 14.4--14.5. | implemented |
| `higham14_problem14_3_right_residual_eq_mul_left_residual` | Exact identity `AX-I = A(XA-I)A_inv`. | Problem 14.3 right-over-left ratio. | implemented |
| `higham14_problem14_3_left_residual_eq_mul_right_residual` | Exact identity `XA-I = A_inv(AX-I)A`. | Problem 14.3 left-over-right ratio. | implemented |
| `higham14_problem14_3_max_residual_ratio_infNorm_le_kappa` | Closes the printed max residual-ratio inequality for `infNorm` under nonzero residual denominators. | Chapter 14 inventory/report. | implemented |
| `higham14_unit_roundoff_add_gamma_le_gamma_succ` | Scalar gamma collapse `u + gamma_n <= gamma_(n+1)`. | Problem 14.5 residual bound. | implemented |
| `higham14_problem14_5_right_inverse_solve_residual_bound` | Closes the right-approximate-inverse residual half of Problem 14.5. | Chapter 14 inventory/report. | implemented |
| `higham14_problem14_5_left_inverse_solve_residual_bound` | Closes the left-approximate-inverse residual half of Problem 14.5 with `b = Ax`. | Chapter 14 inventory/report. | implemented |
| `higham14_inverseLeftResidual_mulVec_add_self` | Expands `Y(Ax)` as `(YA-I)x + x` for the left forward-error proof. | Problem 14.5 left forward-error bound. | implemented |
| `higham14_problem14_5_forward_error_of_residual_bound` | Transfers a componentwise residual envelope to a forward-error envelope via a supplied left inverse. | Problem 14.5 right forward-error bound. | implemented |
| `higham14_problem14_5_right_inverse_solve_forward_error_bound` | Closes the right-approximate-inverse forward-error consequence through `|A_inv|`. | Chapter 14 inventory/report. | implemented |
| `higham14_problem14_5_left_inverse_solve_forward_error_bound` | Closes the exact `|Y||A||x|` left forward-error bound from Appendix A Problem 14.5. | Chapter 14 inventory/report. | implemented |
| `higham14_absMatrix_matMulVec_mono`, `higham14_absMatrix_matMulVec_nonneg` | Componentwise monotonicity and nonnegativity for absolute-matrix products. | Problem 14.5 first-order replacement wrappers. | implemented |
| `higham14_problem14_5_right_inverse_solve_forward_error_bound_of_abs_X_le` | Replaces `|X|` in the right forward envelope by any caller-supplied componentwise upper bound. | Problem 14.5 first-order replacement. | implemented |
| `higham14_problem14_5_right_inverse_solve_forward_error_firstorder_replacement` | Specializes the right forward envelope to `|A_inv||A||A_inv||b|` under `|X| <= |A_inv|`. | Chapter 14 inventory/report. | implemented |
| `higham14_problem14_5_left_inverse_solve_forward_error_bound_of_abs_Y_le` | Replaces `|Y|` in the left forward envelope by any caller-supplied componentwise upper bound. | Problem 14.5 first-order replacement. | implemented |
| `higham14_problem14_5_left_inverse_solve_forward_error_firstorder_replacement` | Specializes the left forward envelope to `|A_inv||A||x|` under `|Y| <= |A_inv|`. | Chapter 14 inventory/report. | implemented |
| `higham14_problem14_5_left_firstorder_envelope_le_right_exact_rhs_envelope` | Formalizes the comparison: with `b = Ax`, the right first-order exact-RHS envelope applies an extra `|A_inv||A|` amplification to the left envelope. | Problem 14.5 interpretation. | implemented |
| `matrixEntryPerturb` | Source-facing additive perturbation of one matrix entry. | Problem 14.10. | implemented |
| `higham14_problem14_10_det_entry_perturb_eq` | Exact determinant change formula `det(A+tE_ij)=det(A)+t*adj(A)_{ji}`. | Problem 14.10 independence iff. | implemented |
| `higham14_problem14_10_det_entry_independent_iff_adjugate_eq_zero` | Closes the determinant-independence condition in cofactor/adjugate form. | Chapter 14 inventory/report. | implemented |
| `higham14_eq14_34_det_eq_prod_U_diag_of_LUFactSpec` | Source-facing Chapter 14 wrapper around the existing unit-lower LU determinant product identity. | Equation (14.34) no-pivot core. | implemented |
| `higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_LUFactSpec` | Absolute-value form of the exact no-pivot LU determinant product. | Equation (14.34) no-pivot core. | implemented |
| `higham14_eq14_34_abs_det_eq_abs_prod_U_diag_of_PermutedLUFactSpec` | Absolute-value determinant product for row-permuted LU certificates. | Equation (14.34) GEPP absolute-value product. | implemented |
| `higham14_problem14_7_inverse_entries_sum_eq_one_of_row_ones` | Closes the row-ones half of Problem 14.7. | Chapter 14 inventory/report. | implemented |
| `higham14_problem14_7_inverse_entries_sum_eq_one_of_col_ones` | Closes the column-ones half of Problem 14.7. | Chapter 14 inventory/report. | implemented |

## External proof sources

| Selected claim | Source and exact location | Role | Local Lean closure | Status |
|---|---|---|---|---|
| Lemmas 14.1--14.3 and Method A--D bounds | Du Croz and Higham [357, 1992], exact locations not yet acquired | Detailed inverse-method error analyses | Partial interfaces only | open |
| Theorem 14.5 second-stage GJE | Peters-Wilkinson [938, 1975] and Dekker-Hoffmann [303, 1989], exact locations not yet acquired | GJE second-stage proof route | Composition wrappers only | open |
| Hyman method / Problem 14.14 | Wilkinson references cited in Notes 14.7; Appendix A solution 14.14 | Hyman determinant error route | none | open |
| Problem 14.15 | Godunov et al. [493, 1993] and singular-value inequalities cited in Appendix A | Determinant perturbation theorem | none | open |

## GPT-5.5 Pro browser consultations

No consultation was used in this milestone. The current blockers are inventoried and still at the repository/Mathlib search and theorem-design stage.

## Skipped items

| Source location | Summary | Reason code |
|---|---|---|
| Figure 14.1 | MATLAB residual plot for a specific family and implementation. | SKIP-EMPIRICAL |
| Tables 14.1--14.5 | Backward-error samples, performance rates, and historical timings. | SKIP-EMPIRICAL |
| Notes 14.7 and LAPACK prose | Literature and software notes. | SKIP-LITERATURE-REVIEW |
| Problem 14.1 | Historical cautionary tale. | SKIP-EDITORIAL |
| Problem 14.6 | Fixed external cover-matrix exercise. | SKIP-FIXED-NUMERICAL |

## Deferred items

| Source location | Summary | Destination/dependency | Reason |
|---|---|---|---|
| Problem 14.9 | Computational investigation of a generalized Sylvester-equation approach. | Chapter 16 / benchmark mode | The source asks for a computational investigation and references Sylvester machinery. |
| Section 14.5 Schulz/Csanky overview | Parallel inverse methods and convergence commentary. | Future benchmark/algorithm work if requested | Mostly literature review and broad algorithm survey; precise Schulz identities are not needed for current core closures. |

## Benchmark candidates

| Source location | Methods compared | Required dependencies |
|---|---|---|
| Section 14.5 | Csanky, Schulz iteration, and parallel/divide-and-conquer inverse methods | Complexity model, matrix iteration convergence, floating-point stability model |
| Tables 14.2--14.5 | Triangular/full inverse implementations on specific machines | Machine and implementation model, benchmark mode |

## Open selected-scope items

See `docs/chapter14/CHAPTER14_NOT_PROVED_LEDGER.md`. The highest-leverage next rows are:

| Source location | Exact claim | Current Lean status | Missing foundation | Next theorem |
|---|---|---|---|---|
| Lemma 14.1 / (14.8) | Method 2 left residual | conditional transfer | Method 2 stage induction | Source-faithful Method 2 loop residual theorem |
| (14.25)--(14.30) | GJE second-stage accumulation | conditional transfer | cumulative product induction | Exact (14.27)--(14.28) wrappers, then (14.29)--(14.30) |
| Theorem 14.5 | Printed GJE constants | partial foundation | second-stage closure and first-order scalar simplification | Instantiate composition theorem to `8 n u`/`2 n u` source surfaces |
| (14.35)--(14.36) | Hyman exact determinant identities | unstarted | block determinant algebra | Exact block LU/determinant wrappers |

## Hidden-hypothesis summary

- The new Problem 14.3 max-ratio theorem assumes both residual denominators are positive. The two one-sided ratio lemmas require only the denominator used by that ratio. This makes the source's implicit nonzero-ratio side condition explicit.
- The new Problem 14.5 theorems close both source residual bounds, the exact right/left forward-error consequences, explicit first-order replacement wrappers, and the exact envelope-comparison interpretation. The right residual theorem assumes `|AX-I| <= u|A||X|`; the right forward theorem additionally assumes a supplied left inverse `A_inv` and `Ax = b`. The first-order wrappers make the `|X| <= |A_inv|` and `|Y| <= |A_inv|` replacement assumptions explicit; the comparison theorem shows the exact-RHS right envelope is the left first-order envelope after one extra nonnegative `|A_inv||A|` amplification. Full asymptotic `O(u^2)` replacement calculus remains open.
- The new Problem 14.10 theorem states the determinant-independence condition as `adj(A)_{ji}=0`. For a nonsingular matrix this is equivalent to the corresponding inverse-entry condition after multiplying by the nonzero determinant factor.
- The new (14.34) determinant theorems include the no-pivot/unit-lower LU core and the row-permuted absolute-value product. They do not yet include a signed row-interchange parity formula and do not define the Hadamard determinant condition number `psi(A)`.
- The new Problem 14.7 theorems assume the appropriate inverse side explicitly (`IsRightInverse` for a row of ones, `IsLeftInverse` for a column of ones); these are source/domain assumptions, not proof artifacts.
- Existing Method 2, Method 2C, Method D, and GJE theorem surfaces still include hypotheses that are essentially the missing algorithmic analyses. They are recorded as conditional interfaces and do not close the source rows.
- Existing `O(u^2)` source statements are not fully modeled unless a theorem explicitly exposes a first-order wrapper; the report does not count asymptotic endpoints as closed.

## Weak-component and bottleneck summary

- Weak components: all floating-point residual/stability interfaces, GJE composition wrappers, and documentation completion claims.
- Active bottleneck: no red bottleneck yet for Chapter 14. The current main blocker is initial missing foundation work rather than repeated failed proof attempts.

## Verification

- Commands run so far:
  - `lake env lean LeanFpAnalysis/FP/Algorithms/MatrixInversion.lean`
  - `lake env lean LeanFpAnalysis/FP/Algorithms/GaussJordan.lean`
  - `lake build LeanFpAnalysis.FP.Algorithms.MatrixInversion`
  - `lake build LeanFpAnalysis.FP.Algorithms.GaussJordan`
  - `git diff --check`
  - stale source-label scan for `Chapter 13`, `§13`, and equation/theorem label variants in the touched Lean files
  - marker scan for `sorry`, `admit`, `axiom`, `unsafe`, and `opaque` over the touched Chapter 14 Lean files
  - focused `#check` file for the two new Problem 14.7 theorems
  - focused `#print axioms` file for the two new Problem 14.7 theorems
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.3 residual-ratio theorems
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.5 right-residual theorem
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.5 left-residual theorem
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.5 right and left forward-error theorems
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.5 first-order replacement and envelope-comparison theorems
  - stdin focused `#check`/`#print axioms` run for the new Problem 14.10 determinant-independence theorems
  - focused module build after the new (14.34) determinant wrappers
  - focused `#check`/`#print axioms` run for the new pivoted absolute-value (14.34) wrapper
  - `lake env lean examples/LibraryLookup.lean`
- Result: both touched Lean files compile after the label correction and Problem 14.7 addition; focused module builds pass before and after the upstream merge and after the Problem 14.3, Problem 14.5 residual/forward/first-order, Problem 14.10, and (14.34) additions; `git diff --check` passes; stale-label and marker scans are clean; focused `#check` and axiom checks pass.
- New theorem axiom surface: the new Problem 14.3, Problem 14.5 residual/forward/first-order, Problem 14.7, Problem 14.10, and (14.34) theorems use only the standard Mathlib axioms reported by Lean (`propext`, `Classical.choice`, `Quot.sound`) when checked; the (14.34) wrappers inherit existing determinant/permutation/LU determinant facts.
- Known verification issue: the full `examples/LibraryLookup.lean` run aborts with a stack overflow / exit 134 after producing large lookup output. Focused lookups for the new declarations pass, so this is recorded as a full-example scale issue rather than a failed declaration lookup.
- New versus pre-existing warnings: a new unused-simp warning appeared during initial Problem 14.7 proof and was removed.

## GitHub synchronization

- Local branch: main
- Latest remote base integrated: `origin/main` fast-forwarded from `0af482e1` to `8411b4d2` before theorem design, then merged `57d02bfd`, `5e10aea0`, `e6c81dbe`, and `c03d362f` after local Chapter 14 milestones; upstream `45c2e8b3` was present before the determinant-product milestone; upstream `3cf69465` was merged cleanly before the Problem 14.5 forward-use push.
- Milestone commits and split prefixes: `6939f36a` (`Split 3A: start Ch14 matrix inversion inventory`), `63347956` (`Split 3A: formalize Ch14 residual ratio`), `90a50b13` (`Split 3A: formalize Ch14 inverse exercises`), `3d01123b` (`Split 3A: clean Ch14 inverse exercise report`), `a2234884` (`Split 3A: formalize Ch14 determinant product`), `1ce54698` (`Split 3A: formalize Ch14 inverse residual completion`), `6e01df40` (`Split 3A: formalize Ch14 inverse forward use`)
- Local merge commits before report-sync updates: `24f75fa4`, `30c972c4`, `3fd44412`, `ff90ea53`, `dc77d6aa`
- Pushed to origin/main: yes, through `dc77d6aa` before this push-record update
- Merge/conflict resolution: clean `ort` merges; latest upstream changed `LeanFpAnalysis/FP/Algorithms/LeastSquares/LSE.lean`, `LeanFpAnalysis/FP/Algorithms/Sylvester/Higham16Spectrum.lean`, `docs/source_coverage/higham_ch16.md`, and `docs/source_coverage/higham_ch20.md`
- New upstream imports or exported contracts: none

## Documentation

- Inventory path: `docs/chapter14/CHAPTER14_SOURCE_INVENTORY.md`
- Not-proved ledger path: `docs/chapter14/CHAPTER14_NOT_PROVED_LEDGER.md`
- Proof-source ledger path: `docs/chapter14/CHAPTER14_PROOF_SOURCE_LEDGER.md`
- Theorem note or PDF: not generated

## Open issues

- Source-visible Problem 14.14 is omitted from the shared chapter problem ledger but appears in the PDF and Appendix A Split 3A ownership list. The inventory includes it.
- Existing `CondEstimation.lean` and `LU/TridiagonalCond.lean` carry older `§14` labels for material now assigned to Chapter 15 by the split plan. They were not changed in this milestone.
- Full source-strength completion of Chapter 14 requires proving several currently conditional floating-point interfaces and determinant/Hyman/problem rows.
