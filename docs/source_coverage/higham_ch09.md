# Higham Chapter 9 Formalization Report - "LU Factorization and Linear Equations"

## Source and scope
- Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed. (SIAM, 2002).
- Chapter: 9, "LU Factorization and Linear Equations" (printed pp. 157-193).
- Source file: `higham-split/sources/chapter-pdfs/1.9780898718027.ch9.pdf`.
- Mode: core.
- Parallel split: 2 (chapters 7-12).
- Planning documents consulted: blueprint, Split 2 section of `split_primary_contracts.md`, `chapter_index.md`.
- Selected-scope gate: PASS. The primary labels Theorems 9.1, 9.3-9.5,
  9.8-9.15, Lemma 9.6, and Algorithm 9.2 are represented by proved
  source-facing declarations; the numbered equation families (9.1)-(9.27) are
  accounted for by the chapter surfaces listed below.

Primary Lean module: `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean`
(chapter-label surface); reusable LU, triangular solve, growth-factor,
tridiagonal, and special-matrix foundations are imported from the `LU/*` modules
and shared analysis files.

## Completed selected targets (primary labels)
| Source label | Lean declaration(s) | Notes |
|---|---|---|
| Theorem 9.1 (LU existence/uniqueness and pivot foundations) | `higham9_1_*`, `higham9_2_DoolittleLU`, `higham9_2_exactDoolittle_recurrences_to_LUFactSpec`, `higham9_1_lu_unique_of_pivots_ne_zero` | determinant/pivot product, Schur complement, and exact LU interfaces |
| Algorithm 9.2 (Gaussian elimination / Doolittle variants) | `higham9_2_*DenseLoop*`, `higham9_2_*AbsBudget*`, `higham9_2_rectRounded*`, `higham9_2_*Permuted*` | square, rectangular, partial-pivot, and complete-pivot loop certificates |
| Theorem 9.3 (GE backward error) | `higham9_3_lu_backward_error_gamma`, `higham9_3_exactDoolittle_recurrences_backward_error_gamma`, `higham9_3_rectRoundedLoop_backward_error`, `higham9_3_*permuted*backward_error*` | exact and rounded Doolittle backward-error surfaces |
| Theorem 9.4 (LU solve backward error) | `higham9_4_lu_solve_backward_error`, `higham9_4_exactDoolittle_recurrences_lu_solve_backward_error`, `higham9_4_rectRoundedLoop_square_lu_solve_backward_error` | triangular solve handoff |
| Theorem 9.5 (Wilkinson-type solve bound) | `higham9_5_wilkinson_source_bound_of_entry_growth`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace`, plus dense/abs-budget/rounded-loop variants | growth-factor-to-solve-error bridge |
| Lemma 9.6 (growth and reduced-matrix support) | `higham9_6_absLU_infNorm_le_source_constant_of_noPivotReducedGrowthFactor_exists_hAmax`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero_exists_hAmax`, `higham9_6_lu_exists_nonnegative_of_totalNonnegative_det_ne_zero` | no-pivot growth, reduced entries, and total-nonnegative support |
| Theorem 9.8 (complete pivoting lower-bound families) | `higham9_8_growth_factor_ge_theta_real`, `higham9_8_exists_completePivoting_growth_factor_ge_theta_real`, `higham9_8_exists_completePivoting_growth_factor_ge_theta_nonsingInv`, `higham9_8_*checkerboard*` | real and checkerboard-conjugate witnesses |
| Theorem 9.9 (diagonal dominance) | `higham9_9_colDiagDominant_exists_LUFactSpec_growthFactorEntry_le_two_of_le_two`, `higham9_9_rowDiagDominant_exists_LUFactSpec_growthFactorEntry_le_two_of_le_two`, `higham9_9_*wilkinson_source_bound_exists*` | column/row diagonal dominance and small-dimension endpoint wrappers |
| Theorem 9.10 (Hessenberg matrices) | `higham9_10_hessenberg_growth_backward_error`, `higham9_10_hessenberg_lu_solve_backward_stable_tight`, `higham9_10_HessenbergGEPPUTrace_*` | Hessenberg GEPP structure and solve bound |
| Theorem 9.11 (banded matrices) | `higham9_11_bohteBound*`, `higham9_11_bohte_banded_solve_tight*`, `higham9_11_matrix_bohte_banded_solve_tight*`, `higham9_11_matrix_tridiag_data_bohte_solve_tight*` | Bohte constants, bandwidth-specialized wrappers, and Matrix APIs |
| Theorem 9.12 (special classes with no growth) | `higham9_12_spd_*`, `higham9_12_nonneg_lu_*`, `higham9_12_mmatrix_lu_*`, `higham9_12_sign_equiv_*`, `higham9_12_totalNonnegative_*`, and the `higham9_12_matrix_*` wrappers | SPD tridiagonal, nonnegative LU, M-matrix, sign-equivalent, total-nonnegative, and Matrix-facing surfaces |
| Theorem 9.13 (tridiagonal diagonal dominance) | `higham9_13_colDiagDom_*`, `higham9_13_rowDiagDom_*`, `higham9_13_tridiag_builder_*`, `higham9_13_matrix_colDiagDom_*`, `higham9_13_matrix_rowDiagDom_*` | `rho <= 3` and componentwise growth packages |
| Theorem 9.14 (growth-factor consequences and special solves) | `higham9_14_f`, `higham9_14_h`, `higham9_14_source_*`, `higham9_14_matrix_source_*`, `higham9_14_tridiag_*`, `higham9_14_totalNonnegative_*`, `higham9_14_checkerboard_*` | source `f(u)`/`h(u)` bounds and special-class endpoints |
| Theorem 9.15 (LU sensitivity) | `higham9_15_lu_perturbation_identity`, `higham9_15_lu_perturbation_relative_bound`, `higham9_15_lu_perturbation_forward_bound`, `higham9_15_chi*`, `higham9_15_normalized_G*`, `higham9_15_componentwise_source_firstOrder*` | condition-chain, resolvent, first-order, and componentwise sensitivity APIs |

## Equations
Equations (9.1)-(9.27) are accounted for by the source-facing declaration
families above: pivot/Doolittle and Schur-complement identities (`higham9_1_*`,
`higham9_2_*`), backward-error and solve equations (`higham9_3_*`,
`higham9_4_*`, `higham9_5_*`), block/sine/Fourier and growth-factor witnesses
(`higham9_8_*` through `higham9_13_*`), tridiagonal data and recurrences
(`higham9_18_*`, `higham9_19_*`), source `f(u)`/`h(u)` bounds and model
equations (`higham9_14_*`), and LU sensitivity operators/normalized systems
(`higham9_15_*`).

## Skipped items (reason codes)
| Source location | Summary | Reason |
|---|---|---|
| Historical notes, implementation commentary, and LAPACK-style prose | background and software guidance | non-mathematical/editorial |
| Empirical performance remarks | qualitative observations | empirical, no formalizable theorem statement |

## Benchmark-reserved (identifiers only - NOT formalized as chapter work)
Problems 9.1-9.18 and Appendix A solutions 9.2-9.11, 9.13 are
benchmark-reserved. Some reusable declarations carry `higham_problem9_*` names
from earlier library work; they are not new exercise transcriptions for this
chapter pass.
The rendered PDF lists Problem 9.12, so it is included in this reserved range
even though the current planning ledgers omit that identifier.

## Open selected-scope items (not-proved ledger)
None. All selected primary labels for Chapter 9 are represented by proved Lean
declarations, with Matrix-facing wrappers added for the Theorem 9.11-9.13 API
surfaces during the final pass.

## Hidden-hypothesis summary
- Exact factorization wrappers state determinant, pivot, diagonal-dominance,
  tridiagonal, SPD, nonnegative, M-matrix, sign-equivalence, or trace
  certificate hypotheses explicitly rather than deriving them silently.
- Rounded GE/solve wrappers expose the loop certificate or budget certificate
  supplying the floating-point local-error model.
- Theorem 9.14 source `f(u)`/`h(u)` endpoints separate model assumptions from
  actual triangular-solve wrappers; gamma-specialized wrappers record the
  required `gammaValid` hypotheses.
- Theorem 9.15 sensitivity results expose inverse/product/resolvent/majorant
  assumptions through named predicates and lemmas; no hidden nonsingularity
  premise is folded into a conclusion.

## Verification
- Recent commands:
  - `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` passed after the final Theorem 9.13 Matrix-wrapper increment.
  - `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` passed: `Build completed successfully (3045 jobs)`.
  - `lake env lean --tstack=131072 examples/LibraryLookup.lean` passed after the final lookup additions.
  - `#print axioms` audits for the newly added Theorem 9.12 and Theorem 9.13 Matrix wrappers all reported only `[propext, Classical.choice, Quot.sound]`.
  - `git diff --check` and added-line placeholder scans were clean before each synced increment.

## Documentation
- Inventory and report: `docs/source_coverage/higham_ch09.md` (this file).
- Public lookup smoke checks: `examples/LibraryLookup.lean`.
- Name inventory: `docs/LIBRARY_LOOKUP.md`.

## Open issues
None for the selected Chapter 9 scope.
