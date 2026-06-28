# Higham Chapter 9 Formalization Report

Date: 2026-06-20, updated 2026-06-28 in the Split 2 proof-completion pass.
Source: `References/1.9780898718027.ch9.pdf`.
Appendix source read: `References/1.9780898718027.appa.pdf`.
Edition: Higham, *Accuracy and Stability of Numerical Algorithms*, 2nd ed., SIAM.
Chapter: 9, "LU Factorization and Linear Equations".
Mode: proof-completion, core selected-scope pass.
Parallel split: Split 2. For this chapter, "previous split" means Split 1.
Planning documents consulted: `HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`,
`split_primary_contracts.md`, and `chapter_index.md`.
Selected-scope gate: FAIL. The proof-completion and unifying passes closed
additional local rows and bridges, but several Split-2-owned LU, pivoting,
determinant, and growth-factor rows remain open.

## Progress Snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- | --- |
| 9 | proof-completion | 100 | 97 | 95 | 96 | 96 | 95 | 5 row families | Rounded pivot trace-to-dense-loop construction after the closed pivoted literal source-budget, component-dominance, exact-product, exact-target-gap, and partial-/complete-/rook-pivot exact trace-to-solve wrappers; residual rectangular executable-loop scheduling after the closed rectangular rounded-fold and absolute-budget certificate surfaces; Bohte external banded proof source; Wilkinson/Foster sharp product proofs; full tridiagonal all-class executable coverage after the closed diagonal-dominant exact-source, lower-level model, and actual-solve `f(u)`/`h(u)` packages; and full Barrlund/Sun Schur-induction/spectral-radius theorem beyond the closed `χ(A)`, `G` ratio, normalized-identity/split, inverse-normalization, source-correct operator-denominator assembly, zero-residual min-factor discharge, factorization-level residual handoffs, and conditional normwise/componentwise source wrapper support | Medium |

## 2026-06-28 Theorem 9.14 Constant-Growth `h(u)` Source Wrappers

This continuation closed the missing final-coefficient surface for the
column- and row-diagonally-dominant exact-LU source packages.  The existing
Theorem 9.13 packages provide `|Lhat||Uhat| <= 3|A|`; the new generic bridge
uses `f(u) <= h(u)` for `0 <= u < 1` to widen the equation-(9.22) result to
`3 h(u)|A|`, then exposes both explicit-model and actual-triangular-solve
entry points.

These wrappers do not construct the still-open rounded tridiagonal
factorization recurrence or executable loop trace.  They close the exact
source-data handoff once the equation (9.20)/(9.21) models, or exact factors
plus actual triangular solves, are available.

New declarations:

- `higham9_14_f_le_h`.
- `higham9_14_source_h_bound_of_absLU_le_const_absA_and_9_20_9_21_models`.
- `higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_const_gamma_le`.
- `higham9_14_colDiagDom_exists_LUFactSpec_source_h_bound_of_models`.
- `higham9_14_rowDiagDom_exists_LUFactSpec_source_h_bound_of_models`.
- `higham9_14_colDiagDom_exists_LUFactSpec_source_h_bound_actual_triangular_solves`.
- `higham9_14_rowDiagDom_exists_LUFactSpec_source_h_bound_actual_triangular_solves`.

## 2026-06-28 Theorem 9.14 Lower-Level Diagonal-Dominant `h(u)` Wrappers

This continuation extended the same constant-growth final-coefficient bridge
to the lower-level diagonal-dominant tridiagonal endpoints.  The builder,
recurrence, and ordinary `LUFactSpec` source-model wrappers now expose
`3 h(u)|A|` counterparts to their existing `3 f(u)|A|` forms, and the
LU-backward-error plus actual-triangular-solve generic bridge now has a
constant-growth final-coefficient variant ready for the executable handoff
layer.

These declarations still consume explicit equation (9.20)/(9.21) models or a
separate LU-backward-error certificate.  They do not prove that a rounded
tridiagonal factorization recurrence produces such a certificate.

New declarations:

- `higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_const_gamma_le`.
- `higham9_14_tridiag_colDiagDom_source_h_bound_from_builders`.
- `higham9_14_tridiag_rowDiagDom_source_h_bound_from_builders`.
- `higham9_14_tridiag_colDiagDom_source_h_bound_from_recurrence`.
- `higham9_14_tridiag_rowDiagDom_source_h_bound_from_recurrence`.
- `higham9_14_tridiag_colDiagDom_source_h_bound_from_LUFactSpec`.
- `higham9_14_tridiag_rowDiagDom_source_h_bound_from_LUFactSpec`.

## 2026-06-28 Theorem 9.14 Diagonal-Dominant Actual-Solve `h(u)` Wrappers

This continuation added the actual-triangular-solve counterparts for the
lower-level diagonal-dominant final-coefficient surfaces.  The builder and
recurrence paths now have `3 h(u)|A|` wrappers both from an explicit
`LUBackwardError` certificate and from exact `LUFactSpec` factors; the ordinary
`LUFactSpec` plus `LUBackwardError` source path also has direct column- and
row-dominant final-coefficient endpoints.

The executable rounded factorization trace remains open.  These wrappers close
the route after such a certificate is available, and after the actual
`fl_forwardSub`/`fl_backSub` triangular solves are selected.

New declarations:

- `higham9_14_tridiag_colDiagDom_source_h_bound_from_builders_LUBackwardError_fl_triangular_solves`.
- `higham9_14_tridiag_rowDiagDom_source_h_bound_from_builders_LUBackwardError_fl_triangular_solves`.
- `higham9_14_tridiag_colDiagDom_source_h_bound_from_recurrence_LUBackwardError_fl_triangular_solves`.
- `higham9_14_tridiag_rowDiagDom_source_h_bound_from_recurrence_LUBackwardError_fl_triangular_solves`.
- `higham9_14_tridiag_colDiagDom_source_h_bound_from_builders_LUFactSpec_fl_triangular_solves`.
- `higham9_14_tridiag_rowDiagDom_source_h_bound_from_builders_LUFactSpec_fl_triangular_solves`.
- `higham9_14_tridiag_colDiagDom_source_h_bound_from_recurrence_LUFactSpec_fl_triangular_solves`.
- `higham9_14_tridiag_rowDiagDom_source_h_bound_from_recurrence_LUFactSpec_fl_triangular_solves`.
- `higham9_14_tridiag_colDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves`.
- `higham9_14_tridiag_rowDiagDom_source_h_bound_from_LUBackwardError_fl_triangular_solves`.

## 2026-06-27 Theorem 9.12/9.14 SPD Nonsingularity Wrappers

This continuation removed redundant nonsingularity side conditions from the
SPD positive-`D L^T` exact-factor endpoints.  The new source-facing wrappers
derive `det A != 0` and `0 < maxEntryNorm A` from `IsSymPosDef n A` via the
repository theorems `isSymPosDef_det_ne_zero` and
`maxEntryNorm_pos_of_det_ne_zero`, then apply the existing growth and
`f(u)|A|` endpoints.  The wrappers intentionally keep the visible tridiagonal
exact-factor, positive diagonal, and `U = D L^T` hypotheses; they do not claim
the still-open source construction of those factors or the rounded tridiagonal
execution trace.

New declarations:

- `higham9_12_spd_tridiag_growthFactorEntry_le_one_of_spd`.
- `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_spd`.
- `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_spd_recurrence`.
- `higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_spd`.

## 2026-06-27 Theorem 9.12 Determinant-Denominator Wrappers

This continuation also removed another source-proof artifact from the
Theorem 9.12 special-class no-growth surfaces.  The existing nonnegative-LU,
M-matrix, sign-equivalent, Problem 9.6 total-nonnegative, and Theorem 9.12
total-nonnegative growth endpoints still accepted an explicit proof of
`0 < maxEntryNorm A`.  The new wrappers derive that positive denominator from
the already-source-shaped nonsingularity hypothesis `det A != 0` using
`maxEntryNorm_pos_of_det_ne_zero`, then call the existing no-growth theorems.
They do not add new special-class existence facts beyond the already proved
total-nonnegative source package and the still-visible factor/certificate
hypotheses for the other classes.

New declarations:

- `higham9_12_nonneg_lu_growthFactorEntry_le_one_of_det_ne_zero`.
- `higham9_12_mmatrix_lu_growthFactorEntry_le_one_of_det_ne_zero`.
- `higham9_12_sign_equiv_growthFactorEntry_le_one_of_det_ne_zero`.
- `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero_exists_hAmax`.
- `higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_det_ne_zero_exists_hAmax`.
- `higham9_12_totalNonnegative_exists_LUFactSpec_growthFactorEntry_le_one_exists_hAmax`.

## 2026-06-28 Problem 9.6 Principal-Block Denominator Wrappers

This continuation removed the last explicit max-entry denominator proof from
the Appendix A total-nonnegative principal-block route.  The new source-facing
wrappers derive `0 < maxEntryNorm A` from either the positive determinant
variant or the source nonsingularity hypothesis `det A != 0`, then reuse the
already-proved principal-block determinant-inequality, nonnegative exact-LU,
final-`U` no-growth, and reduced-matrix no-growth endpoints.  These wrappers do
not add a new determinant inequality or hide any external assumption; the
principal-block inequality remains visible where that route requires it.

New declarations:

- `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_and_properLeadingPrincipalBlock_pos_exists_hAmax`.
- `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_and_principalBlock_inequalities_exists_hAmax`.
- `higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_and_principalBlock_inequalities_exists_hAmax`.
- `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero_and_principalBlock_inequalities_exists_hAmax`.
- `higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_det_ne_zero_and_principalBlock_inequalities_exists_hAmax`.

## 2026-06-28 Lemma 9.6 Source-Constant Denominator Wrapper

This continuation also removes an explicit denominator proof from Lemma 9.6's
printed source constant.  The existing theorem gives
`|| |L||U| ||_inf <= (1 + 2(n^2-n) rho_n) ||A||_inf` for exact no-pivot
`LUFactSpec` data once the positive max-entry denominator inside `rho_n` is
supplied.  The new wrapper derives that denominator from `det A != 0`, keeping
the exact LU certificate visible and not claiming an executable no-pivot trace.

New declaration:

- `higham9_6_absLU_infNorm_le_source_constant_of_noPivotReducedGrowthFactor_exists_hAmax`.

## 2026-06-28 Theorem 9.15 Source-Inverse Split Wrappers

This continuation removed another API-level mismatch from the formal
Barrlund--Sun support layer.  Several normalized Frobenius, split/min-factor,
and componentwise-majorant endpoints consumed the opposite inverse identities
`L L^-1 = I` and `U^-1 U = I`, even when the source-facing hypotheses more
naturally provide `L^-1 L = I` and `U U^-1 = I`.  The new adapters package the
finite-square inverse-side conversion in rectangular `rectMatMul` form, then
expose source-oriented wrappers for the `G` and `Gtilde` split endpoints and
the componentwise majorant endpoint.

These wrappers do not prove the remaining Barrlund--Sun Schur-induction or
spectral-radius theorem.  They keep the normalized min-factor or majorant
hypothesis explicit, but let callers enter those conditional endpoints from the
same inverse identities used in the printed source derivation.

A follow-up proof-completion pass added the matching source-oriented zero-factor
and one-dimensional product-smallness wrappers, so the base and degenerate
split cases no longer require callers to restate the opposite inverse
orientation.

New declarations:

- `higham9_15_rectMatMul_right_inverse_of_matrix_left_inverse`.
- `higham9_15_rectMatMul_left_inverse_of_matrix_right_inverse`.
- `higham9_15_frobenius_relative_assembly_of_inverse_normalized_bounds_opNorm_of_source_inverse_identities`.
- `higham9_15_normwise_source_bound_of_normalized_frobenius_bounds_opNorm_of_source_inverse_identities`.
- `higham9_15_normwise_source_bound_of_G_split_min_factor_bound_opNorm_of_source_inverse_identities`.
- `higham9_15_normwise_source_bound_of_G_split_min_factor_bound_opNorm_of_source_inverse_identities_product_lt`.
- `higham9_15_normwise_source_bound_of_G_split_left_zero_opNorm_of_source_inverse_identities_product_lt`.
- `higham9_15_normwise_source_bound_of_G_split_right_zero_opNorm_of_source_inverse_identities_product_lt`.
- `higham9_15_normwise_source_bound_of_G_split_opNorm_of_source_inverse_identities_fin_one_product_lt`.
- `higham9_15_normwise_source_bound_of_Gtilde_split_min_factor_bound_opNorm_of_source_inverse_identities`.
- `higham9_15_normwise_source_bound_of_Gtilde_split_min_factor_bound_opNorm_of_source_inverse_identities_product_lt`.
- `higham9_15_normwise_source_bound_of_Gtilde_split_left_zero_opNorm_of_source_inverse_identities_product_lt`.
- `higham9_15_normwise_source_bound_of_Gtilde_split_right_zero_opNorm_of_source_inverse_identities_product_lt`.
- `higham9_15_normwise_source_bound_of_Gtilde_split_opNorm_of_source_inverse_identities_fin_one_product_lt`.
- `higham9_15_componentwise_source_bound_of_normalized_majorants_of_source_inverse_identities`.
- `higham9_15_componentwise_source_bound_of_Gtilde_split_majorant_of_source_inverse_identities`.

## 2026-06-28 Growth-Factor Source Family Index

This continuation closed the remaining local growth-family definition row.
The repository already had the scalar `growthFactorEntry`, the normwise
`growthFactor`, and separate partial-, complete-, and rook-pivoting trace
growth value sets.  The new layer adds the exact no-pivot `LUFactSpec` value
family, packages no-pivot/partial/complete/rook families under one source
index, and exposes a trace-only partial/complete/rook index with a uniform
elementary `2^(n-1)` value and supremum bound.

This is a definition and navigation layer only: it does not prove Wilkinson's
sharp complete-pivoting product bound, Foster's sharper rook-pivoting bound, or
any rounded executable pivot-loop certificate.

New declarations:

- `higham9_idMatrix_LUFactSpec`.
- `higham9_noPivotingLUFactSpecGrowthValues`.
- `higham9_noPivotingLUFactSpecGrowthSup`.
- `higham9_noPivotingLUFactSpecGrowthValues_nonempty`.
- `higham9_noPivotingLUFactSpecGrowth_le_sup`.
- `higham9_PivotingGrowthKind`.
- `higham9_pivotingGrowthValues`.
- `higham9_pivotingGrowthSup`.
- `higham9_pivotingGrowthValues_nonempty`.
- `higham9_pivotingGrowth_le_sup`.
- `higham9_TracePivotingGrowthKind`.
- `higham9_tracePivotingGrowthValues`.
- `higham9_tracePivotingGrowthSup`.
- `higham9_tracePivotingGrowthValues_nonempty`.
- `higham9_tracePivotingGrowthValues_le_pow_two`.
- `higham9_tracePivotingGrowthValues_bddAbove`.
- `higham9_tracePivotingGrowth_le_sup`.
- `higham9_tracePivotingGrowthSup_le_pow_two`.

## 2026-06-27 Exact Pivot Certificate API

This continuation added exact-factor entry points for Theorem 9.3's pivoted
backward-error surfaces.  Exact `PA = LU` and `PAQ = LU` certificates now
produce zero-coefficient pivoted backward-error certificates and can also be
consumed at the standard `gamma_n` level without pretending that a rounded
pivoting loop has been constructed.  The complete-pivoting nonsingularity
construction now has a source-facing package that returns an exact `PAQ = LU`
certificate, the corresponding complete-pivoted `gamma_n` backward-error
certificate, and the usual perturbation witness.

New declarations:

- `higham9_2_permutedLUFactSpec_to_PermutedLUBackwardError_zero`.
- `higham9_2_permutedLUFactSpec_to_PermutedLUBackwardError_gamma`.
- `higham9_3_permuted_lu_backward_error_gamma_of_LUFactSpec`.
- `higham9_2_completePermutedLUFactSpec_to_CompletePermutedLUBackwardError_zero`.
- `higham9_2_completePermutedLUFactSpec_to_CompletePermutedLUBackwardError_gamma`.
- `higham9_3_complete_permuted_lu_backward_error_gamma_of_LUFactSpec`.
- `higham9_3_exists_complete_permuted_lu_backward_error_gamma_of_det_ne_zero`.

The concrete rectangular and rounded partial/complete pivot-loop
trace-to-certificate construction remains open.

## 2026-06-27 Algorithm 9.2 Literal Doolittle API

This continuation exposed the remaining compiled dense-square literal
Doolittle constructors through Chapter 9 names.  The new wrappers do not
construct the rectangular or pivoting executable traces, but they remove an API
gap between the literal rounded entry folds in `Doolittle.lean` and the Chapter
9 `DoolittleDenseLoopAbsBudgetCertificate` surface: callers can now enter the
Chapter 9 proof chain from direct literal source budgets, componentwise
work/product/numerator dominance, exact-product no-cancellation margins, or
exact-product numerator margins, before using the already existing
exact-target-gap wrapper and the `DoolittleLU`/`LUBackwardError` handoffs.

New declarations:

- `higham9_2_absBudgetCertificate_of_literal_doolittle_source_budgets`.
- `higham9_2_absBudgetCertificate_of_literal_doolittle_component_dominance`.
- `higham9_2_absBudgetCertificate_of_literal_doolittle_exact_product_margins`.
- `higham9_2_absBudgetCertificate_of_literal_doolittle_exact_product_numerator_margins`.

## 2026-06-28 Square Doolittle Direct Backward-Error Endpoints

Added direct Theorem 9.3 endpoint wrappers for the square literal Doolittle
routes:

- `higham9_3_literalDoolittle_source_budgets_backward_error`
- `higham9_3_literalDoolittle_componentDominance_backward_error`
- `higham9_3_literalDoolittle_exactProductMargins_backward_error`
- `higham9_3_literalDoolittle_exactProductNumeratorMargins_backward_error`
- `higham9_3_literalDoolittle_exactTargetGaps_backward_error`

These are thin wrappers over the existing square absolute-budget constructors
and `higham9_3_absBudgetCertificate_backward_error`, closing the same
convenience layer that was added for the rectangular surface.

## 2026-06-27 Algorithm 9.2 Rectangular Literal Fold Layer

This continuation added the missing rectangular rounded-entry layer for
Algorithm 9.2.  The exact rectangular identities (9.3) and (9.4) were already
formalized; the new declarations now expose the corresponding rounded upper
fold, rounded lower numerator fold, rounded lower division, and explicit
absolute budgets in the source `m x n`, `m >= n` shape.  The residual theorems
prove that these literal rounded rectangular updates are within the displayed
exact-product budgets for the exact rectangular Doolittle targets.  The pass
also adds rectangular dense-loop and absolute-budget certificate surfaces plus
a literal-source-budget constructor, giving future executable-loop work a
source-shaped certificate target analogous to the existing square
`DoolittleDenseLoopAbsBudgetCertificate`.  The square specialization bridge
then feeds rectangular `m = n` dense-loop and absolute-budget certificates
back into the existing square API, and the corresponding Theorem 9.3 wrappers
now expose the standard componentwise backward-error conclusion directly from
square-specialized rectangular certificates and literal source budgets.  This
is a real dependency for a future full rectangular executable trace, but it
still does not construct the whole rectangular loop schedule or connect a
pivoting implementation trace to the dense certificate.

New declarations:

- `higham9_2_rectFlDoolittleUEntry`.
- `higham9_2_rectFlDoolittleLNumerator`.
- `higham9_2_rectFlDoolittleLEntry`.
- `higham9_2_rectDoolittleUProductAbs`.
- `higham9_2_rectDoolittleUWorkAbs`.
- `higham9_2_rectDoolittleUAbsBudget`.
- `higham9_2_rectDoolittleLProductAbs`.
- `higham9_2_rectDoolittleLWorkAbs`.
- `higham9_2_rectDoolittleLNumeratorAbs`.
- `higham9_2_rectDoolittleLAbsBudget`.
- `higham9_2_rectDoolittleUAbsBudget_le_compression_of_component_dominance`.
- `higham9_2_rectDoolittleLAbsBudget_le_compression_of_component_dominance`.
- `higham9_2_rectDoolittleUWorkAbs_le_of_exact_product_margin`.
- `higham9_2_rectDoolittleUProductAbs_le_of_exact_product_margin`.
- `higham9_2_rectDoolittleLWorkAbs_le_of_exact_product_margin`.
- `higham9_2_rectDoolittleLProductAbs_le_of_exact_product_margin`.
- `higham9_2_rectDoolittleLNumeratorAbs_le_of_exact_product_numerator_margin`.
- `higham9_2_rectDoolittleUExactTarget`.
- `higham9_2_rectDoolittleLExactTarget`.
- `higham9_2_rectDoolittleUExactTargetResidualBudget`.
- `higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget`.
- `higham9_2_rectDoolittleLExactTargetEntryResidualBudget`.
- `higham9_2_rectDoolittleUExactProductMargin_of_exactTarget_gap`.
- `higham9_2_rectDoolittleLExactProductMargin_of_exactTarget_gap`.
- `higham9_2_rectDoolittleLExactProductNumeratorMargin_of_exactTarget_gap`.
- `higham9_2_RectDoolittleDenseLoopCertificate`.
- `higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate`.
- `higham9_2_rectAbsBudgetCertificate_to_rectDenseLoopCertificate`.
- `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_source_budgets`.
- `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_component_dominance`.
- `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_margins`.
- `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_numerator_margins`.
- `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_target_gaps`.
- `higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate`.
- `higham9_2_rectAbsBudgetCertificate_to_squareAbsBudgetCertificate`.
- `higham9_2_rectMatMul_eq_prefix_add_upper`.
- `higham9_2_rectMatMul_eq_prefix_add_lower`.
- `higham9_2_abs_upper_entry_le_rectMatMul_abs_sum`.
- `higham9_2_abs_lower_entry_mul_pivot_le_rectMatMul_abs_sum`.
- `higham9_2_rectFlDoolittleUEntry_residual_abs_le`.
- `higham9_2_rectFlDoolittleLNumerator_residual_abs_le`.
- `higham9_2_rectFlDoolittleLEntry_mul_pivot_sub_numerator_abs_le`.
- `higham9_2_rectFlDoolittleLEntry_residual_abs_le`.
- `higham9_3_rectDenseLoopCertificate_backward_error`.
- `higham9_3_rectAbsBudgetCertificate_backward_error`.
- `higham9_3_rectLiteralDoolittle_source_budgets_backward_error`.
- `higham9_3_rectLiteralDoolittle_componentDominance_backward_error`.
- `higham9_3_rectLiteralDoolittle_exactProductMargins_backward_error`.
- `higham9_3_rectLiteralDoolittle_exactProductNumeratorMargins_backward_error`.
- `higham9_3_rectLiteralDoolittle_exactTargetGaps_backward_error`.
- `higham9_3_rectDenseLoopCertificate_square_backward_error`.
- `higham9_3_rectAbsBudgetCertificate_square_backward_error`.
- `higham9_3_rectLiteralDoolittle_source_budgets_square_backward_error`.

## 2026-06-28 Rectangular Doolittle Component-Dominance Budget Handoff

Added the rectangular work-term vocabulary and componentwise dominance
compression lemmas feeding the rectangular literal absolute-budget certificate:

- `higham9_2_rectDoolittleUWorkAbs`
- `higham9_2_rectDoolittleLWorkAbs`
- `higham9_2_rectDoolittleUAbsBudget_le_compression_of_component_dominance`
- `higham9_2_rectDoolittleLAbsBudget_le_compression_of_component_dominance`
- `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_component_dominance`

The upper-entry lemma is the direct rectangular analogue of the square
component-dominance compression.  The lower-entry lemma keeps the scalar
coefficient condition `gamma fp k.val + fp.u + fp.u <= gamma fp n` explicit:
for rectangular rows below the final pivot, the square proof's `k + 2 <= n`
side condition is not automatic.

## 2026-06-28 Rectangular Doolittle Exact-Product Margin Handoffs

Added rectangular row-embedding wrappers around the square exact-product
margin lemmas and certificate constructors:

- `higham9_2_rectDoolittleUWorkAbs_le_of_exact_product_margin`
- `higham9_2_rectDoolittleUProductAbs_le_of_exact_product_margin`
- `higham9_2_rectDoolittleLWorkAbs_le_of_exact_product_margin`
- `higham9_2_rectDoolittleLProductAbs_le_of_exact_product_margin`
- `higham9_2_rectDoolittleLNumeratorAbs_le_of_exact_product_numerator_margin`
- `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_margins`
- `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_numerator_margins`

These wrappers let rectangular callers discharge the absolute-budget
certificate using source-visible no-cancellation margins, while preserving the
same explicit lower coefficient condition required by the rectangular
component-dominance handoff.

## 2026-06-28 Rectangular Doolittle Exact-Target Gap Handoff

Added rectangular exact-target vocabulary and the gap-to-margin handoff:

- `higham9_2_rectDoolittleUExactTarget`
- `higham9_2_rectDoolittleLExactTarget`
- `higham9_2_rectDoolittleUExactTargetResidualBudget`
- `higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget`
- `higham9_2_rectDoolittleLExactTargetEntryResidualBudget`
- `higham9_2_rectDoolittleUExactProductMargin_of_exactTarget_gap`
- `higham9_2_rectDoolittleLExactProductMargin_of_exactTarget_gap`
- `higham9_2_rectDoolittleLExactProductNumeratorMargin_of_exactTarget_gap`
- `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_target_gaps`

The exact targets are expressed with the literal `Fin k.val` prefix sums used
by the rounded Doolittle folds.  The certificate constructor now mirrors the
square exact-target-gap route in rectangular notation, still exposing the
rectangular lower coefficient compression condition.

## 2026-06-28 Rectangular Doolittle Backward-Error Handoff Variants

Added direct Theorem 9.3 backward-error endpoints for the new rectangular
literal-budget routes:

- `higham9_3_rectLiteralDoolittle_componentDominance_backward_error`
- `higham9_3_rectLiteralDoolittle_exactProductMargins_backward_error`
- `higham9_3_rectLiteralDoolittle_exactProductNumeratorMargins_backward_error`
- `higham9_3_rectLiteralDoolittle_exactTargetGaps_backward_error`

These are thin wrappers over the rectangular absolute-budget certificate
constructors and `higham9_3_rectAbsBudgetCertificate_backward_error`, so callers
can enter Theorem 9.3 directly from component-dominance, exact-product, or
exact-target gap hypotheses.

## 2026-06-28 Rectangular Doolittle Backward-Error Endpoint

Added a genuine rectangular `m x n` componentwise backward-error theorem for
the existing rectangular Doolittle certificate surface:

- `higham9_2_rectMatMul_eq_prefix_add_upper`
- `higham9_2_rectMatMul_eq_prefix_add_lower`
- `higham9_2_abs_upper_entry_le_rectMatMul_abs_sum`
- `higham9_2_abs_lower_entry_mul_pivot_le_rectMatMul_abs_sum`
- `higham9_3_rectDenseLoopCertificate_backward_error`
- `higham9_3_rectAbsBudgetCertificate_backward_error`
- `higham9_3_rectLiteralDoolittle_source_budgets_backward_error`

The proof splits each rectangular entry into the upper or lower Doolittle
case, rewrites the rectangular product as the corresponding prefix dot plus
the stored entry, and then lifts the certificate residual-compression field to
the full absolute product sum. This closes the certificate-to-error endpoint
in rectangular source notation; it still does not construct the concrete
rectangular executable schedule.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the rectangular backward-error endpoint |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the rectangular backward-error endpoint |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_rect_backward_error.out 2>&1` | PASS after adding lookup checks for the seven rectangular backward-error/support declarations; redirected output has 57338 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the seven rectangular backward-error/support declarations | PASS; all seven report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the rectangular backward-error update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-27 Theorem 9.5 Pivoted Literal Source-Budget Wrappers

This continuation added literal-source-budget entry points for the row-pivoted
and complete-pivoted Wilkinson normwise source bounds.  The previous public
surface accepted a dense-loop certificate, an absolute-budget certificate, or
an exact `PA = LU`/`PAQ = LU` certificate.  The new wrappers accept the literal
rounded Doolittle entry equations and budget-dominance hypotheses directly for
the permuted source matrix, then route through the existing absolute-budget and
pivoted backward-error adapters.  They do not construct the GEPP/GEPQ trace or
the dense loop from an implementation trace; those obligations remain visible.

New declarations:

- `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_literalSourceBudgets`.
- `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_literalSourceBudgets`.

## 2026-06-27 Theorem 9.5 Pivoted Literal Dominance/Margin Wrappers

This continuation exposed the remaining compiled dense-square literal
Doolittle absolute-budget constructors at the row-pivoted `PA` and
complete-pivoted `PAQ` Wilkinson normwise source-bound endpoints.  Callers can
now enter Theorem 9.5 from componentwise work/product/numerator dominance,
exact-product no-cancellation margins, exact-product numerator margins, or
explicit exact-target gaps for the permuted source matrix.  These wrappers
route through the existing absolute-budget and pivoted backward-error adapters;
they still do not construct the GEPP/GEPQ implementation trace or prove that a
concrete pivoting loop produces the visible dense-loop certificate.

New declarations:

- `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_componentDominance`.
- `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_exactProductMargins`.
- `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_exactProductNumeratorMargins`.
- `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_exactTargetGaps`.
- `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_componentDominance`.
- `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_exactProductMargins`.
- `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_exactProductNumeratorMargins`.
- `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_exactTargetGaps`.

## 2026-06-27 Complete-Pivot Trace-To-Solve Exact Wrapper

This continuation strengthened the recursive complete-pivoting trace support.
The prior trace-to-cumulative-certificate theorem transferred the certificate
`U` max-entry norm to the recursive trace `U`, but it did not expose the
unit-lower multiplier bound needed by the solve-level Wilkinson theorem.  The
new strengthened trace theorem carries `|L_ij| <= 1` by induction: complete
pivoting bounds the first-column multipliers by one, and the recursive
certificate supplies the trailing-block bound.  A general `PAQ = LU` growth
bridge then separates the solve theorem from the particular trace used to
prove growth, and the trace-derived wrapper constructs a complete-pivoted exact
certificate and Wilkinson perturbation witness at the elementary `2^(n-1)`
growth strength.  This still does not prove Wilkinson's sharper complete
pivoting product bound, and it does not construct a rounded dense-loop
certificate.

New declarations:

- `higham9_2_rowColPermutedMatrix_det_ne_zero`.
- `higham9_8_CompletePivotGECPUTrace_exists_CompletePermutedLUFactSpec_L_bound_maxEntryNorm_le`.
- `higham9_5_wilkinson_source_bound_of_CompletePermutedLUFactSpec_growth`.
- `higham9_5_wilkinson_source_bound_exists_of_CompletePivotGECPUTrace`.

## 2026-06-27 Rook-Pivot Trace-To-Solve Exact Wrapper

This continuation added the analogous exact solve bridge for recursive
rook-pivoting traces.  The new trace-to-certificate theorem constructs a
complete-permuted exact LU certificate from a rook trace, records the visible
`|L_ij| <= 1` multiplier bound from the rook first-column multiplier lemma, and
keeps the certificate `U` max-entry norm bounded by the trace `U`.  The
solve-level wrapper then reuses the generic `PAQ = LU` growth bridge and the
elementary rook trace bound `rho <= 2^(n-1)` to produce a Wilkinson normwise
perturbation witness.  This closes an exact trace-to-solve API gap for rook
pivoting, but it still does not prove Foster's sharper product bound or a
rounded dense-loop implementation certificate.

New declarations:

- `higham9_16_RookPivotGEUTrace_exists_CompletePermutedLUFactSpec_L_bound_maxEntryNorm_le`.
- `higham9_16_wilkinson_source_bound_exists_of_RookPivotGEUTrace`.

## 2026-06-27 Partial-Pivot Trace-To-Solve Exact Wrapper

This continuation added the row-pivoted analogue of the complete- and
rook-pivoting exact solve bridges.  A new trailing-row-permutation Schur
lemma supports a cumulative `PA = LU` certificate construction from a
recursive GEPP `U` trace.  The construction records the visible
`|L_ij| <= 1` multiplier bound from the partial-pivot column maximum, and
keeps the certificate `U` max-entry norm bounded by the trace `U`.  The
solve-level wrapper then reuses a generic exact `PA = LU` growth bridge and
the elementary GEPP trace bound `rho <= 2^(n-1)` to produce the Theorem 9.5
Wilkinson normwise perturbation witness.  This removes the exact partial trace
to solve API gap; the rounded GEPP loop-to-dense-loop/backward-error
certificate construction remains open.

New declarations:

- `higham9_7_luFirstSchurComplement_trailingRowPerm`.
- `higham9_5_wilkinson_source_bound_of_PermutedLUFactSpec_growth`.
- `higham9_7_PartialPivotGEPPUTrace_exists_PermutedLUFactSpec_L_bound_maxEntryNorm_le`.
- `higham9_5_wilkinson_source_bound_exists_of_PartialPivotGEPPUTrace`.

## 2026-06-27 Pivoted Det-Only Exact Solve Wrappers

This continuation also added source-facing wrappers that discharge the explicit
recursive trace witnesses for partial, complete, and rook pivoting from the
single nonsingularity hypothesis `det A != 0`.  These wrappers compose the
existing trace-existence theorems with the exact trace-to-solve bridges above,
so callers can enter the elementary `2^(n-1)` Wilkinson perturbation surfaces
directly from a nonsingular source matrix.  The sharp complete-/rook-pivoting
product bounds and rounded pivot-loop certificates remain open.

New declarations:

- `higham9_5_wilkinson_source_bound_exists_of_PartialPivotGEPPUTrace_of_det_ne_zero`.
- `higham9_5_wilkinson_source_bound_exists_of_CompletePivotGECPUTrace_of_det_ne_zero`.
- `higham9_16_wilkinson_source_bound_exists_of_RookPivotGEUTrace_of_det_ne_zero`.

## 2026-06-27 Upper-Hessenberg Exact Trace-To-Solve Wrapper

This continuation connected the exact upper-Hessenberg GEPP trace layer back to
the row-pivoted exact solve surface.  The new trace-forgetting lemma shows that
an upper-Hessenberg GEPP `U` trace is an ordinary partial-pivoting GEPP trace,
so it can reuse the cumulative `PA = LU` certificate construction with
unit-bounded multipliers.  The Hessenberg-specific wrapper keeps the sharper
trace growth bound `rho <= n` instead of falling back to `2^(n-1)`, producing a
source-facing Wilkinson normwise perturbation witness for every nonsingular
upper-Hessenberg input.  This is a normwise exact-trace wrapper; the broader
complex/algorithmic and componentwise rounded Hessenberg coverage remains
open.

New declarations:

- `higham9_10_HessenbergGEPPUTrace_to_PartialPivotGEPPUTrace`.
- `higham9_10_wilkinson_source_bound_exists_of_HessenbergGEPPUTrace`.
- `higham9_10_wilkinson_source_bound_exists_of_det_ne_zero`.

## 2026-06-27 Theorem 9.14 SPD Tridiagonal Recurrence Wrappers

This continuation added source-data recurrence entry points for the SPD
positive-`D L^T` tridiagonal branch.  The previous API had the final
model-consuming `h(u)|A|` theorem and the actual-triangular-solve `f(u)|A|`
theorem for arbitrary visible tridiagonal factors.  The new wrappers specialize
those results to `TridiagData` and the exact recurrence (9.19), so callers can
stay at the source-data layer instead of manually assembling
`tridiag_L_matrix`, `tridiag_U_matrix`, the structural `IsTridiagLU`
certificate, and the exact product identity.  This is still not the rounded
tridiagonal executable factorization theorem; the recurrence, positive-`D L^T`
certificate, and source perturbation models remain visible hypotheses.

New declarations:

- `higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_recurrence`.
- `higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_recurrence`.
- `higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_spd_recurrence`.

## 2026-06-27 Problem 9.3, Equation (9.26), Equation (9.27), and Theorem 9.15 Support

This continuation closed the selected Problem 9.3 field-of-values route and the
source Holder wrapper for equation (9.26). It also added the compiled
`G = L^{-1} ΔA U^{-1}` Frobenius/operator-2 norm-product bridges used by the
right-hand side of equation (9.27), and surfaced the local componentwise forward
perturbation coefficient `2α + α^2` as a Chapter 9 wrapper. A later step in
this pass also closed the source condition-number consequence
`κ₂(A) <= χ(A) <= min{κ₂(L), κ₂(U)}κ₂(A)` in certificate and exact-product
forms. A subsequent step formalized the normalized algebraic identities
`I + G = (I + L^{-1}ΔL)(I + ΔU U^{-1})` and
`I - Gtilde = (I - Lhat^{-1}ΔL)(I - ΔU Uhat^{-1})` as matrix theorems.
It also added local `stril`/`triu` projections and proved the corresponding
normalized split equations `X = stril(G - XY)`, `Y = triu(G - XY)` and
`X = stril(Gtilde + XY)`, `Y = triu(Gtilde + XY)` under explicit
strict-lower/upper triangular hypotheses. The projection maps are now proved
Frobenius nonexpansive, yielding immediate `||X||_F` and `||Y||_F` bounds by
the residual split matrices `G - XY` and `Gtilde + XY`; the local triangle and
Frobenius submultiplicativity step is also closed, giving the one-step
nonlinear bound `max(||X||_F, ||Y||_F) <= ||G||_F + ||X||_F ||Y||_F` and its
`Gtilde` analogue. The scalar denominator handoff from a linearized step
`q <= g + eta*q`, `eta < 1`, to `q <= g/(1-eta)` is closed separately, so the
remaining normwise gap is the Schur-induction step that supplies the needed
linearized inequality. The source-level handoff from that exact linearized
inequality to Higham's printed operator-denominator bound is now packaged by
`higham9_15_normwise_source_bound_of_normalized_linear_step_opNorm_of_inverse_identities`.
The componentwise `Gtilde` route now has the matching linear-step ratio and
printed-denominator source wrappers; they keep the normalized linear inequality
explicit and do not claim the missing Schur-induction theorem.
The normalized linear-step wrappers now also have source-oriented inverse
variants that assume only `L^{-1}L = I` and `UU^{-1} = I`, deriving the
opposite inverse identities internally before applying the printed
operator-denominator assembly.
A later step in this pass also proves the entrywise
projected majorants from the split equations: `|X|` and `|Y|` are bounded by
the strict-lower/upper projections of `|G| + |X||Y|` in the normwise route and
of `|Gtilde| + |X||Y|` in the componentwise route. A conditional scalar bridge
is closed as well: if the smaller of `||X||_F` and `||Y||_F` is already
bounded by the small operator parameter, the nonlinear one-step inequality
implies the displayed ratio bound. This is support for the Barrlund--Sun
induction; it does not prove that the one-factor bound follows from
`||G||_2 < 1`.
The Frobenius-denominator relative assembly step is closed as an auxiliary
handoff: from `ΔL = L X`, `ΔU = Y U`, and normalized Frobenius bounds on `X`
and `Y`, the max bound with denominators `||L||_F` and `||U||_F` follows by
Frobenius submultiplicativity. A source re-audit of the printed Theorem 9.15
confirmed that the theorem itself normalizes by `||L||_2` and `||U||_2`; this
pass therefore adds source-correct operator-denominator assembly wrappers using
the mixed operator/Frobenius product estimates.
The componentwise original-variable assembly step is closed too: from
`ΔL = Lhat X`, `ΔU = Y Uhat`, and entrywise envelopes for normalized
perturbations `X` and `Y`, the source envelopes
`|ΔL| <= |Lhat| B_L` and `|ΔU| <= B_U |Uhat|` follow by entrywise
absolute-product estimates.
The opposite-inverse identities now bridge those assembly wrappers directly to
the normalized perturbations `L^{-1}ΔL`, `ΔU U^{-1}`,
`Lhat^{-1}ΔL`, and `ΔU Uhat^{-1}`. On a nonempty square dimension, the
printed operator-denominator wrappers now derive `0 < ||L||_2` and
`0 < ||U||_2` from the displayed inverse identities rather than requiring
those positive denominator facts as separate source hypotheses.
The equation (9.27) denominator algebra is now closed: exact `G` Frobenius and
operator-2 bounds are converted to the source ratio
`||G||_F/(1-||G||_2)` bounded by the corresponding product ratio.
A source-facing conditional normwise wrapper with the printed operator
denominators now reduces the remaining normwise theorem to exactly the
normalized Frobenius bounds for `L^{-1}ΔL` and `ΔU U^{-1}`. The older
Frobenius-denominator conditional wrapper remains available only as an
auxiliary compatibility result; the nonempty-dimension printed wrapper derives
the positive denominator side conditions from the inverse identities.
A matching conditional componentwise wrapper reduces the remaining
spectral-radius theorem to normalized strict-lower/upper majorants.
The factorization-level wrappers now derive the normalized `I + G` and
`I - Gtilde` split identities from the original exact perturbed factorization
equations. They also provide source-oriented variants that assume only
`L^{-1}L = I` and `UU^{-1} = I`, deriving the opposite inverse identities by
finite-square inverse-side adapters before applying the conditional
normwise/componentwise endpoints.
The full Barrlund--Sun normwise/spectral Theorem 9.15 remains open; the new
(9.27), componentwise forward, `χ(A)`, normalized-identity, and split-equation
material plus operator-denominator Frobenius/componentwise assembly is support
infrastructure, not a claim of the full nonlinear perturbation theorem.

Oracle/GPT-5.5 Pro browser consultation was used for the remaining hard
Barrlund--Sun route. The safe-export packet contained only the theorem target
and local proof obligations, not repository source or book text. The returned
route isolates two remaining major formalization lemmas: a normalized
Frobenius Schur-induction theorem for `I + E = (I + X)(I + Y)` under
`||E||₂ < 1`, and a nonnegative Schur-majorant/spectral-radius induction for
`I - E = (I - X)(I - Y)` under `ρ(C) < 1`.

This pass also closed equation (9.23)'s source-facing forward-error wrapper:
the exact denominator form is proved from the Chapter 7 relative infinity-norm
theorem with unperturbed right-hand side, and the displayed
`3 n u cond(A) cond(U) + O(u^2)` form is recorded via the repository
`FirstOrderLe` vocabulary from a visible row-wise backward-error coefficient
hypothesis `eta <= 3 n u cond(U)`.

New declarations:

- `higham_problem9_3_complexOfReal`,
  `higham_problem9_3_zeroNotInFieldOfValues`,
  `higham_problem9_3_properLeadingPrincipalBlock_det_ne_zero_of_zeroNotInFieldOfValues`,
  `higham_problem9_3_lu_exists_unique_of_zeroNotInFieldOfValues`.
- `higham9_26_prefixLpNorm`,
  `higham9_26_holder_prefix_dot_abs_le`,
  `higham9_26_stage_entry_abs_le`,
  `higham9_26_stage_entry_abs_le_of_uniform_bounds`.
- `higham9_27_GMatrix`,
  `higham9_27_GMatrix_frobenius_le`,
  `higham9_27_GMatrix_opNorm2Le`,
  `higham9_15_ratio_le_of_norm_bounds`,
  `higham9_27_GMatrix_ratio_le_product_ratio`.
- `higham9_15_lu_perturbation_forward_bound`.
- `higham9_15_chi`,
  `higham9_15_chi_nonneg`,
  `higham9_15_rectMatMul_opNorm2Le`,
  `higham9_15_kappa2_le_chi_of_inverse_product_bound`,
  `higham9_15_chi_le_kappa2L_mul_kappa2A_of_Uinv_bound`,
  `higham9_15_chi_le_kappa2U_mul_kappa2A_of_Linv_bound`,
  `higham9_15_chi_condition_chain_of_inverse_product_bounds`,
  `higham9_15_chi_condition_chain_min_of_inverse_product_bounds`,
  `higham9_15_chi_condition_chain_of_inverse_products`,
  `higham9_15_chi_condition_chain_min_of_inverse_products`.
- `higham9_15_normalized_G_factorization_matrix`,
  `higham9_15_normalized_Gtilde_factorization_matrix`.
- `higham9_15_strilPart`,
  `higham9_15_triuPart`,
  `higham9_15_frobNormRect_strilPart_le`,
  `higham9_15_frobNormRect_triuPart_le`,
  `higham9_15_abs_strilPart_le_strilPart_of_abs_le`,
  `higham9_15_abs_triuPart_le_triuPart_of_abs_le`,
  `higham9_15_strilPart_mono`,
  `higham9_15_triuPart_mono`,
  `higham9_15_abs_matrix_mul_le_abs_mul_abs`,
  `higham9_15_strilPart_add_strictLower_upper`,
  `higham9_15_triuPart_add_strictLower_upper`,
  `higham9_15_normalized_G_split_matrix`,
  `higham9_15_normalized_G_split_frobNorm_bounds`,
  `higham9_15_normalized_G_split_componentwise_majorants`,
  `higham9_15_normalized_G_split_frobNorm_step_bound`,
  `higham9_15_scalar_bound_of_le_add_mul`,
  `higham9_15_normalized_G_frobNorm_ratio_bound_of_linear_step`,
  `higham9_15_mul_le_eta_mul_max_of_min_le`,
  `higham9_15_normalized_G_frobNorm_ratio_bound_of_min_factor_bound`,
  `higham9_15_normalized_Gtilde_split_matrix`,
  `higham9_15_normalized_Gtilde_split_frobNorm_bounds`,
  `higham9_15_normalized_Gtilde_split_componentwise_majorants`,
  `higham9_15_normalized_Gtilde_split_frobNorm_step_bound`,
  `higham9_15_normalized_Gtilde_frobNorm_ratio_bound_of_min_factor_bound`.
- `higham9_15_frobenius_relative_lower_of_left_factor`,
  `higham9_15_frobenius_relative_upper_of_right_factor`,
  `higham9_15_frobenius_relative_assembly_bound`,
  `higham9_15_frobenius_relative_lower_of_left_factor_opNorm`,
  `higham9_15_frobenius_relative_upper_of_right_factor_opNorm`,
  `higham9_15_frobenius_relative_assembly_bound_opNorm`.
- `higham9_15_abs_rectMatMul_left_le`,
  `higham9_15_abs_rectMatMul_right_le`,
  `higham9_15_componentwise_original_assembly`.
- `higham9_15_deltaL_eq_L_mul_normalized_of_right_inverse`,
  `higham9_15_deltaU_eq_normalized_mul_U_of_left_inverse`,
  `higham9_15_opNorm2_pos_of_rectMatMul_right_inverse`,
  `higham9_15_opNorm2_pos_of_rectMatMul_left_inverse`,
  `higham9_15_frobenius_relative_assembly_of_inverse_normalized_bounds`,
  `higham9_15_frobenius_relative_assembly_of_inverse_normalized_bounds_opNorm`,
  `higham9_15_frobenius_relative_assembly_of_inverse_normalized_bounds_opNorm_of_inverse_identities`,
  `higham9_15_componentwise_original_assembly_of_inverse_normalized_bounds`.
- `higham9_15_normwise_source_bound_of_normalized_frobenius_bounds`.
- `higham9_15_normwise_source_bound_of_normalized_frobenius_bounds_opNorm`.
- `higham9_15_normwise_source_bound_of_normalized_frobenius_bounds_opNorm_of_inverse_identities`.
- `higham9_15_normwise_source_bound_of_G_split_min_factor_bound_opNorm_of_inverse_identities`.
- `higham9_15_matrix_right_inverse_of_matrix_left_inverse`.
- `higham9_15_matrix_left_inverse_of_matrix_right_inverse`.
- `higham9_15_normwise_source_bound_of_normalized_linear_step_opNorm_of_inverse_identities`.
- `higham9_15_normalized_Gtilde_frobNorm_ratio_bound_of_linear_step`.
- `higham9_15_normwise_source_bound_of_Gtilde_normalized_linear_step_opNorm_of_inverse_identities`.
- `higham9_15_normwise_source_bound_of_Gtilde_normalized_linear_step_opNorm_of_inverse_identities_product_lt`.
- `higham9_15_normwise_source_bound_of_normalized_linear_step_opNorm_of_source_inverse_identities`.
- `higham9_15_normwise_source_bound_of_normalized_linear_step_opNorm_of_source_inverse_identities_product_lt`.
- `higham9_15_normwise_source_bound_of_Gtilde_normalized_linear_step_opNorm_of_source_inverse_identities`.
- `higham9_15_normwise_source_bound_of_Gtilde_normalized_linear_step_opNorm_of_source_inverse_identities_product_lt`.
- `higham9_15_normwise_source_bound_of_factorization_min_factor_bound_opNorm_of_matrix_inverse_identities`.
- `higham9_15_normwise_source_bound_of_factorization_min_factor_bound_opNorm`.
- `higham9_15_componentwise_source_bound_of_normalized_majorants`.
- `higham9_15_componentwise_source_bound_of_Gtilde_split_majorant_of_inverse_identities`.
- `higham9_15_componentwise_source_bound_of_factorization_Gtilde_majorant_of_matrix_inverse_identities`.
- `higham9_15_componentwise_source_bound_of_factorization_Gtilde_majorant`.
- `higham9_23_condSkeel_nonneg`,
  `higham9_23_forward_error_exact_condSkeel`,
  `higham9_23_firstOrderLe_of_backward_error_coeff`,
  `higham9_23_forward_error_firstOrder_cond_product`.

## 2026-06-27 Equations (9.20)--(9.22) Source Models

This continuation made the printed perturbation surfaces for equations (9.20)
and (9.21) explicit as source model predicates, proved the equation (9.22)
`f(u)` aggregation from those models, and added model-consuming `h(u)|A|`
wrappers for the final source scalar step. It also closes that final scalar
step for SPD positive-`D L^T`, nonnegative-LU, M-matrix LU, sign-equivalent,
and total-nonnegative/nonsingular optimal-growth surfaces once the explicit
source perturbation models are supplied. These declarations do not claim that
every rounded tridiagonal recurrence or special matrix class produces the
models; that executable/source-class coverage remains open under Theorem 9.14.
This pass also added the constant-growth equation-(9.22) source-model bridge:
if a structural theorem supplies `|Lhat||Uhat| <= c|A|`, the explicit
equation (9.20)/(9.21) models imply the bound `c f(u)|A|`.  The new
column- and direct-row diagonally-dominant source-data wrappers instantiate
this with the local Theorem 9.13 exact-LU packages and `c = 3`; they still
leave the rounded perturbation models as visible hypotheses.
The same `3 f(u)|A|` bridge is now exposed for the explicit `TridiagData`
builder and equation-(9.19) exact-recurrence variants, matching the existing
absorbed `3 gamma_6` builder/recurrence wrappers.
It is also exposed for ordinary exact `LUFactSpec` certificates under the same
column- or row-dominant tridiagonal hypotheses.
This continuation additionally added coefficient-dominance production bridges:
`higham9_20_tridiag_lu_perturbation_model_of_LUBackwardError_le` turns an
existing `LUBackwardError` certificate into the equation (9.20) source model
when its coefficient is bounded by `u`, and
`higham9_21_tridiag_solve_perturbation_model_of_fl_triangular_solves_gamma_le`
turns the actual `fl_forwardSub`/`fl_backSub` solves into the equation (9.21)
model when `gamma fp n <= u`.  The composed wrappers
`higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le`
and `higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma`
then feed those produced models through the constant-growth `f(u)` bridge.
They reduce explicit model hypotheses for certificate-based paths, but they do
not close the sharper printed all-class rounded tridiagonal recurrence proof.
The exact-`LUFactSpec` column- and row-dominant tridiagonal wrappers now also
have certificate-producing variants,
`higham9_14_tridiag_colDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves`
and
`higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves`,
which combine coefficient-dominated `LUBackwardError`, actual triangular
solves, and the Theorem 9.13 `3|A|` growth comparison.
The same production route is exposed for explicit `TridiagData` builder and
equation-(9.19) exact-recurrence surfaces via the
`*_from_builders_LUBackwardError_fl_triangular_solves` and
`*_from_recurrence_LUBackwardError_fl_triangular_solves` declarations.
This continuation also adds `LUFactSpec.to_LUBackwardError_zero`, a generic
exact-LU-to-zero-backward-error bridge, and uses it to expose exact-factor plus
actual triangular-solve source-data wrappers for the column- and row-dominant
tridiagonal packages. These wrappers remove the explicit `(9.20)`/`(9.21)`
model hypotheses only for exact LU factors; they do not model a rounded LU
factorization path.
The explicit tridiagonal builder exact-product certificate now also has an
ordinary `LUFactSpec` bridge via
`higham9_19_tridiag_LUFactSpec_of_exact_product` and
`higham9_19_tridiag_LUFactSpec_of_recurrence`.  Using that bridge, the
builder and equation-(9.19) exact-recurrence surfaces have exact-factor plus
actual triangular-solve wrappers with no separate `LUBackwardError` certificate
hypothesis.  These remain exact-factor endpoints and still assume the `U`
diagonal nonzero side condition required by the triangular solve model.

New declarations:

- `higham9_20_tridiag_lu_perturbation_model`.
- `higham9_21_tridiag_solve_perturbation_model`.
- `higham9_22_source_f_bound_of_9_20_9_21_models`.
- `higham9_14_source_h_bound_of_9_20_9_21_models_absLUhat_bound`.
- `higham9_14_source_h_bound_of_9_20_9_21_models_absLUhat_mul_one_sub_bound`.
- `higham9_14_source_h_bound_of_absLU_le_absA_and_9_20_9_21_models`.
- `higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_models`.
- `higham9_14_nonnegative_lu_source_h_bound_of_models`.
- `higham9_14_mmatrix_lu_source_h_bound_of_models`.
- `higham9_14_sign_equiv_source_h_bound_of_models`.
- `higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves`.
- `higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_spd`.
- `higham9_14_nonnegative_lu_source_f_bound_actual_triangular_solves`.
- `higham9_14_mmatrix_lu_source_f_bound_actual_triangular_solves`.
- `higham9_14_sign_equiv_source_f_bound_actual_triangular_solves`.
- `higham9_14_totalNonnegative_exists_source_h_bound_of_models`.
- `higham9_14_totalNonnegative_exists_source_f_bound_actual_triangular_solves`.
- `higham9_14_colDiagDom_exists_LUFactSpec_fu_bound`,
  `higham9_14_rowDiagDom_exists_LUFactSpec_fu_bound`.
- `higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models`.
- `higham9_14_tridiag_colDiagDom_source_f_bound_from_builders`,
  `higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders`.
- `higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence`,
  `higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence`.
- `higham9_14_tridiag_colDiagDom_source_f_bound_from_LUFactSpec`,
  `higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUFactSpec`.
- `higham9_14_colDiagDom_exists_LUFactSpec_source_f_bound_of_models`,
  `higham9_14_rowDiagDom_exists_LUFactSpec_source_f_bound_of_models`.
- `LUFactSpec.to_LUBackwardError_zero`.
- `higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le`.
- `higham9_14_colDiagDom_exists_LUFactSpec_source_f_bound_actual_triangular_solves`,
  `higham9_14_rowDiagDom_exists_LUFactSpec_source_f_bound_actual_triangular_solves`.
- `higham9_19_tridiag_LUFactSpec_of_exact_product`,
  `higham9_19_tridiag_LUFactSpec_of_recurrence`.
- `higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves`,
  `higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves`,
  `higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence_LUFactSpec_fl_triangular_solves`,
  `higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence_LUFactSpec_fl_triangular_solves`.

## 2026-06-27 Pivoted Dense-Loop Certificate Bridges

This continuation also tightened the Algorithm 9.2/Theorem 9.5 interface:
dense Doolittle certificates for the already permuted matrices `PA` and `PAQ`
now produce the existing pivoted and complete-pivoted backward-error
certificates. The source-facing Wilkinson normwise wrappers can therefore
consume a dense-loop or absolute-budget certificate directly. This closes a
certificate-adapter layer only; it still does not construct the partial- or
complete-pivoting trace from a concrete executable GEPP/GEPQ loop.

New declarations:

- `higham9_2_permutedDenseLoopCertificate_to_PermutedLUBackwardError`,
  `higham9_2_permutedAbsBudgetCertificate_to_PermutedLUBackwardError`.
- `higham9_2_completePermutedDenseLoopCertificate_to_CompletePermutedLUBackwardError`,
  `higham9_2_completePermutedAbsBudgetCertificate_to_CompletePermutedLUBackwardError`.
- `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_denseLoop`,
  `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_absBudget`.
- `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_denseLoop`,
  `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_absBudget`.

## 2026-06-27 Exact Theorem 9.5 Certificate Bridges

This continuation added exact-certificate entry points for the Theorem 9.5
Wilkinson source-bound wrappers.  Exact `PA = LU` and `PAQ = LU` certificates
now weaken zero residuals to `gamma_n` and feed the row-pivoted and
complete-pivoted source-bound surfaces directly.  This closes another
certificate-adapter layer only; it still does not construct the rounded
partial- or complete-pivoting traces from a concrete executable GEPP/GEPQ loop.

New declarations:

- `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_LUFactSpec`.
- `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_LUFactSpec`.

## 2026-06-24 Full Permutation Norm-Preservation Design

| Source row | Old status | Re-audit result | Existing declaration/import | Intended Lean target | Dependencies | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| Equations (9.2a)--(9.2b), row/column permutation certificate norm bookkeeping | `PROVE-NOW-SPLIT` dependency endpoint | Row-only norm preservation is closed for the pivoted Wilkinson adapter, but the complete-pivoting `PAQ` certificate surface still lacks reusable column and row/column max-entry/infinity-norm preservation wrappers | `higham9_2_colPermutedMatrix`, `higham9_2_rowColPermutedMatrix`, `higham9_2_rowPermutedMatrix_maxEntryNorm`, `higham9_2_rowPermutedMatrix_infNorm`; module `LeanFpAnalysis.FP.Algorithms.HighamChapter9` | `higham9_2_colPermutedMatrix_maxEntryNorm`, `higham9_2_colPermutedMatrix_infNorm`, `higham9_2_rowColPermutedMatrix_maxEntryNorm`, and `higham9_2_rowColPermutedMatrix_infNorm` | `IsPermutation`, `Equiv.ofBijective`, `maxEntryNorm`, `infNorm`, row-sum invariance under column reindexing, and the row-permutation preservation lemmas | Implement thin proved wrappers, add lookup/example checks, and keep Wilkinson's sharp complete-pivoting product bound and Foster's rook-pivoting product bound open |

Result: implemented in this continuation; the full row/column permutation
norm-preservation endpoint is closed. Wilkinson's sharp complete-pivoting
product bound and Foster's rook-pivoting product bound remain open.

## 2026-06-24 Complete-Pivoted Explicit-Certificate Normwise Bound Design

| Source row | Old status | Re-audit result | Existing declaration/import | Intended Lean target | Dependencies | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| Theorem 9.4 / Theorem 9.5 complete-pivoted explicit-certificate normwise source bound | `PROVE-NOW-SPLIT` dependency endpoint; sharp complete-pivoting product bound still open | The current branch has complete-pivoted backward-error certificates, the complete-pivoting `U` trace, elementary trace-level `rho <= 2^(n-1)`, and full row/column norm preservation. It lacks the source-facing wrapper that unpermutes both rows and columns and states the normwise bound over the original matrix norm. | `higham9_2_CompletePermutedLUBackwardError`, `higham9_2_completePermutedLUBackwardError_to_LUBackwardError`, `higham9_8_CompletePivotGECPUTrace`, `higham9_8_CompletePivotGECPUTrace_growthFactorEntry_le_pow_two`, `higham9_2_rowColPermutedMatrix_maxEntryNorm`, `higham9_2_rowColPermutedMatrix_infNorm`, and `higham9_5_wilkinson_source_bound_of_entry_growth`; module `LeanFpAnalysis.FP.Algorithms.HighamChapter9` | `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace` | Explicit complete-pivoting `U` trace, visible `PAQ` backward-error certificate, nonzero `U` diagonal, unit multiplier bound, `gammaValid`, row/column unpermutation of the perturbation, and the elementary complete-pivoting trace bound | Implement the source-facing wrapper, add lookup/example checks, and keep Wilkinson's sharp complete-pivoting product bound (9.14) open |

Result: implemented in this continuation; the complete-pivoted explicit
certificate normwise source wrapper is closed. Wilkinson's sharp
complete-pivoting product bound (9.14), Foster's rook-pivoting product bound
(9.16), and the computed GEPP trace/certificate link remain open.

## 2026-06-24 Rook Trace Growth-Value Endpoint Design

| Source row | Old status | Re-audit result | Existing declaration/import | Intended Lean target | Dependencies | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| Equation (9.16), recursive rook-pivoting `U` trace support and source-facing growth-family endpoint | `PROVE-NOW-SPLIT` partial endpoint | Trace existence and the elementary `rho <= 2^(n-1)` theorem are already closed; the live API lacks the same value-set/supremum navigation surface used for partial and complete pivoting | `higham9_16_RookPivotGEUTrace`, `higham9_16_RookPivotGEUTrace_growthFactorEntry_le_pow_two`, `higham9_16_exists_RookPivotGEUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero`; module `LeanFpAnalysis.FP.Algorithms.HighamChapter9` | `higham9_16_rookPivotingUTraceGrowthValues`, `higham9_16_rookPivotingUTraceGrowthSup`, `higham9_16_rookPivotingUTraceGrowthValues_le_pow_two`, `higham9_16_rookPivotingUTraceGrowthValues_bddAbove`, and `higham9_16_rookPivotingUTraceGrowth_le_sup` | Existing rook trace predicate, `growthFactorEntry`, `sSup`, `BddAbove`, and `le_csSup` | Implement thin proved wrappers, add lookup/example checks, and keep Foster's sharper product-bound theorem open |

Result: implemented and verified in this continuation; Foster's sharper
rook-pivoting product-bound theorem remains open.

## 2026-06-24 Rook Trace Supremum Endpoint Design

| Source row | Old status | Re-audit result | Existing declaration/import | Intended Lean target | Dependencies | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| Equation (9.16), rook-pivoting trace growth-family supremum endpoint | `PROVE-NOW-SPLIT` partial endpoint | The current branch already has the rook-pivoting trace value set, direct elementary value upper bound, boundedness, and `le_sup` adapter, but the live API lacks the positive-dimensional nonemptiness wrapper and source-shaped elementary supremum upper bound analogous to the partial- and complete-pivoting endpoints | `higham9_16_rookPivotingUTraceGrowthValues`, `higham9_16_rookPivotingUTraceGrowthSup`, `higham9_16_rookPivotingUTraceGrowthValues_le_pow_two`, `higham9_16_rookPivotingUTraceGrowthValues_bddAbove`, `higham9_16_RookPivotGEUTrace_growthFactorEntry_le_pow_two`, `higham9_16_exists_RookPivotGEUTrace_of_det_ne_zero`; module `LeanFpAnalysis.FP.Algorithms.HighamChapter9` | `higham9_16_rookPivotingUTraceGrowthValues_nonempty` and `higham9_16_rookPivotingUTraceGrowthSup_le_pow_two` | Existing rook-pivoting trace existence for nonsingular matrices, the Wilkinson matrix nonsingularity witness, `growthFactorEntry`, `sSup`, `csSup_le`, and the elementary rook-pivoting trace upper bound | Implement thin proved wrappers, add lookup/example checks, and keep Foster's sharper rook-pivoting product bound open |

Result: implemented and full verification passed in this continuation;
Foster's sharper rook-pivoting product bound remains open.

## 2026-06-24 Complete Trace Supremum Endpoint Design

| Source row | Old status | Re-audit result | Existing declaration/import | Intended Lean target | Dependencies | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| Problem 9.11 / equation (9.15), complete-pivoting trace growth-family supremum endpoint | `PROVE-NOW-SPLIT` partial endpoint | The current branch already has the complete-pivoting trace value set, boundedness, and lower-bound witness family, but the live API lacks the positive-dimensional nonemptiness wrapper and source-shaped elementary supremum upper bound analogous to the partial-pivoting endpoint | `higham9_completePivotingUTraceGrowthValues`, `higham9_completePivotingUTraceGrowthSup`, `higham9_completePivotingUTraceGrowthValues_bddAbove`, `higham9_8_CompletePivotGECPUTrace_growthFactorEntry_le_pow_two`, `higham9_8_exists_CompletePivotGECPUTrace_of_det_ne_zero`; module `LeanFpAnalysis.FP.Algorithms.HighamChapter9` | `higham9_completePivotingUTraceGrowthValues_nonempty` and `higham9_8_completePivotingUTraceGrowthSup_le_pow_two` | Existing complete-pivoting trace existence for nonsingular matrices, the Wilkinson matrix nonsingularity witness, `growthFactorEntry`, `sSup`, `csSup_le`, and the elementary complete-pivoting trace upper bound | Implement thin proved wrappers, add lookup/example checks, and keep the sharper Wilkinson complete-pivoting product bound open |

Result: implemented and full verification passed in this continuation; the
sharper Wilkinson complete-pivoting product bound remains open.

## 2026-06-24 Certificate-Level Complete-Pivoting Value Witness Design

| Source row | Old status | Re-audit result | Existing declaration/import | Intended Lean target | Dependencies | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| Problem 9.11 / equation (9.15), certificate-level complete-pivoting growth-value witness | `PROVE-NOW-SPLIT` partial endpoint | The current branch has the certificate-level complete-pivoting value set, supremum, `le_sup` adapter under boundedness, and sine-block lower-bound theorem, but the live API lacks the explicit global value-set witness analogous to the trace-level theorem | `higham9_completePivotingCertificateGrowthValues`, `higham9_completePivotingCertificateGrowthSup`, `higham9_completePivotingCertificateGrowth_le_sup`, `higham9_11_sineBlockCompletePivotingGrowthSet_exists_ge_succ`; module `LeanFpAnalysis.FP.Algorithms.HighamChapter9` | `higham9_11_completePivotingCertificateGrowthValues_exists_ge_succ` | Existing concrete flattened sine-block `PAQ = LU` complete-pivoting certificate and global certificate-level value-set definition | Implement the witness theorem, refactor the certificate-level supremum lower-bound proof through it, add lookup/example checks, and keep Wilkinson boundedness/product upper-bound open |

Result: implemented and focused verification passed in this continuation;
Wilkinson boundedness/product upper-bound proof remains open.

## 2026-06-24 Hessenberg Trace Supremum Endpoint Design

| Source row | Old status | Re-audit result | Existing declaration/import | Intended Lean target | Dependencies | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| Theorem 9.10, upper-Hessenberg GEPP trace growth-family supremum endpoint | `PROVE-NOW-SPLIT` partial endpoint | The current branch already has the explicit upper-Hessenberg GEPP `U` trace, source-facing trace existence for nonsingular upper-Hessenberg matrices, and the direct `rho <= n` theorem. The public API lacks the same value-set/supremum navigation surface already present for partial, complete, and rook pivoting. | `higham9_10_HessenbergGEPPUTrace`, `higham9_10_exists_HessenbergGEPPUTrace_of_det_ne_zero`, `higham9_10_HessenbergGEPPUTrace_growthFactorEntry_le_card`, `higham9_10_exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_of_det_ne_zero`; module `LeanFpAnalysis.FP.Algorithms.HighamChapter9` | `higham9_10_hessenbergGEPPUTraceGrowthValues`, `higham9_10_hessenbergGEPPUTraceGrowthSup`, `higham9_10_hessenbergGEPPUTraceGrowthValues_le_card`, `higham9_10_hessenbergGEPPUTraceGrowthValues_bddAbove`, `higham9_10_hessenbergGEPPUTraceGrowth_le_sup`, `higham9_10_hessenbergGEPPUTraceGrowthValues_nonempty`, and `higham9_10_hessenbergGEPPUTraceGrowthSup_le_card` | Existing Hessenberg trace predicate, `IsUpperHessenberg`, `growthFactorEntry`, `maxEntryNorm`, `sSup`, `BddAbove`, `le_csSup`, `csSup_le`, and the identity matrix as a nonsingular upper-Hessenberg witness | Implement thin proved wrappers, add lookup/example checks, and keep the remaining sharp complete-/rook-pivoting product-bound rows open |

Result: implemented in this continuation. Focused Ch9 verification passed before the lookup/report updates; full lookup/build verification is recorded below after the navigation checks.

## 2026-06-24 Pivoted GEPP Wilkinson Adapter Design

| Source row | Old status | Re-audit result | Existing declaration/import | Intended Lean target | Dependencies | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| Theorem 9.5 / equation (9.10), partial-pivoting normwise backward-error bound from an explicit pivoted certificate and GEPP `U` trace | `PROVE-NOW-SPLIT` partial endpoint; computed GEPP/certificate link still open | The current branch has the GEPP `U` trace growth theorem and row-pivoted backward-error certificates, but the public API lacks a source-facing theorem that combines them for the pivoted solve while preserving the original matrix norm. The theorem will not claim that the floating-point implementation constructs the trace or certificate; those remain visible hypotheses. | `higham9_7_PartialPivotGEPPUTrace`, `higham9_7_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two`, `higham9_2_PermutedLUBackwardError`, `higham9_2_permutedLUBackwardError_to_LUBackwardError`, `higham_problem9_4_permuted_lu_solve_backward_error`, and `higham9_5_wilkinson_source_bound_of_entry_growth`; module `LeanFpAnalysis.FP.Algorithms.HighamChapter9` | `higham9_2_rowPermutedMatrix_maxEntryNorm`, `higham9_2_rowPermutedMatrix_infNorm`, and `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace` | `IsPermutation`, `Equiv.ofBijective`, `maxEntryNorm`, `infNorm`, `growthFactorEntry`, row-unpermuting the perturbation, and the closed trace growth bound `rho <= 2^(n-1)` | Implement the norm-preservation lemmas and the pivoted source-facing Wilkinson bound, add lookup/example checks, and keep the actual computed GEPP trace/certificate construction open |

Result: implemented in this continuation; the actual computed GEPP
trace/certificate construction remains open.

## 2026-06-24 Column-Dominant Tridiagonal Exact-LU Growth Design

| Source row | Old status | Re-audit result | Existing declaration/import | Intended Lean target | Dependencies | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| Theorem 9.13, column-diagonally-dominant tridiagonal `|L||U| <= 3|A|` and `rho <= 3` with exact no-pivot LU existence | `PROVE-NOW-SPLIT` source exact-LU packaging endpoint | The branch already has exact no-pivot LU existence for nonsingular column-diagonally-dominant matrices with unit-bounded lower entries, and has Theorem 9.13 tridiagonal componentwise/max-entry growth wrappers for any exact `LUFactSpec`; the public API still required users to combine these manually. | `higham9_9_colDiagDominant_lu_exists_unit_lower_of_det_ne_zero`, `higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec`, and `higham9_13_colDiagDom_growthFactorEntry_le_three_of_LUFactSpec`; module `LeanFpAnalysis.FP.Algorithms.HighamChapter9` | `higham9_13_colDiagDom_exists_LUFactSpec_growth_bound_3` and `higham9_13_colDiagDom_exists_LUFactSpec_growthFactorEntry_le_three` | Existing no-pivot exact-LU construction, source tridiagonality, column diagonal dominance, nonsingularity, and max-entry positivity for the `rho` form | Implement thin existential wrappers, add lookup/example checks, and keep row-dominant/general special-class executable trace coverage open |

Result: implemented in this continuation.  The column-dominant tridiagonal
source exact-LU/growth package is closed; row-dominant/general special-class
existence not already covered by explicit `LUFactSpec`/recurrence hypotheses
and rounded executable trace construction remain open.

## 2026-06-24 Row-Dominant Transpose Tridiagonal Exact-LU Growth Design

| Source row | Old status | Re-audit result | Existing declaration/import | Intended Lean target | Dependencies | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| Theorem 9.13, row-diagonally-dominant tridiagonal transpose exact-LU `|L_T||U_T| <= 3|Aᵀ|` and `rho <= 3` | `PROVE-NOW-SPLIT` source exact-LU packaging endpoint for the transpose orientation | The branch had row/column transpose adapters, exact no-pivot LU existence for nonsingular column-diagonally-dominant matrices, column-dominant exact-LU growth packaging, and row-dominant transpose structural/max-entry wrappers. The public API still lacked the existential row-dominant transpose package that produces exact factors for `Aᵀ` directly from source data on `A`. | `higham9_13_colDiagDom_exists_LUFactSpec_growth_bound_3`, `higham9_13_colDiagDom_exists_LUFactSpec_growthFactorEntry_le_three`, `higham9_13_tridiagonal_transpose_iff`, `higham9_9_colDiagDominant_transpose_iff_rowDiagDominant`, and `maxEntryNorm_matTranspose`; module `LeanFpAnalysis.FP.Algorithms.HighamChapter9` | `higham9_13_rowDiagDom_transpose_exists_LUFactSpec_growth_bound_3` and `higham9_13_rowDiagDom_transpose_exists_LUFactSpec_growthFactorEntry_le_three` | Determinant invariance under transpose, source tridiagonality, source row diagonal dominance, and max-entry transpose invariance for the `rho` form | Implement thin existential transpose wrappers, add lookup/example checks, then add the later direct row-dominant rescaling bridge; keep executable trace coverage open |

Result: implemented in this continuation.  The row-dominant transpose exact-LU
growth package is closed for factors of `Aᵀ`.  A later proof-completion step
also added `higham9_13_LUFactSpec_of_transpose_LUFactSpec_nonzero_pivots`,
which rescales an exact LU of `Aᵀ` with nonzero pivots into a unit-lower/upper
exact LU of `A`, and the direct row-dominant source packages
`higham9_13_rowDiagDom_exists_LUFactSpec_growth_bound_3` and
`higham9_13_rowDiagDom_exists_LUFactSpec_growthFactorEntry_le_three`.
General special-class existence packaging and rounded executable trace
construction remain open.

## 2026-06-24 Total-Nonnegative Special-Class Exact-LU Growth Design

| Source row | Old status | Re-audit result | Existing declaration/import | Intended Lean target | Dependencies | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| Theorem 9.12 special-class no-growth endpoint, total-nonnegative/nonsingular branch | Closed source existence package for one special class; other special classes remain under visible factor/certificate hypotheses | Problem 9.6 proves that every nonsingular totally nonnegative real matrix admits exact no-pivot LU factors with nonnegative `L` and `U`, and the Theorem 9.12 nonnegative-LU wrapper proves `|L||U| = |A|` and `rho <= 1` from such factors. The public Theorem 9.12 surface now has source-shaped existential wrappers, and Theorem 9.14 has both the corresponding model-consuming final `h(u)|A|` package and an exact-factor/actual triangular-solve `f(u)|A|` package. | `higham9_6_lu_exists_nonnegative_of_totalNonnegative_det_ne_zero`, `higham9_12_nonneg_lu_optimal_growth`, `higham9_12_nonneg_lu_growthFactorEntry_le_one`; module `LeanFpAnalysis.FP.Algorithms.HighamChapter9` | `higham9_12_totalNonnegative_exists_LUFactSpec_optimal_growth`, `higham9_12_totalNonnegative_exists_LUFactSpec_growthFactorEntry_le_one`, `higham9_14_totalNonnegative_exists_source_h_bound_of_models`, and `higham9_14_totalNonnegative_exists_source_f_bound_actual_triangular_solves` | Total nonnegativity, nonsingularity, exact no-pivot LU existence from Problem 9.6, max-entry positivity for the `rho` form, explicit equation (9.20)/(9.21) source perturbation models for the Theorem 9.14 final `h(u)` bound, and actual `fl_forwardSub`/`fl_backSub` certificates with `gamma fp n <= u` for the `f(u)` bound | Keep remaining source-existence branches for SPD/M-matrix/sign-equivalent/general tridiagonal classes open unless their visible hypotheses are independently discharged; keep rounded LU factorization trace production open. |

Result: implemented in this continuation and extended on 2026-06-27. The
total-nonnegative/nonsingular source-existence branch of Theorem 9.12 now
exposes exact nonnegative no-pivot LU factors with optimal componentwise growth
and `rho <= 1`. The Theorem 9.14 wrappers turn those factors either plus
explicit source perturbation models into the final `h(u)|A|` bound, or plus
actual `fl_forwardSub`/`fl_backSub` calls into the exact-factor `f(u)|A|`
bound. Other special-class existence branches remain open unless their visible
factor/certificate hypotheses are independently supplied, and rounded LU
factorization trace production remains open.

## 2026-06-28 Sign-Equivalent Source-Predicate Bridge

This continuation closes the adapter layer between the repository's source
predicate `IsSignEquiv` and the existing explicit sign-diagonal Theorem 9.12(d)
and Theorem 9.14 surfaces.  The proof constructs diagonal matrices from the
source sign vectors, proves they satisfy `IsSignDiag`, and rewrites the
source equality `A = diag(d1) B diag(d2)` into the finite-sum form consumed by
the existing sign-equivalence growth lemmas.

New declarations:

- `higham9_12_signDiagMatrix`.
- `higham9_12_signDiagMatrix_isSignDiag`.
- `higham9_12_sign_equiv_signDiag_witnesses`.
- `higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv`.
- `higham9_12_sign_equiv_growthFactorEntry_le_one_of_IsSignEquiv`.
- `higham9_12_sign_equiv_growthFactorEntry_le_one_of_IsSignEquiv_det_ne_zero`.
- `higham9_14_sign_equiv_source_h_bound_of_IsSignEquiv_models`.
- `higham9_14_sign_equiv_source_f_bound_actual_triangular_solves_of_IsSignEquiv`.

Formalization decision: this is a source-predicate adapter only.  It reuses
the already formalized sign-diagonal optimal-growth and tridiagonal
backward-error wrappers, and it deliberately leaves the absolute factor
structure, exact `LUFactSpec`, perturbation models, and nonsingularity
hypotheses visible.  It does not claim source existence of sign-equivalent LU
factors or a rounded tridiagonal factorization trace.

## 2026-06-28 Problem 9.9 Det-Only Denominator Wrappers

This continuation also closes a small denominator-packaging gap for the exact
no-pivot Problem 9.9 surfaces.  The existing reduced-growth and final-`U`
growth bounds required callers to supply both `0 < maxEntryNorm A` and
`0 < infNorm A`; nonsingularity already supplies both in positive dimension.
The new wrappers discharge those side conditions from `det A != 0` and return
the required `maxEntryNorm` witness in the theorem conclusion.

New declarations:

- `higham9_infNorm_pos_of_det_ne_zero`.
- `higham_problem9_9_noPivotReducedGrowthFactor_le_one_of_nonnegative_LU_exists_hAmax`.
- `higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_absLU_infNorm_div_exists_hAmax`.
- `higham_problem9_9_growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div_exists_hAmax`.

Formalization decision: these wrappers do not construct no-pivot factors or
prove that an executable GE loop produced the supplied `LUFactSpec`.  They
only remove redundant denominator hypotheses for already formalized exact
Problem 9.9 growth bounds.

## 2026-06-28 Problem 9.9 / Equation 9.17 Skeel Composition

This continuation composes the exact no-pivot Problem 9.9 growth bounds with
the equation (9.17) exact-LU bridge
`‖ |L| |U| ‖∞ <= condSkeel(U) ‖A‖∞`.  Given an exact `LUFactSpec`, an exact
inverse for `U`, and `det A != 0`, the reduced-growth and final-`U` growth
surfaces now expose the source-shaped bound `1 + n * condSkeel(U)` directly.

New declarations:

- `higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_condSkeel_exists_hAmax`.
- `higham_problem9_9_growthFactorEntry_le_one_add_card_mul_condSkeel_exists_hAmax`.
- `higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_two_card_sub_one_of_rowDiagDomUpper_exists_hAmax`.
- `higham_problem9_9_growthFactorEntry_le_one_add_card_mul_two_card_sub_one_of_rowDiagDomUpper_exists_hAmax`.

Formalization decision: this is a composition of already closed exact-LU
algebra, the corrected equation (9.17) row-dominant-upper bound
`|| |L| |U| ||_inf <= (2n - 1) ||A||_inf`, and Problem 9.9 max-entry growth
support.  It does not prove the full diagonal-dominance theorem
`rho_n <= 2`, which remains deferred to the source-cited later
block-diagonal-dominance results, and it does not construct the no-pivot
executable trace.

## 2026-06-28 Theorem 9.13 Det-Derived Growth Denominators

This continuation removes another small source-facing obligation from the
diagonally-dominant tridiagonal packages: the source-data builder/recurrence,
column-dominant, row-dominant transpose, and direct row-dominant `rho <= 3`
wrappers now have versions that derive `0 < maxEntryNorm A` from an
already-present or explicit nonsingularity hypothesis.

New declarations:

- `higham9_13_tridiag_builder_growthFactorEntry_le_three_exists_hAmax`.
- `higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three_exists_hAmax`.
- `higham9_13_tridiag_builder_growthFactorEntry_le_three_of_recurrence_exists_hAmax`.
- `higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three_of_recurrence_exists_hAmax`.
- `higham9_13_colDiagDom_exists_LUFactSpec_growthFactorEntry_le_three_exists_hAmax`.
- `higham9_13_rowDiagDom_transpose_exists_LUFactSpec_growthFactorEntry_le_three_exists_hAmax`.
- `higham9_13_rowDiagDom_exists_LUFactSpec_growthFactorEntry_le_three_exists_hAmax`.

Formalization decision: these are API-completion wrappers over the existing
Theorem 9.13 exact-LU packages.  They do not add a rounded factorization trace
or close the all-class tridiagonal executable coverage row.

## 2026-06-28 Pivot Trace Growth Denominator Wrappers

This continuation adds det-derived positive-denominator wrappers at the raw
trace-growth level for partial pivoting, complete pivoting, rook pivoting, and
upper-Hessenberg GEPP.  The complete-pivoting declaration exposes the elementary
recursive `2^(n-1)` trace bound for nonsingular inputs; it does not prove
Wilkinson's sharper product bound.

New declarations:

- `higham9_7_exists_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero_exists_hAmax`.
- `higham9_8_exists_CompletePivotGECPUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero`.
- `higham9_8_exists_CompletePivotGECPUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero_exists_hAmax`.
- `higham9_16_exists_RookPivotGEUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero_exists_hAmax`.
- `higham9_10_exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_of_det_ne_zero_exists_hAmax`.

Formalization decision: these are source-facing trace-growth API completions.
They keep the rounded pivot-loop trace-to-certificate construction, the sharp
complete-pivoting product proof, and Foster's rook-pivoting product proof open.

## This Pass

Newly proved Lean material across the Chapter 9 proof-completion and Split 2
unifying passes:

| Source item | Lean declaration | File | Status |
| --- | --- | --- | --- |
| Section 9.1, partial/complete/rook first-stage pivot choices and multiplier bounds | `higham9_1_partialPivotChoice`, `higham9_1_completePivotChoice`, `higham9_1_rookPivotChoice`, `higham9_1_partialPivot_multiplier_abs_le_one`, `higham9_1_completePivot_column_multiplier_abs_le_one`, `higham9_1_completePivot_active_entry_ratio_abs_le_one`, `higham9_1_rookPivot_column_multiplier_abs_le_one`, `higham9_1_rookPivot_row_multiplier_abs_le_one` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the first-stage pivot predicates and the immediate multiplier/active-entry ratio bound lemmas |
| Section 9.1, finite active-set pivot-choice existence | `higham9_1_exists_partialPivotChoice`, `higham9_1_exists_completePivotChoice`, `higham9_1_rookPivotChoice_of_completePivotChoice`, `higham9_1_exists_rookPivotChoice` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for existence of partial- and complete-pivoting maxima over the finite active row/submatrix and for complete-pivot maxima as accepted rook pivots; full elimination traces remain open |
| Section 9.1, selected pivot nonzero support | `higham9_1_partialPivotChoice_pivot_ne_zero_of_exists`, `higham9_1_completePivotChoice_pivot_ne_zero_of_exists`, `higham9_1_exists_partialPivotChoice_pivot_ne_zero`, `higham9_1_exists_completePivotChoice_pivot_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for deriving a nonzero selected partial/complete pivot whenever the active column/submatrix contains a nonzero candidate; full elimination traces remain open |
| Section 9.1 / equation (9.2b), complete-pivoting first-step nonsingularity support | `higham9_1_exists_entry_ne_zero_of_det_ne_zero`, `higham9_1_exists_first_completePivotChoice_pivot_ne_zero_of_det_ne_zero`, `higham9_2_firstPivotRowColSwap_det_ne_zero`, `higham9_1_firstCompletePivotSchurComplement_det_ne_zero_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the first complete-pivoting trace dependency that a nonsingular positive-dimensional real matrix has a nonzero first complete pivot, that moving the first complete pivot to `(0,0)` by row and column swaps preserves nonsingularity, and that the first Schur complement remains nonsingular; this is dependency infrastructure and does not construct the full complete-pivoting trace |
| Section 9.1, first-stage nonzero pivot and ratio-bound packages | `higham9_1_exists_partialPivot_nonzero_and_multiplier_bound`, `higham9_1_exists_completePivot_nonzero_and_ratio_bounds`, `higham9_1_exists_rookPivot_nonzero_and_ratio_bounds` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for combining finite active-set existence, nonzero selected-pivot support, and multiplier/entry-ratio bounds at one active stage; full elimination traces remain open |
| Equation (9.1), determinant-pivot product for an exact LU certificate | `LUFactSpec.det_eq_prod_U_diag`, `LUFactSpec.det_ne_zero_iff_U_diag_ne_zero`, `higham9_1_det_eq_pivot_product`, `higham9_1_det_ne_zero_iff_pivots_ne_zero` | `LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean`, `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the determinant/product identity and nonzero-pivot iff consequence once an exact LU certificate is supplied |
| Theorem 9.1 / Problems 9.1-9.2, leading-principal determinant-pivot support, Schur-complement determinant induction, exact LU existence, exact-LU uniqueness, and Problem 9.1 converse | `higham9_1_firstSchurComplement`, `higham9_1_lu_exists_of_firstSchurComplement`, `higham9_1_firstSchurComplement_properLeadingPrincipalBlock_det_ne_zero`, `higham9_1_lu_exists_of_properLeadingPrincipalBlock_det_ne_zero`, `higham9_1_leadingPrincipalBlock_det_eq_pivot_product`, `higham9_1_leadingPrincipalBlock_det_ne_zero_iff_pivots_ne_zero`, `higham9_1_lu_unique_of_proper_pivots_ne_zero`, `higham9_1_lu_unique_of_properLeadingPrincipalBlock_det_ne_zero`, `higham9_1_lu_exists_and_unique_of_properLeadingPrincipalBlock_det_ne_zero`, `higham9_1_lu_nonunique_of_zero_proper_pivot`, `higham_problem9_1_properLeadingPrincipalBlock_det_ne_zero_of_unique_lu`, `higham9_1_lu_exists_unique_iff_properLeadingPrincipalBlock_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean`, `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for Higham's exact source iff with `A(1:k,1:k)` nonsingular for `k = 1 : n-1`; the first-Schur-complement proper-leading-minor inheritance step feeds the one-step construction by induction, uniqueness uses only proper nonzero pivots plus triangularity in the last column, and the singular-converse direction is proved by an explicit lower-shear nonuniqueness construction |
| Equations (9.2a)--(9.2b) and Theorem 9.3, permuted LU certificate adapters | `higham9_2_rowPermutedMatrix`, `higham9_2_PermutedLUFactSpec`, `higham9_2_permutedLUFactSpec_to_LUFactSpec`, `higham9_2_PermutedLUBackwardError`, `higham9_2_permutedLUBackwardError_to_LUBackwardError`, `higham9_2_permutedLUFactSpec_to_PermutedLUBackwardError_zero`, `higham9_2_permutedLUFactSpec_to_PermutedLUBackwardError_gamma`, `higham9_3_permuted_lu_backward_error_gamma`, `higham9_3_permuted_lu_backward_error_gamma_of_LUFactSpec`, `higham9_2_colPermutedMatrix`, `higham9_2_rowColPermutedMatrix`, `higham9_2_firstPivotRowColSwap_det_ne_zero`, `higham9_2_CompletePermutedLUFactSpec`, `higham9_2_completePermutedLUFactSpec_to_LUFactSpec`, `higham9_2_CompletePermutedLUBackwardError`, `higham9_2_completePermutedLUBackwardError_to_LUBackwardError`, `higham9_2_completePermutedLUFactSpec_to_CompletePermutedLUBackwardError_zero`, `higham9_2_completePermutedLUFactSpec_to_CompletePermutedLUBackwardError_gamma`, `higham9_3_complete_permuted_lu_backward_error_gamma`, `higham9_3_complete_permuted_lu_backward_error_gamma_of_LUFactSpec`, `higham9_3_exists_complete_permuted_lu_backward_error_gamma_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for converting explicit `PA = LU`, `PAQ = LU`, and pivoted/complete-pivoted backward-error certificates into ordinary LU certificates on the corresponding permuted source matrix; exact certificates now produce zero-coefficient and `gamma_n` backward-error certificates, and nonsingular real inputs have an exact complete-pivoted certificate existence package. The rounded pivot-loop trace-to-certificate construction remains open |
| Equations (9.2a)--(9.2b), full permutation norm preservation | `higham9_2_rowPermutedMatrix_maxEntryNorm`, `higham9_2_rowPermutedMatrix_infNorm`, `higham9_2_colPermutedMatrix_maxEntryNorm`, `higham9_2_colPermutedMatrix_infNorm`, `higham9_2_rowColPermutedMatrix_maxEntryNorm`, `higham9_2_rowColPermutedMatrix_infNorm` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for preserving Higham's max-entry norm and the matrix infinity norm under source row, column, and row/column permutations; this supports pivoted and complete-pivoted source bounds over the original matrix norm |
| Equations (9.2a)--(9.2b), determinant-pivot consequences for explicit permuted LU certificates | `higham9_2_permutedLUFactSpec_det_eq_pivot_product`, `higham9_2_permutedLUFactSpec_det_ne_zero_iff_pivots_ne_zero`, `higham9_2_completePermutedLUFactSpec_det_eq_pivot_product`, `higham9_2_completePermutedLUFactSpec_det_ne_zero_iff_pivots_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for `PA`/`PAQ` once an explicit permuted LU certificate is supplied; pivot-trace construction remains open |
| Algorithm 9.2, dense square Doolittle executable-loop handoff | `higham9_2_DoolittleDenseLoopCertificate`, `higham9_2_DoolittleDenseLoopAbsBudgetCertificate`, `higham9_2_denseLoopCertificate_to_DoolittleLU`, `higham9_2_absBudgetCertificate_to_DoolittleLU`, `higham9_2_absBudgetCertificate_of_literal_doolittle_source_budgets`, `higham9_2_absBudgetCertificate_of_literal_doolittle_component_dominance`, `higham9_2_absBudgetCertificate_of_literal_doolittle_exact_product_margins`, `higham9_2_absBudgetCertificate_of_literal_doolittle_exact_product_numerator_margins`, `higham9_2_absBudgetCertificate_of_literal_doolittle_exact_target_gaps`, `higham9_3_denseLoopCertificate_backward_error`, `higham9_3_absBudgetCertificate_backward_error`, `higham9_3_literalDoolittle_source_budgets_backward_error`, `higham9_3_literalDoolittle_componentDominance_backward_error`, `higham9_3_literalDoolittle_exactProductMargins_backward_error`, `higham9_3_literalDoolittle_exactProductNumeratorMargins_backward_error`, `higham9_3_literalDoolittle_exactTargetGaps_backward_error` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the source-facing bridge from dense square literal-loop certificates with visible residual-compression, source absolute budgets, componentwise dominance, exact-product margins, exact-product numerator margins, or explicit exact-target gap hypotheses to the compact `DoolittleLU` certificate and Theorem 9.3 backward-error surface, including direct Theorem 9.3 endpoint wrappers for each literal-budget route; the full rectangular executable trace remains open |
| Algorithm 9.2, rectangular Doolittle source identities (9.3) and (9.4), rounded literal fold/certificate layer, and exact-LU recurrence converse | `higham9_2_rectRow`, `higham9_2_rectPrefixDot`, `higham9_2_rectDoolittleUUpdate`, `higham9_2_rectDoolittleLUpdate`, `higham9_2_rectFlDoolittleUEntry`, `higham9_2_rectFlDoolittleLNumerator`, `higham9_2_rectFlDoolittleLEntry`, `higham9_2_rectDoolittleUProductAbs`, `higham9_2_rectDoolittleUWorkAbs`, `higham9_2_rectDoolittleUAbsBudget`, `higham9_2_rectDoolittleLProductAbs`, `higham9_2_rectDoolittleLWorkAbs`, `higham9_2_rectDoolittleLNumeratorAbs`, `higham9_2_rectDoolittleLAbsBudget`, `higham9_2_rectDoolittleUAbsBudget_le_compression_of_component_dominance`, `higham9_2_rectDoolittleLAbsBudget_le_compression_of_component_dominance`, `higham9_2_rectDoolittleUWorkAbs_le_of_exact_product_margin`, `higham9_2_rectDoolittleUProductAbs_le_of_exact_product_margin`, `higham9_2_rectDoolittleLWorkAbs_le_of_exact_product_margin`, `higham9_2_rectDoolittleLProductAbs_le_of_exact_product_margin`, `higham9_2_rectDoolittleLNumeratorAbs_le_of_exact_product_numerator_margin`, `higham9_2_rectDoolittleUExactTarget`, `higham9_2_rectDoolittleLExactTarget`, `higham9_2_rectDoolittleUExactTargetResidualBudget`, `higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget`, `higham9_2_rectDoolittleLExactTargetEntryResidualBudget`, `higham9_2_rectDoolittleUExactProductMargin_of_exactTarget_gap`, `higham9_2_rectDoolittleLExactProductMargin_of_exactTarget_gap`, `higham9_2_rectDoolittleLExactProductNumeratorMargin_of_exactTarget_gap`, `higham9_2_RectDoolittleDenseLoopCertificate`, `higham9_2_RectDoolittleDenseLoopAbsBudgetCertificate`, `higham9_2_rectAbsBudgetCertificate_to_rectDenseLoopCertificate`, `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_source_budgets`, `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_component_dominance`, `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_margins`, `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_numerator_margins`, `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_target_gaps`, `higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate`, `higham9_2_rectAbsBudgetCertificate_to_squareAbsBudgetCertificate`, `higham9_2_rectMatMul_eq_prefix_add_upper`, `higham9_2_rectMatMul_eq_prefix_add_lower`, `higham9_2_abs_upper_entry_le_rectMatMul_abs_sum`, `higham9_2_abs_lower_entry_mul_pivot_le_rectMatMul_abs_sum`, `higham9_3_rectDenseLoopCertificate_backward_error`, `higham9_3_rectAbsBudgetCertificate_backward_error`, `higham9_3_rectLiteralDoolittle_source_budgets_backward_error`, `higham9_3_rectLiteralDoolittle_componentDominance_backward_error`, `higham9_3_rectLiteralDoolittle_exactProductMargins_backward_error`, `higham9_3_rectLiteralDoolittle_exactProductNumeratorMargins_backward_error`, `higham9_3_rectLiteralDoolittle_exactTargetGaps_backward_error`, `higham9_3_rectDenseLoopCertificate_square_backward_error`, `higham9_3_rectAbsBudgetCertificate_square_backward_error`, `higham9_3_rectLiteralDoolittle_source_budgets_square_backward_error`, `higham9_2_rectFlDoolittleUEntry_residual_abs_le`, `higham9_2_rectFlDoolittleLNumerator_residual_abs_le`, `higham9_2_rectFlDoolittleLEntry_mul_pivot_sub_numerator_abs_le`, `higham9_2_rectFlDoolittleLEntry_residual_abs_le`, `higham9_2_rectDoolittleUUpdate_source_identity`, `higham9_2_rectDoolittleU_source_identity`, `higham9_2_rectDoolittleLUpdate_source_identity`, `higham9_2_rectDoolittleL_source_identity`, `higham9_2_rectDoolittleUUpdate_eq_of_LUFactSpec`, `higham9_2_rectDoolittleLUpdate_eq_of_LUFactSpec` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the exact rectangular upper/lower update identities, for the rectangular rounded upper/lower literal fold residual budgets, for the rectangular absolute-budget certificate target, literal-source-budget constructor, component-dominance handoff, exact-product/no-cancellation margin handoffs, and exact-target gap handoff with the required rectangular lower coefficient condition exposed, for the direct rectangular Theorem 9.3 componentwise backward-error endpoint plus direct component-dominance/exact-product/exact-target endpoint variants, for the `m = n` bridge back into the existing square dense-loop/absolute-budget certificate APIs, and for the square exact-LU converse showing any `LUFactSpec` satisfies the Doolittle upper/lower recurrence; the full rectangular executable loop schedule and pivot-loop trace-to-certificate construction remain open |
| Algorithm 9.2, printed leading flop-count polynomial | `higham9_2_doolittleSourceFlopPolynomial`, `higham9_2_doolittleSourceFlopPolynomial_eq`, `higham9_2_doolittleSourceFlopPolynomial_one` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the rational source polynomial and its expansion; exact integer loop-cost accounting is SKIP because the source does not specify a literal cost model |
| Algorithm 9.2, reduced-matrix identity (9.5) | `higham9_5_rectPrefixRange`, `higham9_5_rectGEReducedEntry`, `higham9_5_rectGEReducedEntry_succ_of_lt`, `higham9_5_rectPrefixRange_eq_rectPrefixDot`, `higham9_5_rectGEReducedEntry_eq_DoolittleUUpdate`, `higham9_5_rectGEReducedEntry_eq_DoolittleLUpdate_mul_pivot` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the exact no-pivot GE reduced-entry identity and its Doolittle upper/lower update specializations; the full executable rectangular loop remains open |
| Lemma 9.6, no-pivot reduced-stage absolute-product source constant | `higham9_5_rectPrefixRange_full_eq_matMul`, `higham9_5_rectGEReducedEntry_full_eq_zero_of_LUFactSpec`, `higham9_6_rankOne_abs_le_reduced_add_succ`, `higham9_6_absLU_infNorm_le_of_reduced_stage_pair_rows`, `higham9_6_absLU_infNorm_le_two_card_mul_of_reduced_stage_row_bounds`, `higham9_6_sum_stage_pair_eq_endpoints_add_two_range`, `higham9_6_absLU_infNorm_le_source_constant_of_reduced_entry_growth`, `higham9_6_absLU_infNorm_le_source_constant_of_noPivotReducedGrowthFactor`, `higham9_6_absLU_infNorm_le_source_constant_of_noPivotReducedGrowthFactor_exists_hAmax` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the full-prefix equals `LU`, terminal residual-zero, per-stage rank-one absolute estimate, stage-pair row-sum bridge, exact source counting, and the printed `1 + 2(n^2-n)rho_n` constant using the no-pivot reduced growth factor from equation (9.5), including the source-nonsingularity wrapper that derives the positive denominator in `rho_n` from `det A != 0` |
| Theorem 9.5, max-entry growth to infinity-norm source bridge and explicit-trace specializations | `entry_abs_le_infNorm`, `maxEntryNorm_le_infNorm`, `infNorm_le_card_mul_maxEntryNorm`, `infNorm_le_card_mul_growthFactorEntry_bound`, `higham9_5_wilkinson_source_bound_of_entry_growth`, `higham9_5_wilkinson_source_bound_of_PartialPivotGEPPUTrace`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_denseLoop`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_absBudget`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_literalSourceBudgets`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_componentDominance`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_exactProductMargins`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_exactProductNumeratorMargins`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_exactTargetGaps`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_LUFactSpec`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_denseLoop`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_absBudget`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_literalSourceBudgets`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_componentDominance`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_exactProductMargins`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_exactProductNumeratorMargins`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_exactTargetGaps`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_LUFactSpec` | `LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean`, `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for converting a source max-entry final-`U` growth bound into the infinity-norm bridge used by Wilkinson's bound, for instantiating equation (9.10)'s `2^(n-1)` factor for an explicit partial-pivoting `U` trace under visible LU/backward-error certificate hypotheses, for the row-pivoted source-system form that unpermutes the perturbation and preserves the original matrix norm, for dense-loop, absolute-budget, literal source-budget, component-dominance, exact-product margin, exact-product numerator-margin, exact-target-gap, and exact-certificate entry points over `PA`, and for the complete-pivoted explicit `PAQ` certificate plus the same dense-loop, absolute-budget, literal source-budget, dominance/margin, exact-target-gap, and exact-certificate forms that unpermute both rows and columns. The concrete pivot trace-to-certificate construction and the sharp complete-pivoting product bound remain open |
| Theorem 9.7 / partial-pivoting first-step, arbitrary `U` trace upper bound, recurrence, Wilkinson witness, and source growth-family support | `higham9_7_firstPivotRowSwap`, `higham9_7_partialPivot_firstSchurComplement_entry_abs_le_two`, `higham9_7_partialPivot_firstSchurComplement_maxEntryNorm_le_two`, `higham9_7_partialPivot_stageMax_le_pow_two`, `higham9_7_partialPivot_growthFactorEntry_le_pow_two_of_stage_bounds`, `higham9_7_PartialPivotGEPPUTrace`, `higham9_7_PartialPivotGEPPUTrace_upper_zero`, `higham9_7_PartialPivotGEPPUTrace_entry_abs_le_pow_two`, `higham9_7_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two`, `higham9_7_exists_PartialPivotGEPPUTrace_of_det_ne_zero`, `higham9_7_exists_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero`, `higham9_7_wilkinsonGrowthMatrix`, `higham9_7_wilkinsonGrowthL`, `higham9_7_wilkinsonGrowthU`, `higham9_7_wilkinsonGrowthStageU`, `higham9_7_wilkinsonGrowthStageU_one`, `higham9_7_wilkinsonGrowthStageMatrix`, `higham9_7_wilkinsonGrowthStageMatrix_one`, `higham9_7_wilkinsonGrowthStage_partialPivotChoice_zero`, `higham9_7_wilkinsonGrowthStage_firstSchurComplement`, `higham9_7_wilkinsonGrowthStage_pow_firstSchurComplement`, `higham9_7_PartialPivotNoInterchangeTrace`, `higham9_7_wilkinsonGrowthStage_partialPivotChoice_zero_succ`, `higham9_7_wilkinsonGrowthStage_pivot_zero_ne_zero`, `higham9_7_wilkinsonGrowthStage_pow_firstSchurComplement_succ`, `higham9_7_wilkinsonGrowthStage_noInterchangeTrace`, `higham9_7_wilkinsonGrowth_noInterchangeTrace`, `higham9_7_wilkinsonGrowthStage_entry_abs_le_scale`, `higham9_7_wilkinsonGrowthStage_maxEntryNorm_eq_scale`, `higham9_7_wilkinsonGrowthStage_maxEntryNorm_eq_pow`, `higham9_7_wilkinsonGrowthStage_lu`, `higham9_7_wilkinsonGrowthStageU_entry_abs_le_scale_pow`, `higham9_7_wilkinsonGrowthStageU_maxEntryNorm_eq_scale_pow`, `higham9_7_wilkinsonGrowthStage_growthFactorEntry_eq_pow`, `higham9_7_wilkinsonGrowthL_two_pow_sum`, `higham9_7_wilkinsonGrowth_lu`, `higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_eq_one`, `higham9_7_wilkinsonGrowthU_maxEntryNorm_eq_pow`, `higham9_7_wilkinsonGrowth_growthFactorEntry_eq_pow`, `higham9_7_wilkinsonGrowth_attains_partialPivoting_bound`, `higham9_7_partialPivoting_growth_bound_and_attainment`, `higham9_partialPivotingUTraceGrowthValues`, `higham9_partialPivotingUTraceGrowthSup`, `higham9_partialPivotingUTraceGrowthValues_bddAbove`, `higham9_partialPivotingUTraceGrowth_le_sup`, `higham9_partialPivotingUTraceGrowthValues_nonempty`, `higham9_7_partialPivotingUTraceGrowthSup_le_pow_two` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the source one-step inequality that, after moving a partial-pivoting column maximum into the leading row, every first Schur-complement entry and the whole Schur-complement max-entry norm are bounded by `2 * maxEntryNorm A`; for the arbitrary nonsingular recursive partial-pivoting `U` trace and its source-facing exact growth upper bound `rho_n^p <= 2^(n-1)`; for the trace-level partial-pivoting growth-value family, boundedness, nonemptiness in positive dimension, supremum adapter, and source-shaped supremum theorem `sup rho_n^p <= 2^(n-1)`; for the arithmetic recurrence turning explicit per-stage doubling and a final upper-factor bound into `growthFactorEntry <= 2^(n-1)`; for the displayed Wilkinson matrix family, exact LU certificate, source max-entry norm `1`, upper-factor max-entry norm `2^(n-1)`, exact max-entry growth `2^(n-1)`, and no-interchange partial-pivoting trace; and for the scaled active-stage Wilkinson matrices, including the no-pivot first-column choice, first Schur-complement doubling, power-of-two stage recurrence, stage exact LU/upper-factor certificates, and stage max-entry/growth identities. The final package `higham9_7_partialPivoting_growth_bound_and_attainment` combines the nonsingular upper-bound theorem and Wilkinson attainability, and `higham9_7_partialPivotingUTraceGrowthSup_le_pow_two` closes the exact trace-level growth-family upper-bound surface. |
| Problem 9.9, exact no-pivot reduced-matrix and exact-LU growth bounds | `higham_problem9_9_noPivotReducedEntryMax`, `higham_problem9_9_noPivotReducedGrowthFactor`, `higham_problem9_9_noPivotReducedEntryMax_le_maxEntryNorm_add_absLU_infNorm`, `higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_absLU_infNorm_div`, `growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div`, `higham_problem9_9_growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div` | `LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean`, `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the source inequality `rho_n <= 1 + n * || |L||U| ||_inf / ||A||_inf`, with `rho_n` formalized over the exact GE-without-pivoting reduced matrices from equation (9.5), and for the final-`U` exact-LU algebraic specialization |
| Problem 9.10, single multiplier blunder rank-one error formula | `higham_problem9_10_rankOneBasis`, `higham_problem9_10_multiplierBlunderAlpha`, `higham_problem9_10_rankOneBasis_mulVec`, `higham_problem9_10_rankOnePerturbed_mulVec`, `higham_problem9_10_apply_left_inverse_of_matMulVec_eq`, `higham_problem9_10_matMulVec_scaledBasis`, `higham_problem9_10_rankOne_blunder_solution`, `higham_problem9_10_rankOne_blunder_error`, `higham_problem9_10_multiplier_blunder_error` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED by direct rank-one matrix-vector algebra: from `A x = b`, `(A - alpha e_i e_j^T) xhat = b`, an available left inverse of `A`, and the nonzero Sherman-Morrison denominator, the source error formula `x - xhat = -alpha*x_j/(1-alpha*A_inv(j,i))*A_inv(:,i)` is proved without importing or assuming the later Sherman-Morrison problem |
| Theorem 9.10, upper-Hessenberg first-step/stage-invariant trace support, growth scalar consequence, and solve-level backward-error consequence | `higham9_7_firstPivotRowSwap_involutive`, `higham9_7_firstPivotRowSwap_isPermutation`, `higham9_7_firstPivotRowSwap_det_ne_zero`, `higham9_10_hessenberg_firstColumn_nonzero_row_le_one`, `higham9_10_exists_first_active_column_nonzero_of_det_ne_zero`, `higham9_10_exists_first_partialPivotChoice_pivot_ne_zero_of_det_ne_zero`, `higham9_10_hessenberg_firstPivotRowSwap_tail`, `higham9_10_hessenberg_firstSchurComplement_tail_rows_eq_original`, `higham9_10_hessenberg_firstSchurComplement_isUpperHessenberg`, `higham9_10_firstSchurComplement_det_ne_zero_of_det_ne_zero`, `higham9_10_hessenberg_firstSchurComplement_row_bound`, `higham9_10_HessenbergStageBound`, `higham9_10_hessenberg_firstSchurComplement_stageBound`, `higham9_10_HessenbergStageBound_one_of_maxEntryNorm`, `higham9_10_HessenbergGEPPTrace`, `higham9_10_HessenbergGEPPTrace_upperHessenberg_and_stageBound`, `higham9_10_HessenbergGEPPTrace_isUpperHessenberg`, `higham9_10_HessenbergGEPPTrace_stageBound`, `higham9_10_exists_HessenbergGEPPTrace_terminal`, `higham9_10_exists_HessenbergGEPPTrace_terminal_of_det_ne_zero`, `higham9_10_hessenberg_growthFactorEntry_le_card_of_row_bounds`, `higham9_10_hessenberg_growth_backward_error`, `higham9_10_hessenberg_lu_solve_backward_stable_tight` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the first-stage Hessenberg GEPP facts that the first row swap is a determinant-preserving permutation, a nonsingular active matrix has a nonzero first-column entry, a nonzero first partial pivot can be selected, a nonzero first-column pivot is in row 0 or 1, the row-swapped first Schur complement remains nonsingular, tail rows are unchanged by the first Schur complement, the reduced matrix remains upper Hessenberg, the first reduced matrix satisfies the row-indexed bound, the source stage invariant advances from `k*M` to `(k+1)*M`, the initial max-entry bound starts the source invariant, and an explicit recursive trace interface preserves both upper-Hessenberg structure and the stage invariant by induction, with terminal trace existence for nonsingular active and source matrices; also closed for the scalar step from the source row-indexed upper-factor bound to `rho_n^p <= n`, and for the factorization and solve backward-error consequences once the source growth inequality `|L_hat||U_hat| <= n|A|` is supplied explicitly. The remaining local gap is constructing the full Hessenberg GEPP trace/final upper-factor row-bound theorem for arbitrary source inputs, not the nonsingularity/first-step/trace-induction/terminal-trace package. |
| Theorem 9.8, real max-entry `theta <= n` estimate | `inverse_row_identity_le_card_mul_maxEntryNorm`, `theta_le_card_of_inverse_row_identity`, `higham9_8_theta_le_card_real` | `LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean`, `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the real max-entry row-identity subclaim |
| Theorem 9.8, real max-entry `rho >= theta` bridge, exact final-pivot witness, and cumulative complete-pivoting `PAQ = LU` certificate | `growthFactorEntry_ge_inverse_entry_theta`, `higham9_8_growth_factor_ge_theta_real`, `higham9_8_finalPivot_mul_inverse_entry_eq_one`, `higham9_8_finalPivot_inverse_entry_abs_inv_le_maxEntryNorm`, `higham9_8_growth_factor_ge_theta_of_lu_right_inverse`, `higham9_2_rowColPermutedMatrix_right_inverse`, `higham9_8_finalPivot_mul_inverse_entry_eq_one_of_completePermutedLUFactSpec`, `higham9_8_finalPivot_inverse_entry_abs_inv_le_maxEntryNorm_of_completePermutedLUFactSpec`, `higham9_8_growth_factor_ge_theta_of_completePermutedLUFactSpec_right_inverse`, `higham9_8_extendTrailingPerm`, `higham9_8_extendTrailingPerm_isPermutation`, `higham9_8_luFirstSchurComplement_trailingPerm`, `higham9_8_exists_CompletePermutedLUFactSpec_of_det_ne_zero`, `higham9_8_exists_completePivoting_growth_factor_ge_theta_real` | same | CLOSED for the final-pivot/inverse-entry witness implication, for deriving that witness from an unpermuted exact `LUFactSpec`, for transporting the identity through an explicit `P A Q = L U` complete-permuted certificate plus a visible right inverse of `A`, and for constructing a cumulative real complete-pivoting `PAQ = LU` certificate from recursive complete-pivot choices. This does not prove Wilkinson's complete-pivoting upper bound or the bounded source `g(n)` family. |
| Theorem 9.8, recursive complete-pivoting `U` trace support | `higham9_8_CompletePivotGECPUTrace`, `higham9_8_CompletePivotGECPUTrace_upper_zero`, `higham9_8_exists_CompletePivotGECPUTrace_of_det_ne_zero`, `higham9_8_exists_CompletePivotGECPUTrace_upper_zero_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for constructing an explicit recursive complete-pivoting upper-factor trace for every nonsingular real matrix, using finite complete-pivot selection, row/column first-pivot swaps, and Schur-complement determinant inheritance; proves the exposed `U` rows are upper triangular. This is trace infrastructure only and does not prove Wilkinson's complete-pivoting growth bound. |
| Theorem 9.8 / Problem 9.11 complete-pivoting trace growth boundedness | `higham9_2_rowColPermutedMatrix_firstPivotRowSwap_maxEntryNorm`, `higham9_1_completePivot_rowColPermuted_partialPivotChoice_zero`, `higham9_8_completePivot_firstSchurComplement_maxEntryNorm_le_two`, `higham9_8_CompletePivotGECPUTrace_entry_abs_le_pow_two`, `higham9_8_CompletePivotGECPUTrace_growthFactorEntry_le_pow_two`, `higham9_completePivotingUTraceGrowthValues`, `higham9_completePivotingUTraceGrowthSup`, `higham9_completePivotingUTraceGrowthValues_bddAbove`, `higham9_completePivotingUTraceGrowth_le_sup`, `higham9_completePivotingUTraceGrowthValues_nonempty`, `higham9_8_completePivotingUTraceGrowthSup_le_pow_two` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the trace-level boundedness dependency: first row/column pivot swaps preserve max-entry norm, a first complete-pivot Schur complement has max-entry norm at most twice the source, every recursive complete-pivoting `U` trace satisfies `rho <= 2^(n-1)`, and the trace-level `g(n)` value set is bounded above, nonempty in every positive dimension, and has elementary supremum bound `g(n) <= 2^(n-1)`. This does not prove Wilkinson's sharper product bound (9.14). |
| Problem 9.11 trace-level complete-pivoting `g(2n)` lower bound | `maxEntryNorm_le_of_entry_le_bound`, `maxEntryNorm_le_of_entry_le_max`, `higham9_8_CompletePivotGECPUTrace_exists_CompletePermutedLUFactSpec_maxEntryNorm_le`, `higham9_8_CompletePivotGECPUTrace_growth_factor_ge_theta_real`, `higham9_11_exists_completePivotingUTrace_sine_block_growth_ge_succ`, `higham9_11_completePivotingUTraceGrowthValues_exists_ge_succ`, `higham9_11_completePivotingUTraceGrowthSup_ge_succ` | `LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean`, `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the source-shaped trace-level lower bound `n + 1 <= g(2n)`: every recursive complete-pivoting `U` trace yields a cumulative `PAQ = LU` certificate whose certificate `U` has no larger max-entry norm than the trace `U`; the final-pivot inverse-entry lower bound transfers to the trace surface; and the flattened sine block contributes a trace-level growth value at least `n + 1`. |
| Theorem 9.5 / Theorem 9.7 partial-pivoting exact trace-to-solve bridge | `higham9_7_luFirstSchurComplement_trailingRowPerm`, `higham9_5_wilkinson_source_bound_of_PermutedLUFactSpec_growth`, `higham9_7_PartialPivotGEPPUTrace_exists_PermutedLUFactSpec_L_bound_maxEntryNorm_le`, `higham9_5_wilkinson_source_bound_exists_of_PartialPivotGEPPUTrace` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for turning a recursive partial-pivoting GEPP trace into a cumulative exact `PA = LU` certificate with visible unit lower multipliers and certificate `U` max-entry norm bounded by the trace, then feeding the elementary trace growth theorem into the Theorem 9.5 Wilkinson normwise perturbation surface. Rounded GEPP loop-to-certificate construction remains open. |
| Theorem 9.5 pivoted det-only exact solve wrappers | `higham9_5_wilkinson_source_bound_exists_of_PartialPivotGEPPUTrace_of_det_ne_zero`, `higham9_5_wilkinson_source_bound_exists_of_CompletePivotGECPUTrace_of_det_ne_zero`, `higham9_16_wilkinson_source_bound_exists_of_RookPivotGEUTrace_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for using the existing recursive trace-existence theorems to enter the partial-, complete-, and rook-pivoting exact trace-to-solve Wilkinson perturbation surfaces directly from `det A != 0`; sharp complete-/rook-pivoting product bounds and rounded pivot-loop certificates remain open. |
| Theorem 9.10 upper-Hessenberg exact trace-to-solve bridge | `higham9_10_HessenbergGEPPUTrace_to_PartialPivotGEPPUTrace`, `higham9_10_wilkinson_source_bound_exists_of_HessenbergGEPPUTrace`, `higham9_10_wilkinson_source_bound_exists_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for forgetting the upper-Hessenberg GEPP trace to the ordinary partial-pivoting trace surface, reusing the cumulative exact `PA = LU` certificate construction, and applying the Hessenberg trace growth bound `rho <= n` to get a source-facing Wilkinson normwise perturbation witness for nonsingular upper-Hessenberg inputs. Complex/fully algorithmic and rounded componentwise Hessenberg coverage remains open. |
| Equation (9.16), recursive rook-pivoting `U` trace support and elementary trace growth | `higham9_16_RookPivotGEUTrace`, `higham9_16_RookPivotGEUTrace_upper_zero`, `higham9_16_rookPivot_firstSchurComplement_entry_abs_le_two`, `higham9_16_rookPivot_firstSchurComplement_maxEntryNorm_le_two`, `higham9_16_RookPivotGEUTrace_entry_abs_le_pow_two`, `higham9_16_RookPivotGEUTrace_growthFactorEntry_le_pow_two`, `higham9_16_exists_RookPivotGEUTrace_of_det_ne_zero`, `higham9_16_exists_RookPivotGEUTrace_upper_zero_of_det_ne_zero`, `higham9_16_exists_RookPivotGEUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for constructing an explicit recursive rook-pivoting upper-factor trace for every nonsingular real matrix, using complete-pivot maxima as valid rook pivots plus row/column first-pivot swaps and Schur-complement determinant inheritance; proves the exposed `U` rows are upper triangular, proves the elementary cumulative trace bound `rho <= 2^(n-1)`, and packages the nonsingular source-facing existential growth theorem under the standard positive max-entry side condition. This is not Foster's sharper rook-pivoting product bound. |
| Equation (9.16), rook-pivoting trace growth-value endpoint | `higham9_16_rookPivotingUTraceGrowthValues`, `higham9_16_rookPivotingUTraceGrowthSup`, `higham9_16_rookPivotingUTraceGrowthValues_le_pow_two`, `higham9_16_rookPivotingUTraceGrowthValues_bddAbove`, `higham9_16_rookPivotingUTraceGrowth_le_sup`, `higham9_16_rookPivotingUTraceGrowthValues_nonempty`, `higham9_16_rookPivotingUTraceGrowthSup_le_pow_two` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the trace-level value set, supremum, direct elementary value upper bound, boundedness proof, `le_sup` adapter, positive-dimensional nonemptiness, and source-shaped supremum upper bound for recursive rook-pivoting traces; Foster's sharper product bound remains open. |
| Equation (9.16), rook-pivoting exact trace-to-solve bridge | `higham9_16_RookPivotGEUTrace_exists_CompletePermutedLUFactSpec_L_bound_maxEntryNorm_le`, `higham9_16_wilkinson_source_bound_exists_of_RookPivotGEUTrace` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for turning a recursive rook-pivoting exact trace into a complete-permuted exact LU certificate with visible unit lower multipliers and `U` max-entry norm bounded by the trace, then feeding the elementary trace growth theorem into the Theorem 9.5 Wilkinson normwise perturbation surface. Foster's sharper product theorem and rounded pivot-loop certificate construction remain open. |
| Problem 9.4, row- and complete-pivoted LU solve backward-error analogues | `higham_problem9_4_permuted_lu_solve_backward_error`, `higham_problem9_4_complete_permuted_lu_solve_backward_error` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the source permutation analogues of Theorem 9.4: row-pivoted solves use `P b` and unpermute perturbation rows; complete-pivoted solves use `P b`, return `x_j = z_(Q^{-1}j)`, and unpermute perturbation rows and columns. These reuse the already available Split-1 gamma/triangular-solve theorem rather than assuming a new stability result. |
| Problem 9.11 and equation (9.12), block-doubling algebra, `g(n)` supremum adapter, and sine-matrix finite-sum/inverse/theta support | `higham9_11_blockMatrix`, `higham9_11_blockInverseCandidate`, `higham9_11_flatBlockIndex`, `higham9_11_flatInnerIndex`, `higham9_11_flattenTwoBlock`, `higham9_11_flatIndexOfBlock`, `higham9_11_flatBlockIndex_flatIndexOfBlock`, `higham9_11_flatInnerIndex_flatIndexOfBlock`, `higham9_11_flattenTwoBlock_entry_flatIndexOfBlock`, `higham9_11_flattenTwoBlock_maxEntryNorm_eq_blockMaxNorm`, `higham9_11_blockInverseCandidate_left`, `higham9_11_blockInverseCandidate_right`, `higham9_11_alpha_block_eq`, `higham9_11_flatten_blockMatrix_maxEntryNorm_eq`, `higham9_11_beta_blockInv_eq`, `higham9_11_flatten_blockInverseCandidate_maxEntryNorm_eq`, `higham9_11_theta_block_eq_two_theta`, `higham9_11_sine_block_theta_candidate_ge_succ`, `higham9_11_complete_pivoting_lower_bound_from_sine_block_theta`, `higham9_11_complete_pivoting_lower_bound_consequence`, `higham9_11_complete_pivoting_lower_bound_consequence_le`, `higham9_completePivotGrowthSet`, `higham9_completePivotGrowthSup`, `higham9_completePivotGrowth_le_sup`, `higham9_11_complete_pivoting_lower_bound_from_witness`, `higham9_11_complete_pivoting_lower_bound_from_witness_le`, `higham9_11_complete_pivoting_lower_bound_from_flattened_sine_block`, `higham9_11_complete_pivoting_lower_bound_from_flattened_sine_block_maxEntry`, `higham9_12_sineMatrix`, `higham9_12_sineMatrix_symm`, `higham9_12_sineMatrix_entry_abs_le_scale`, `higham9_12_sineMatrix_maxEntryNorm_le_scale`, `higham9_12_sineMatrix_zero_zero_pos`, `higham9_12_sineMatrix_maxEntryNorm_pos`, `higham9_12_cos_sum_even`, `higham9_12_cos_sum_odd`, `higham9_12_cos_sum_pos_lt_two_mul`, `higham9_12_cos_sum_eq_of_mod_two_eq`, `higham9_12_sine_product_sum`, `higham9_12_sineMatrix_mul_self`, `higham9_12_sineMatrix_inverse_formula`, `higham9_12_theta_ge_half_succ_of_maxEntryNorm_le_scale`, `higham9_12_two_theta_ge_succ_of_maxEntryNorm_le_scale`, `higham9_12_sineMatrix_theta_candidate_ge_half_succ`, `higham9_12_sineMatrix_two_theta_candidate_ge_succ` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the appendix block inverse, `alpha(B)=alpha(A)`, `beta(B)=beta(A)/2`, `theta(B)=2 theta(A)`, the block-doubled sine theta lower bound, the final arithmetic consequence under equality or inequality hypotheses, the visible-witness, flattened sine-block, flattened max-entry lower-bound bridges, equality- and inequality-form supremum adapters, and the source equation (9.12) sine matrix definition, symmetry, entrywise/max-entry scale bounds, positivity, finite cosine/sine orthogonality sums, self-inverse certificate, and theta lower-bound arithmetic. The trace-level `g(2n)` lower-bound consequence is closed by the dedicated row above. |
| Theorem 9.10, upper-Hessenberg GEPP trace growth-value/supremum endpoint | `higham9_10_hessenbergGEPPUTraceGrowthValues`, `higham9_10_hessenbergGEPPUTraceGrowthSup`, `higham9_10_hessenbergGEPPUTraceGrowthValues_le_card`, `higham9_10_hessenbergGEPPUTraceGrowthValues_bddAbove`, `higham9_10_hessenbergGEPPUTraceGrowth_le_sup`, `higham9_10_hessenbergGEPPUTraceGrowthValues_nonempty`, `higham9_10_hessenbergGEPPUTraceGrowthSup_le_card` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED in this continuation for the source-facing positive-dimensional value set, supremum, direct value bound `rho <= n`, boundedness proof, `le_sup` adapter, identity-matrix nonempty witness, and supremum upper bound. This is a trace-family navigation endpoint and does not close the remaining complex/fully algorithmic Hessenberg coverage or the sharp complete-/rook-pivoting product bounds. |
| Problem 9.11, concrete flattened sine-block complete-pivoting witness | `higham9_11_flatIndexOfBlock_flatBlockIndex_flatInnerIndex`, `higham9_11_flatBlockInner_eq_iff`, `higham9_11_flatBlockEquiv`, `higham9_11_flattenTwoBlock_matMul_entry`, `higham9_11_flattenTwoBlock_right_inverse`, `higham9_det_ne_zero_of_isRightInverse`, `higham9_11_exists_completePivoting_sine_block_growth_ge_succ` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for transporting the displayed block right inverse through the flattened `Fin (2*n)` surface, deriving nonsingularity from a visible right inverse, and instantiating the cumulative real complete-pivoting theorem on the flattened sine block to prove a genuine `P B Q = L U` certificate with `growthFactorEntry(B,U) >= n + 1`. The global trace-level source `g(2n)` lower bound is closed by the dedicated trace-level row; Wilkinson's sharp product upper-bound theorem remains separate equation (9.14) work. |
| Problem 9.11, fixed sine-block complete-pivoting growth-value bridge | `higham9_11_sineBlockCompletePivotingGrowthSet`, `higham9_11_sineBlockCompletePivotingGrowthSet_exists_ge_succ`, `higham9_11_sineBlockCompletePivotingGrowth_upper_bound_ge_succ` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the fixed-matrix bridge: the set of actual exact complete-pivoting certificate growth values for the flattened sine block contains a value at least `n + 1`, and any upper bound for that fixed set is at least `n + 1`. The global trace-level source `g(2n)` lower bound is closed by the dedicated trace-level row; Wilkinson's sharp product upper-bound theorem remains separate equation (9.14) work. |
| Problem 9.11, certificate-level `g(n)` surface and sine-block lower bound | `higham9_completePivotingCertificateGrowthSet`, `higham9_completePivotingCertificateGrowthValues`, `higham9_completePivotingCertificateGrowthSup`, `higham9_completePivotingCertificateGrowth_le_sup`, `higham9_11_completePivotingCertificateGrowthValues_exists_ge_succ`, `higham9_11_completePivotingCertificateGrowthSup_ge_succ` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for replacing the old arbitrary-`rhoC` global-growth interface by a certificate-level complete-pivoting growth-value set and supremum: every value comes from an explicit exact `PAQ = LU` certificate, the flattened sine block contributes a global certificate-level value at least `n + 1`, and the flattened sine block proves `n + 1 <= g(2n)` for this certificate-level surface once its values are known bounded above. The remaining source gap is exactly the Wilkinson complete-pivoting boundedness/upper-bound theorem, not Split 1 and not a missing sine-block witness. |
| Equation (9.13), complex Fourier/Vandermonde matrix definition, full Gram support, inverse formula, complex `theta <= n`, theta witness, and conditional growth bridge | `higham9_13_fourierVandermonde`, `higham9_13_fourierVandermonde_symm`, `higham9_13_fourierVandermonde_firstRow`, `higham9_13_fourierVandermonde_firstCol`, `higham9_13_fourierVandermonde_norm`, `higham9_13_fourierVandermonde_conj_mul_self`, `higham9_13_fourierVandermonde_column_norm_sq`, `higham9_13_fourierVandermonde_row_norm_sq`, `higham9_13_fourierRoot_pow_card`, `higham9_13_fourierRoot_ne_one`, `higham9_13_fourierRoot_geometric_sum_zero`, `higham9_13_fourierVandermonde_conj_mul_eq_pow_of_col_lt`, `higham9_13_fourierVandermonde_column_orthogonal_of_lt`, `higham9_13_fourierVandermonde_column_orthogonal`, `higham9_13_fourierVandermonde_column_gram`, `higham9_13_fourierVandermonde_row_orthogonal`, `higham9_13_fourierVandermonde_row_gram`, `higham9_13_fourierVandermondeScaledAdjoint`, `higham9_13_scaledAdjoint_mul_fourierVandermonde`, `higham9_13_fourierVandermonde_mul_scaledAdjoint`, `higham9_13_fourierVandermonde_inverse_formula`, `higham9_13_complexMaxEntryNorm`, `higham9_13_entry_norm_le_complexMaxEntryNorm`, `higham9_13_inverse_row_identity_le_card_mul_complexMaxEntryNorm`, `higham9_8_theta_le_card_complex`, `higham9_13_fourierVandermonde_complexMaxEntryNorm_eq_one`, `higham9_13_fourierVandermondeScaledAdjoint_norm`, `higham9_13_fourierVandermondeScaledAdjoint_complexMaxEntryNorm_eq_inv`, `higham9_13_fourierVandermonde_theta_eq_card`, `higham9_13_complexGrowthFactorEntry`, `higham9_8_complexGrowthFactorEntry_ge_inverse_entry_theta`, `higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the source complex Vandermonde/Fourier matrix definition, symmetry, first row/column identities, unit-circle entry norm, roots-of-unity cancellation, full row/column Gram identities, entrywise `V_n^{-1} = n^{-1}V_nᴴ` two-sided inverse formula, the general complex max-entry `theta <= n` row-identity estimate, the complex max-entry `theta(V_n)=n` witness, and the conditional complex max-entry growth bridge `n <= rho` once a pivot trace supplies the final-pivot inverse-entry witness; that trace construction remains open |
| Equations (9.14) and (9.16), complete-/rook-pivoting scalar upper-bound RHS surfaces | `higham9_14_completePivotWilkinsonProduct`, `higham9_14_completePivotWilkinsonBound`, `higham9_14_completePivotWilkinsonProduct_nonneg`, `higham9_14_completePivotWilkinsonProduct_pos`, `higham9_14_completePivotWilkinsonBound_nonneg`, `higham9_14_completePivotWilkinsonBound_pos`, `higham9_16_rookPivotFosterBound`, `higham9_16_rookPivotFosterBound_nonneg`, `higham9_16_rookPivotFosterBound_pos` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the displayed scalar RHS definitions and nonnegativity/positivity only; the Wilkinson complete-pivoting upper-bound theorem and Foster rook-pivoting upper-bound theorem remain open Split-2 work, while the recursive complete- and rook-pivoting `U` trace existence/upper-triangularity support is now recorded separately |
| Theorem 9.9 diagonal-dominance nonsingularity side condition | `higham9_9_rowDiagDominant_zero_diag_row_zero`, `higham9_9_colDiagDominant_zero_diag_col_zero`, `higham9_9_rowDiagDominant_diag_ne_zero_of_det_ne_zero`, `higham9_9_colDiagDominant_diag_ne_zero_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the source parenthetical that a nonsingular row- or column-diagonally-dominant matrix has nonzero diagonal entries; the actual diagonal-dominance LU/growth theorem remains open Split-2 work |
| Theorem 9.9 diagonal-dominance off-diagonal and first-ratio bounds | `higham9_9_rowDiagDominant_offdiag_abs_le_diag`, `higham9_9_colDiagDominant_offdiag_abs_le_diag`, `higham9_9_rowDiagDominant_entry_ratio_abs_le_one`, `higham9_9_colDiagDominant_entry_ratio_abs_le_one`, `higham9_9_rowDiagDominant_entry_ratio_abs_le_one_of_det_ne_zero`, `higham9_9_colDiagDominant_entry_ratio_abs_le_one_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the local diagonal-dominance fact that each off-diagonal entry is bounded by its diagonal and hence the visible first no-pivot column ratio is unit-bounded under nonsingularity; the full source growth theorem is recorded separately as `DEFER-LATER-CHAPTER` through Chapter 13 |
| Theorem 9.9 column-dominant exact no-pivot LU support | `higham9_9_colDiagDominant_first_column_multiplier_sum_le_one`, `higham9_9_colDiagDominant_first_column_multiplier_sum_except_le`, `higham9_9_colDiagDominant_firstSchurComplement`, `higham9_9_colDiagDominant_firstSchurComplement_maxEntryNorm_le_two`, `higham9_9_colDiagDominant_firstSchurComplement_offdiag_le_maxEntryNorm`, `higham9_9_colDiagDominant_firstSchurComplement_det_ne_zero`, `higham9_9_colDiagDominant_lu_exists_unit_lower_of_det_ne_zero`, `higham9_9_colDiagDominant_lu_exists_unique_unit_lower_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the first-column no-pivot multiplier-sum bound, preservation of column diagonal dominance, the first-step max-entry Schur-complement bound by `2 * maxEntryNorm A`, the sharper first-step off-diagonal bound by `maxEntryNorm A`, nonsingularity by the first Schur-complement step, and exact no-pivot LU existence/uniqueness for nonsingular column-diagonally-dominant matrices with unit-bounded lower factor entries; the full max-entry growth theorem `rho_n <= 2` remains open Split-2 work |
| Theorem 9.9 diagonal-dominance growth-factor endpoint adapter | `growthFactorEntry_le_of_entry_bound_factor`, `higham9_9_growthFactorEntry_le_two_of_upper_entry_bound` | `LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean`, `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for converting a final-upper entrywise bound `|U_ij| <= 2 * maxEntryNorm A` into Higham's max-entry growth conclusion `rho <= 2`; the full source proof of that final-upper bound is deferred to Chapter 13 Theorems 13.7/13.8 under this prompt's Chapter 13/14 exclusion |
| Problem 9.13, threshold-pivoting sparse-column growth bound | `higham9_13_thresholdFactor`, `higham9_13_threshold_update_abs_bound`, `higham9_13_column_growth_by_modification_count`, `higham9_13_growthFactorEntry_bound_from_column_modifications` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the source argument that per-column modification counts give `rho_n <= (1 + tau^{-1})^muMax` |
| Problem 9.14, pre-pivoted GEPP no-interchange LU side | `higham_problem9_14_PrePivotedGEPP`, `higham9_7_PartialPivotNoInterchangeTrace_reindex_time`, `higham9_7_PartialPivotNoInterchangeTrace_exists_LUFactSpec`, `higham9_7_PartialPivotNoInterchangeTrace_exists_LUFactSpec_pivots_ne_zero`, `higham9_7_PartialPivotNoInterchangeTrace_det_ne_zero`, `higham_problem9_14_PrePivotedGEPP_exists_LUFactSpec`, `higham_problem9_14_PrePivotedGEPP_det_ne_zero`, `higham_problem9_14_PrePivotedGEPP_lu_unique`, `higham_problem9_14_PrePivotedGEPP_exists_unique_LUFactSpec`, `higham_problem9_14_PrePivotedGEPP_firstSchurComplement` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the dependency that a source pre-pivoted/no-interchange GEPP trace yields exact no-pivot LU factors with nonzero pivots, nonsingularity, ordinary exact-LU uniqueness for `A`, stage-counter reindexing, and the recursive handoff that the first Schur complement is again pre-pivoted; the first §9.9 method and row-reversal pairwise branches are closed by the recursive certificate rows below |
| Problem 9.14, generic right-dominant pairwise elimination step | `higham_problem9_14_pairPivotEliminateToLeft_left_eq_right_of_abs_le`, `higham_problem9_14_pairPivotEliminateToLeft_target_eq_left_sub_right`, `higham_problem9_14_pairPivotEliminateToLeft_target_active_eq_zero_of_abs_le`, `higham_problem9_14_pairPivotEliminateToLeft_target_abs_le_two_of_abs_le` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the local pairwise-pivoting dependency that a right row with dominant active-column magnitude is moved into the left pivot slot, the old right-row slot receives the exact elimination update, the active entry is zeroed when the dominant pivot is nonzero, and the target row obeys the factor-two row-budget bound. This is the reusable bubble-step lemma needed by the cumulative row-reversal/pairwise trace; it is retained as a local dependency feeding the closed recursive Problem 9.14 branches. |
| Problem 9.14, pair-step row-shape invariant | `higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_of_ne_pair` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the local dependency that a right-dominant pair pivot-and-eliminate step leaves every row outside the compared pair unchanged, with the pre-pivoted row-reversal specialization needed by the cumulative bubble-trace induction. This trace-shape dependency feeds the closed recursive pairwise branch. |
| Problem 9.14, one-step next-selector invariant | `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_active_ne_zero`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_unchanged_abs_le_pivot` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the local dependency that, after one pre-pivoted row-reversal pair step, the moved source pivot row still has a nonzero active entry and every unchanged row remains dominated by it in the active column. This is the selector invariant needed to continue the adjacent-pair bubble trace; this feeds the closed recursive pairwise branch. |
| Problem 9.14, two-step bubble trace support | `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_next_pairPivotRow`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_row` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the local dependency that, after one bubble step, the next adjacent pair selects the moved source pivot row and a second pair pivot-and-eliminate step moves that same row one position further left. This is a two-step trace-shape dependency, not the full cumulative trace equivalence. |
| Problem 9.14, two-step induction invariants | `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_of_ne_triple`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_active_ne_zero`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_unchanged_abs_le_pivot` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the local dependency that after two adjacent pair steps, rows outside the three touched positions are unchanged, the twice-moved pivot row is still nonzero in the active column, and untouched rows remain dominated by it. These are induction invariants for a future cumulative bubble trace; this feeds the closed recursive pairwise branch. |
| Problem 9.14, recursive pairwise-bubble schedule and trace | `higham_problem9_14_pairwiseBubbleRow`, `higham_problem9_14_pairwiseBubbleRow_zero`, `higham_problem9_14_pairwiseBubbleRows_adjacent`, `higham_problem9_14_pairwiseBubbleRows_distinct`, `higham_problem9_14_pairwiseBubbleRow_succ_val_lt`, `higham_problem9_14_pairwiseBubbleRow_self`, `higham_problem9_14_pairwiseBubbleMatrix`, `higham_problem9_14_pairwiseBubbleMatrix_zero`, `higham_problem9_14_pairwiseBubbleMatrix_succ`, `higham_problem9_14_PairwiseBubbleTrace`, `higham_problem9_14_pairwiseBubbleMatrix_trace`, `higham_problem9_14_pairwiseBubbleMatrix_terminal_trace`, `higham_problem9_14_pairwiseBubbleMatrix_det_ne_zero`, `higham_problem9_14_pairwiseBubbleMatrix_terminal_det_ne_zero`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_invariant`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_pivot_row`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_pivot_active_ne_zero`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_eliminated_active_eq_zero`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_active_eq_zero_of_ne_zero`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_one_pivot_row`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_two_pivot_row` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the local dependency that the source row-reversal pairwise-pivoting bubble has an explicit adjacent-row schedule, a recursive exact matrix state, a source-facing trace predicate, a proved terminal trace, determinant preservation/nonsingularity for every prefix and terminal state, a general prefix invariant, terminal row-zero pivot-row/nonzero-pivot corollaries, and a separate eliminated-column invariant showing that all rows below the carried pivot have zero active-column entries. The one-/two-step scheduled row-motion bridges are retained as source-facing special cases. This pairwise trace is connected recursively by the pairwise LU certificate row below; the first §9.9 method branch is closed separately. |
| Problem 9.14, terminal pairwise-bubble Schur bridge | `higham_problem9_14_pairwiseBubbleSourceRow`, `higham_problem9_14_pairwiseBubbleSourceRow_succ`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_eliminated_row`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_trailing_eq_rowReversed_firstSchurComplement`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_firstSchurComplement_eq_rowReversed_firstSchurComplement` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the next local dependency: every already-eliminated row in the scheduled pairwise bubble is proved to be the exact first-column Schur update of its source row, the terminal trailing block is exactly the row reversal of `luFirstSchurComplement A`, and the first Schur complement of the terminal full matrix is that same row-reversed Schur complement. This connects the terminal pairwise trace to the first no-interchange Schur step; this feeds the closed recursive pairwise branch until this bridge is iterated recursively and packaged with the exact-LU uniqueness result. |
| Problem 9.14, recursive row-reversal pairwise trace package | `higham_problem9_14_RecursivePairwiseBubbleTrace`, `higham_problem9_14_RecursivePairwiseBubbleTrace_of_PrePivotedGEPP` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the local recursive trace-existence dependency: a pre-pivoted input admits the source-facing row-reversal pairwise-bubble trace that performs the scheduled terminal bubble, identifies the terminal first Schur complement with the row-reversed no-interchange Schur complement, and recurses. This is still an intermediate trace package, not the final same-LU factorization theorem. |
| Problem 9.14, recursive pairwise LU certificate and same-LU bridge | `higham_problem9_14_RecursivePairwiseLUFactSpec`, `higham_problem9_14_RecursivePairwiseLUFactSpec_to_LUFactSpec`, `higham_problem9_14_exists_RecursivePairwiseLUFactSpec_of_PrePivotedGEPP`, `higham_problem9_14_RecursivePairwiseLUFactSpec_same_as_PrePivotedGEPP` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the modeled pairwise-pivoting LU branch: the recursive pairwise certificate records each scheduled row-reversal bubble and terminal Schur bridge, yields an ordinary exact `LUFactSpec`, exists for every pre-pivoted GEPP input, and has the same exact factors as any GEPP/no-interchange LU certificate by uniqueness. The first-method branch is closed by the following first-method certificate row. |
| Problem 9.14, first §9.9 method trace/LU certificate and same-LU bridge | `higham_problem9_14_firstMethodTarget`, `higham_problem9_14_firstMethodMatrix`, `higham_problem9_14_FirstMethodTrace`, `higham_problem9_14_firstMethodMatrix_trace`, `higham_problem9_14_firstMethodMatrix_det_ne_zero`, `higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_prefix_invariant`, `higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_multiplier_abs_le_one`, `higham_problem9_14_PrePivotedGEPP_firstMethodMatrix_terminal_firstSchurComplement`, `higham_problem9_14_RecursiveFirstMethodTrace`, `higham_problem9_14_RecursiveFirstMethodTrace_of_PrePivotedGEPP`, `higham_problem9_14_RecursiveFirstMethodLUFactSpec`, `higham_problem9_14_RecursiveFirstMethodLUFactSpec_to_LUFactSpec`, `higham_problem9_14_exists_RecursiveFirstMethodLUFactSpec_of_PrePivotedGEPP`, `higham_problem9_14_RecursiveFirstMethodLUFactSpec_same_as_PrePivotedGEPP` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for branch (a): the first §9.9 method is modeled on the original pre-pivoted matrix `A`, with row-zeroing targets `2,3,...,n`; pre-pivoting proves the multiplier bounds, the terminal first Schur complement is the ordinary `luFirstSchurComplement A`, recursive first-method factors exist, and exact-LU uniqueness gives the same `L,U` as GEPP. Branch (b) is the separate row-reversal pairwise certificate above. |
| Problem 9.14, row-reversal permutation and first-column pivot surface | `higham_problem9_14_rowReversal`, `higham_problem9_14_rowReversal_involutive`, `higham_problem9_14_rowReversal_isPermutation`, `higham_problem9_14_rowReversal_zero_eq_last`, `higham_problem9_14_rowReversal_last_eq_zero`, `higham_problem9_14_rowReversedMatrix`, `higham_problem9_14_rowReversedMatrix_involutive`, `higham_problem9_14_rowReversedMatrix_det_ne_zero`, `higham_problem9_14_rowReversedMatrix_firstColumn_partialPivotChoice_last`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot`, `higham_problem9_14_adjacentRows`, `higham_problem9_14_pairRowSwap`, `higham_problem9_14_pairRowSwap_left`, `higham_problem9_14_pairRowSwap_right`, `higham_problem9_14_pairRowSwap_involutive`, `higham_problem9_14_pairRowSwap_isPermutation`, `higham_problem9_14_pairRowSwap_det_ne_zero`, `higham_problem9_14_pairPivotChoice`, `higham_problem9_14_exists_pairPivotChoice`, `higham_problem9_14_pairPivotRow`, `higham_problem9_14_pairPivotRow_choice`, `higham_problem9_14_pairPivotRow_eq_right_of_abs_le`, `higham_problem9_14_pairPivotRow_eq_left_of_abs_gt`, `higham_problem9_14_pairPivotRow_eq_right_of_firstColumn_partialPivotChoice`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotRow_last`, `higham_problem9_14_pairPivotToLeftSwap`, `higham_problem9_14_pairPivotToLeftSwap_left`, `higham_problem9_14_pairPivotToLeftSwap_isPermutation`, `higham_problem9_14_pairPivotToLeftMatrix`, `higham_problem9_14_pairPivotToLeftMatrix_left`, `higham_problem9_14_pairPivotToLeftMatrix_det_ne_zero`, `higham_problem9_14_pairPivotChoice_multiplier_abs_le_one`, `higham_problem9_14_pairPivotChoice_left_multiplier_abs_le_one`, `higham_problem9_14_pairPivotChoice_right_multiplier_abs_le_one`, `higham_problem9_14_pairPivotRow_left_multiplier_abs_le_one`, `higham_problem9_14_pairPivotRow_right_multiplier_abs_le_one`, `higham_problem9_14_pairEliminateRow`, `higham_problem9_14_pairEliminateRow_target`, `higham_problem9_14_pairEliminateRow_of_ne`, `higham_problem9_14_pairEliminateRow_pivot`, `higham_problem9_14_pairEliminateRow_target_active_eq_zero`, `higham_problem9_14_pairEliminateRow_eq_updateRow_add_smul`, `higham_problem9_14_pairEliminateRow_det_eq`, `higham_problem9_14_pairEliminateRow_det_ne_zero`, `higham_problem9_14_pairPivotEliminateToLeft`, `higham_problem9_14_pairPivotEliminateToLeft_target`, `higham_problem9_14_pairPivotEliminateToLeft_of_ne`, `higham_problem9_14_pairPivotEliminateToLeft_pivot`, `higham_problem9_14_pairPivotEliminateToLeft_multiplier_abs_le_one`, `higham_problem9_14_pairPivotEliminateToLeft_left`, `higham_problem9_14_pairPivotEliminateToLeft_target_active_eq_zero`, `higham_problem9_14_pairPivotEliminateToLeft_det_ne_zero`, `higham_problem9_14_rowReversedMatrix_pairPivotEliminateToLeft_det_ne_zero`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_row`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_row`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_abs_le_two`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_maxEntryNorm_le_two`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_growthFactorEntry_le_two`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_active_eq_zero`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_multiplier_abs_le_one`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_normalized_multiplier_abs_le_one`, `higham_problem9_14_rowReversedMatrix_maxEntryNorm`, `higham_problem9_14_rowReversedMatrix_maxEntryNorm_pos`, `higham_problem9_14_rowReversedMatrix_growthFactorEntry_eq` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the source permutation `Π = I(n:-1:1,:)`, its involution/bijection/endpoint facts, preservation of nonsingularity under `ΠA`, the matrix-level identity `Π(ΠA)=A`, max-entry-norm preservation, the corresponding growth-factor denominator bridge, the first-column fact that pre-pivoting of `A` makes the last row of `ΠA` a valid nonzero first partial pivot, the adjacent-row predicate and determinant-preserving pair row-swap primitive, both existential and deterministic natural two-row pairwise pivot choices, selector tie-breaking/first-column-last-row consequences, pivot-to-left permutation/nonsingularity support, and unit-bounded multipliers, and the exact pairwise row-operation primitive plus one-step pivot-and-eliminate wrapper with row-shape facts, row-reversed determinant preservation, unit multiplier bound, and pre-pivoted row-reversal first-column pivot-row/target-row/target-bound/max-entry/growth-quotient specialization that zeros the target active-column entry while preserving determinant/nonsingularity for distinct pivot and target rows; the recursive pairwise branch is closed by the certificate rows above |
| Theorem 9.9 / Theorem 9.13 row-column orientation adapters | `higham9_9_colDiagDominant_transpose_iff_rowDiagDominant`, `higham9_9_rowDiagDominant_transpose_iff_colDiagDominant`, `higham9_13_tridiagonal_transpose_iff` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the real-transpose row/column diagonal-dominance bridge and tridiagonal transpose preservation; the remaining general diagonal-dominance growth work is recorded under Theorem 9.9, while direct row-dominant tridiagonal certificate growth is recorded under Theorem 9.13 |
| Theorem 9.13 tridiagonal diagonally-dominant componentwise and max-entry growth consequences | `growthFactorEntry_le_of_absLU_componentwise`, `maxEntryNorm_matTranspose`, `LUFactSpec.isTridiagLU_of_tridiagonal`, `tridiag_colDom_L_entries_bounded`, `tridiag_rowDom_growth_bound_3`, `higham9_13_tridiag_growth_bound_3_of_LUFactSpec`, `higham9_13_growthFactorEntry_le_three_of_LUFactSpec`, `higham9_13_colDiagDom_L_entries_bounded_of_LUFactSpec`, `higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec`, `higham9_13_colDiagDom_growthFactorEntry_le_three_of_LUFactSpec`, `higham9_13_colDiagDom_exists_LUFactSpec_growth_bound_3`, `higham9_13_colDiagDom_exists_LUFactSpec_growthFactorEntry_le_three`, `higham9_13_rowDiagDom_transpose_exists_LUFactSpec_growth_bound_3`, `higham9_13_rowDiagDom_transpose_exists_LUFactSpec_growthFactorEntry_le_three`, `higham9_13_LUFactSpec_of_transpose_LUFactSpec_nonzero_pivots`, `higham9_13_rowDiagDom_exists_LUFactSpec_growth_bound_3`, `higham9_13_rowDiagDom_exists_LUFactSpec_growthFactorEntry_le_three`, `higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec`, `higham9_13_rowDiagDom_growthFactorEntry_le_three_of_LUFactSpec`, `higham9_13_tridiag_growthFactorEntry_le_three`, `higham9_13_rowDiagDom_transpose_tridiag_growth_bound_3`, `higham9_13_rowDiagDom_transpose_growthFactorEntry_le_three`, `higham9_13_rowDiagDom_transpose_growthFactorEntry_le_three_of_Amax`, `higham9_13_rowDiagDom_tridiag_growth_bound_3`, `higham9_13_rowDiagDom_growthFactorEntry_le_three` | `LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean`, `LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean`, `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for applying the local column-dominant tridiagonal growth theorem to explicit bidiagonal LU certificates, deriving bidiagonal LU structure from exact `LUFactSpec` plus source tridiagonality and nonzero pivots, deriving the column-dominant multiplier bound from column diagonal dominance, packaging exact no-pivot LU existence with column-dominant componentwise and max-entry growth, packaging the row-dominant transpose exact-LU/growth endpoint for factors of `Aᵀ`, converting exact LU factors of `Aᵀ` with nonzero pivots into direct unit-lower/upper exact LU factors of `A`, packaging the direct row-dominant exact-LU/growth endpoint for factors of `A`, proving the direct row-dominant tridiagonal componentwise bound for both explicit bidiagonal LU and ordinary exact-LU certificates of `A`, deriving the Higham max-entry growth-factor bound `rho <= 3`, transporting componentwise and max-entry conclusions to `Aᵀ`, and normalizing the transposed denominator with `maxEntryNorm Aᵀ = maxEntryNorm A`; remaining work is general special-class exact-LU existence not already covered by explicit `LUFactSpec`/recurrence hypotheses and executable algorithmic trace coverage |
| Theorem 9.13 source-data tridiagonal builder growth surface | `tridiag_L_lower_bidiag`, `tridiag_U_upper_bidiag`, `tridiag_matrices_isTridiagLU`, `tridiag_L_matrix_entries_bounded`, `tridiag_prevIndex`, `TridiagExactLURecurrence`, `tridiag_exact_product_of_recurrence`, `higham9_19_TridiagExactLURecurrence`, `higham9_19_tridiag_prevIndex`, `higham9_19_tridiag_exact_product_of_recurrence`, `higham9_19_tridiag_LUFactSpec_of_exact_product`, `higham9_19_tridiag_LUFactSpec_of_recurrence`, `higham9_13_tridiag_builder_growth_bound_3`, `higham9_13_tridiag_builder_growthFactorEntry_le_three`, `higham9_13_rowDiagDom_tridiag_builder_growth_bound_3`, `higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three`, `higham9_13_tridiag_builder_growth_bound_3_of_recurrence`, `higham9_13_tridiag_builder_growthFactorEntry_le_three_of_recurrence`, `higham9_13_rowDiagDom_tridiag_builder_growth_bound_3_of_recurrence`, `higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three_of_recurrence` | `LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean`, `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for removing the separate `IsTridiagLU` hypothesis when the factors are the explicit `tridiag_L_matrix`/`tridiag_U_matrix` builders over source `TridiagData`; the exact recurrence-to-product theorem now discharges the exact-product certificate from equation (9.19) in the exact-arithmetic recurrence branch, and the same exact-product certificate is available as an ordinary `LUFactSpec` for downstream exact-factor wrappers. The multiplier or row-dominance hypotheses remain visible, and the rounded algorithmic recurrence trace is not claimed |
| Theorem 9.12 special-class max-entry growth consequence | `tridiag_spd_shape_absLU_eq_absA`, `higham9_12_spd_tridiag_absLU_eq_of_positive_DLT`, `higham9_12_spd_tridiag_lu_backward_error_of_positive_DLT`, `higham9_growthFactorEntry_le_one_of_absLU_le_absA`, `higham9_12_spd_tridiag_growthFactorEntry_le_one`, `higham9_12_spd_tridiag_growthFactorEntry_le_one_of_spd`, `higham9_12_spd_tridiag_builder_absLU_eq_of_positive_DLT`, `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one`, `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_spd`, `higham9_12_spd_tridiag_builder_lu_backward_error_of_positive_DLT`, `higham9_12_spd_tridiag_builder_absLU_eq_of_recurrence`, `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_recurrence`, `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_spd_recurrence`, `higham9_12_spd_tridiag_builder_lu_backward_error_of_recurrence`, `higham9_12_nonneg_lu_growthFactorEntry_le_one`, `higham9_12_nonneg_lu_growthFactorEntry_le_one_of_det_ne_zero`, `higham9_12_mmatrix_lu_growthFactorEntry_le_one`, `higham9_12_mmatrix_lu_growthFactorEntry_le_one_of_det_ne_zero`, `higham9_12_sign_equiv_growthFactorEntry_le_one`, `higham9_12_sign_equiv_growthFactorEntry_le_one_of_det_ne_zero`, `higham9_12_totalNonnegative_exists_LUFactSpec_optimal_growth`, `higham9_12_totalNonnegative_exists_LUFactSpec_growthFactorEntry_le_one`, `higham9_12_totalNonnegative_exists_LUFactSpec_growthFactorEntry_le_one_exists_hAmax`, `higham9_14_totalNonnegative_exists_source_h_bound_of_models`, `higham9_14_totalNonnegative_exists_source_f_bound_actual_triangular_solves` | `LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean`, `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the SPD positive-`D L^T` algebraic core `|L||U| = |LU| = |A|` under an explicit tridiagonal LU certificate, its builder and equation-(9.19) exact-recurrence forms, its backward-error handoffs, the max-entry growth consequence `rho <= 1`, and source-facing SPD variants that derive the positive max-entry denominator from SPD nonsingularity; also closed for converting any optimal componentwise `|L||U| <= |A|` bound and unit lower diagonal into `rho <= 1`, for the nonnegative-LU, M-matrix, and sign-equivalent factor specializations including determinant-derived positive-denominator variants, for the total-nonnegative/nonsingular source-existence branch via Problem 9.6 including its determinant-derived positive-denominator variant, and for the corresponding total-nonnegative model-consuming Theorem 9.14 final `h(u)|A|` package plus exact-factor/actual triangular-solve `f(u)|A|` package. Remaining source existence/class coverage is recorded in the inventory row. |
| Problem 9.2, Appendix A finite-exception shifted-matrix LU theorem | `higham9_2_danger_shift_count_bound`, `higham9_2_charpolyDangerSet`, `higham9_2_mem_charpolyDangerSet_iff_isRoot`, `higham9_2_mem_charpolyDangerSet_iff_det_shift_eq_zero`, `higham9_2_charpolyDangerSet_card_le`, `higham9_2_charpoly_danger_shift_count_bound`, `higham9_2_leadingPrincipalBlock`, `higham9_2_leadingBlockDangerSet`, `higham9_2_shiftedLeadingBlock`, `higham9_2_mem_leadingBlockDangerSet_iff_det_shift_eq_zero`, `higham9_2_shiftedLeadingBlock_det_ne_zero_of_not_mem_danger_union`, `higham9_2_leadingBlockDangerSet_card_le`, `higham9_2_leadingBlockDangerSet_count_bound`, `higham9_2_shiftedMatrix`, `higham9_2_shiftedMatrixDangerSet`, `higham9_2_shiftedMatrixDangerSet_card_le`, `higham9_2_shiftedMatrix_properLeadingPrincipalBlock_det_ne_zero_of_not_mem_danger`, `higham9_2_shiftedMatrix_lu_exists_unique_of_not_mem_danger`, `higham_problem9_2_shiftedMatrix_lu_exists_unique_except_card_bound` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the `1 + 2 + ... + (n-1) = n(n-1)/2` danger-value count, the characteristic-polynomial root/determinant-shift cardinality bridge, the source union over leading principal blocks of a concrete matrix, the implication from avoiding that union to nonzero shifted-block determinants, and the final source-facing theorem that outside a set of at most `n(n-1)/2` shifts the matrix `sigma I - A` has a unique exact no-pivot LU factorization via Theorem 9.1 |
| Theorem 9.14 / equations (9.20)--(9.22), source perturbation models and scalar `f(u)`/`h(u)` aggregation | `higham9_20_tridiag_lu_perturbation_model`, `higham9_21_tridiag_solve_perturbation_model`, `higham9_14_f`, `higham9_14_h`, `higham9_14_h_eq_f_div`, `higham9_14_f_nonneg`, `higham9_14_h_mul_one_sub_eq_f`, `higham9_20_tridiag_lu_perturbation_model_of_LUBackwardError_le`, `higham9_21_tridiag_solve_perturbation_model_of_fl_triangular_solves_gamma_le`, `LUFactSpec.to_LUBackwardError_zero`, `higham9_14_source_f_bound`, `higham9_22_source_f_bound_of_9_20_9_21_models`, `higham9_14_source_h_bound_of_absLUhat_bound`, `higham9_14_source_h_bound_of_absLUhat_mul_one_sub_bound`, `higham9_14_source_h_bound_of_9_20_9_21_models_absLUhat_bound`, `higham9_14_source_h_bound_of_9_20_9_21_models_absLUhat_mul_one_sub_bound`, `higham9_14_source_h_bound_of_absLU_le_absA_and_9_20_9_21_models`, `higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models`, `higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le`, `higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma`, `higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_builders`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_LUFactSpec`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUFactSpec`, `higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_models`, `higham9_14_nonnegative_lu_source_h_bound_of_models`, `higham9_14_mmatrix_lu_source_h_bound_of_models`, `higham9_14_sign_equiv_source_h_bound_of_models`, `higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves`, `higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_spd`, `higham9_14_nonnegative_lu_source_f_bound_actual_triangular_solves`, `higham9_14_mmatrix_lu_source_f_bound_actual_triangular_solves`, `higham9_14_sign_equiv_source_f_bound_actual_triangular_solves`, `higham9_14_totalNonnegative_exists_source_h_bound_of_models`, `higham9_14_totalNonnegative_exists_source_f_bound_actual_triangular_solves`, `higham9_14_colDiagDom_exists_LUFactSpec_source_f_bound_of_models`, `higham9_14_rowDiagDom_exists_LUFactSpec_source_f_bound_of_models`, `higham9_14_colDiagDom_exists_LUFactSpec_source_f_bound_actual_triangular_solves`, `higham9_14_rowDiagDom_exists_LUFactSpec_source_f_bound_actual_triangular_solves` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the explicit source model surfaces for equations (9.20) and (9.21), the printed scalar polynomial, nonnegativity, denominator-cleared `h(u)=f(u)/(1-u)` relation, the coefficient-dominance production bridges from existing `LUBackwardError` and actual triangular-solve certificates, the exact-LU zero-coefficient bridge and exact-factor/actual triangular-solve `f(u)` wrappers, the algebraic aggregation of the source perturbation coefficients into the printed `f(u)`, both divided and source-shaped `(1-u)|Lhat||Uhat| <= |A|` conditional `h(u)` bounds including model-consuming variants, the constant-growth model bridge `|Lhat||Uhat| <= c|A| -> c f(u)|A|`, the composed certificate-based constant-growth `f(u)` wrappers, builder, exact-recurrence, and ordinary exact-`LUFactSpec` `3 f(u)|A|` wrappers for column/direct-row diagonal dominance, the final model-consuming `h(u)|A|` step for SPD positive-`D L^T`, nonnegative-LU, M-matrix LU, and sign-equivalent optimal-growth surfaces plus their exact-factor/actual triangular-solve `f(u)|A|` endpoints, including the SPD variant that derives nonsingularity from `IsSymPosDef`, the total-nonnegative/nonsingular existential package and exact-factor/actual triangular-solve `f(u)|A|` endpoint, and the column/direct-row diagonally-dominant exact-LU source-data `3 f(u)|A|` packages including exact-factor plus actual triangular-solve endpoints; the sharper all-class rounded tridiagonal recurrence proof remains open |
| Theorem 9.14, structural tridiagonal absorbed/source-model backward-error specialization | `higham9_14_tridiag_diagDom_fu_bound_from_structural_growth`, `higham9_14_tridiag_rowDiagDom_fu_bound_from_structural_growth`, `higham9_14_tridiag_colDiagDom_fu_bound_from_LUFactSpec`, `higham9_14_tridiag_rowDiagDom_fu_bound_from_LUFactSpec`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_LUFactSpec`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUFactSpec`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves`, `LUFactSpec.to_LUBackwardError_zero`, `higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le`, `higham9_14_colDiagDom_exists_LUFactSpec_fu_bound`, `higham9_14_rowDiagDom_exists_LUFactSpec_fu_bound`, `higham9_14_colDiagDom_exists_LUFactSpec_source_f_bound_of_models`, `higham9_14_rowDiagDom_exists_LUFactSpec_source_f_bound_of_models`, `higham9_14_colDiagDom_exists_LUFactSpec_source_f_bound_actual_triangular_solves`, `higham9_14_rowDiagDom_exists_LUFactSpec_source_f_bound_actual_triangular_solves` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for instantiating the absorbed `3 gamma_6` backward-error theorem with local Theorem 9.13 tridiagonal growth proofs under explicit bidiagonal-LU/exact-product hypotheses, under ordinary exact `LUFactSpec` certificates for nonsingular column- or row-diagonally-dominant tridiagonal matrices, and under source-data existential exact-LU packages that choose the column- or direct row-dominant factors before exposing the perturbation hypotheses; also CLOSED for the model-consuming `3 f(u)|A|` source form from ordinary exact-LU certificates and from the same source-data factors with explicit equation (9.20)/(9.21) perturbation models, plus certificate-producing exact-LU variants that use coefficient-dominated `LUBackwardError` and actual triangular solves, and exact-factor variants that derive the LU model with coefficient zero before applying the actual triangular solves; the full source all-class theorem remains open |
| Theorem 9.14 source-data builder absorbed/source-model backward-error specialization | `higham9_14_tridiag_colDiagDom_fu_bound_from_builders`, `higham9_14_tridiag_rowDiagDom_fu_bound_from_builders`, `higham9_14_tridiag_colDiagDom_fu_bound_from_recurrence`, `higham9_14_tridiag_rowDiagDom_fu_bound_from_recurrence`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_builders`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_LUBackwardError_fl_triangular_solves`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_LUBackwardError_fl_triangular_solves`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence_LUBackwardError_fl_triangular_solves`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence_LUBackwardError_fl_triangular_solves`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence_LUFactSpec_fl_triangular_solves`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence_LUFactSpec_fl_triangular_solves` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for instantiating the structural `3 gamma_6` absorbed theorem and the source-model `3 f(u)|A|` equation-(9.22) theorem with the explicit `TridiagData` matrix builders; the exact-recurrence variants discharge the exact-product certificate from equation (9.19), the certificate-producing variants combine coefficient-dominated `LUBackwardError` with actual triangular solves, and the exact-factor variants convert the builder/recurrent product certificate to `LUFactSpec` before applying actual triangular solves with zero LU-factorization coefficient. The fully rounded all-class tridiagonal algorithmic trace remains open. |
| Problem 9.5, exact 2 by 2 counterexample | `higham9_5_problemA`, `higham9_5_problemL`, `higham9_5_problemU`, `higham9_5_problem_lu_product`, `higham9_5_problem_abs_lu_bottom_right`, `higham9_5_problem_no_componentwise_bound` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED |
| Problem 9.6, source total-nonnegative determinant and first Schur-update support | `higham9_6_twoByTwoSubmatrix`, `higham9_6_firstSchurUpdate`, `higham9_6_threeByThreeSubmatrix`, `higham9_6_IsTotallyNonnegative`, `higham9_6_totalNonnegative_submatrix`, `higham9_6_IsTotallyNonnegativeOrderTwo`, `higham9_6_totalNonnegative_entry_nonneg`, `higham9_6_totalNonnegative_twoByTwoSubmatrix_det_nonneg`, `higham9_6_totalNonnegative_to_orderTwo`, `higham9_6_twoByTwoSubmatrix_det`, `higham9_6_pivot_mul_schur_twoByTwo_det_eq_threeByThree_det`, `higham9_6_pivot_mul_schur_det_eq_source_minor`, `higham9_6_totalNonnegative_threeByThreeSubmatrix_det_nonneg`, `higham9_6_schur_twoByTwo_det_nonneg_of_totalNonnegative`, `higham9_6_twoByTwo_determinantal_inequality`, `higham9_6_totalNonnegativeOrderTwo_entry_nonneg`, `higham9_6_multiplier_nonneg_of_orderTwo`, `higham9_6_schur_update_nonneg_of_orderTwo`, `higham9_6_schur_update_le_original_of_orderTwo`, `higham9_6_abs_schur_update_le_abs_entry_of_orderTwo`, `higham9_6_schur_update_nonneg_of_totalNonnegative`, `higham9_6_abs_schur_update_le_abs_entry_of_totalNonnegative`, `higham9_6_firstSchurUpdate_trailing_orderTwo_of_totalNonnegative`, `higham9_6_firstSchurUpdate_trailing_totalNonnegative_of_totalNonnegative`, `higham9_6_firstSchurUpdate_trailing_nonneg_of_totalNonnegative`, `higham9_6_firstSchurUpdate_trailing_abs_le_original_of_totalNonnegative`, `higham9_6_firstSchurUpdate_trailing_maxEntryNorm_le_original`, `maxEntryNorm_submatrix_le`, `higham9_6_firstSchurUpdate_trailing_maxEntryNorm_le_source` | `LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean`, `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the source all-square-minors predicate, inherited-submatrix lemma, its `1 by 1` and `2 by 2` adapters to the order-two support predicate, the local `2 by 2` minor determinant formula, local and arbitrary-size denominator-cleared Schur determinant identities, nonnegative selected `3 by 3` source minors, determinantal inequality, nonnegative first multiplier, first Schur-update no-growth facts, first-step all-minors total-nonnegativity preservation on strictly trailing square submatrices, trailing nonnegativity/absolute-entry/max-entry no-growth, max-entry no-growth relative to the full source matrix, and order-two trailing-minor preservation used by the appendix argument |
| Problem 9.6, leading-principal first-Schur determinant identity | `higham9_6_pivot_mul_firstSchur_leadingPrincipalBlock_det_eq` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the leading-principal-block specialization of the arbitrary-size denominator-cleared first-pivot Schur determinant identity: the first pivot times the `k by k` leading determinant of the first Schur complement equals the `(1+k) by (1+k)` leading determinant of the source matrix. This was used in the now-closed Koteljanskii/Fischer route and is not an assumption of that inequality. |
| Problem 9.6, block Desnanot/Sylvester Schur determinant core, source reindexing adapters, and adjacent source-indexed inequality bridge | `higham9_6_desnanot_schur_core`, `higham9_6_desnanot_schur_core_inequality`, `higham9_6_desnanot_schur_core_inequality_of_offdiag_product_nonneg`, `higham9_6_middleEndpointsEquiv`, `higham9_6_det_middleEndpoints_fromBlocks_eq_source`, `higham9_6_middleEndpoint0LeadingEquiv`, `higham9_6_middleEndpoint1TrailingEquiv`, `higham9_6_det_middleEndpoint0_fromBlocks_eq_leadingPrincipalBlock`, `higham9_6_det_middleEndpoint1_fromBlocks_eq_trailingPrincipalBlock`, `higham9_6_adjacent_desnanot_inequality_of_offdiag_product_nonneg` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the pure block determinant identity behind the adjacent-minor condensation route, its immediate inequality corollaries under explicit nonnegativity of either the two off-diagonal bordered determinants or their product, the source-indexed determinant adapters for `[1,\dots,m,0,m+1]`, `[1,\dots,m,0]`, and `[1,\dots,m,m+1]`, and the adjacent source-indexed determinant inequality under the explicit off-diagonal bordered-minor product side condition. This is local algebraic infrastructure; the product-side condition is now derived from total nonnegativity by `higham9_6_adjacent_offdiag_product_nonneg_of_totalNonnegative`, and the full Koteljanskii/Fischer inequality is closed by `higham9_6_principalBlock_determinantal_inequality_of_totalNonnegative`. |
| Problem 9.6, principal-block positivity, recursive nonnegative LU construction, and growth endpoints | `higham9_6_trailingPrincipalBlock`, `higham9_6_totalNonnegative_leadingPrincipalBlock_det_nonneg`, `higham9_6_totalNonnegative_trailingPrincipalBlock_det_nonneg`, `higham9_6_totalNonnegative_det_nonneg`, `higham9_6_totalNonnegative_det_pos_of_det_ne_zero`, `higham9_6_principalBlock_determinantal_inequality_of_det_eq_zero`, `higham9_6_principalBlock_determinantal_inequality_zero`, `higham9_6_principalBlock_determinantal_inequality_full`, `higham9_6_principalBlock_determinantal_inequality_fin_two`, `higham9_6_middle_entry_pos_of_fin_three_totalNonnegative_det_pos`, `higham9_6_principalBlock_determinantal_inequality_fin_three_one_of_middle_pos`, `higham9_6_principalBlock_determinantal_inequality_fin_three_one`, `higham9_6_principalBlock_determinantal_inequality_fin_three_two_of_middle_pos`, `higham9_6_principalBlock_determinantal_inequality_fin_three_two`, `higham9_6_topLeft_pos_of_totalNonnegative_det_ne_zero`, `higham9_6_leadingPrincipalBlock_det_pos_of_totalNonnegative_det_ne_zero`, `higham9_6_principalBlock_dets_pos_of_determinantal_inequality`, `higham9_6_leadingPrincipalBlock_det_pos_of_determinantal_inequality`, `luFirstStepL`, `luFirstStepU`, `LUFactSpec.of_firstSchurComplement_explicit`, `higham9_6_luFirstStepL_nonneg`, `higham9_6_luFirstStepU_nonneg`, `higham9_6_lu_exists_nonnegative_of_totalNonnegative_and_leadingPrincipalBlock_pos`, `higham9_6_lu_exists_nonnegative_of_totalNonnegative_and_properLeadingPrincipalBlock_pos`, `higham9_6_lu_exists_nonnegative_of_totalNonnegative_det_ne_zero`, `higham9_6_nonnegativeLU_growthFactorEntry_le_one`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_and_properLeadingPrincipalBlock_pos`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_and_properLeadingPrincipalBlock_pos_exists_hAmax`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero_exists_hAmax`, `higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_det_ne_zero`, `higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_det_ne_zero_exists_hAmax`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_and_principalBlock_inequalities`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_and_principalBlock_inequalities_exists_hAmax`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero_and_principalBlock_inequalities`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero_and_principalBlock_inequalities_exists_hAmax`, `higham9_5_rectPrefixRange_nonneg_of_nonnegative_factors`, `higham9_5_rectPrefixRange_le_full_of_nonnegative_factors`, `higham9_6_reducedEntry_abs_le_maxEntryNorm_of_nonnegative_LU`, `higham_problem9_9_noPivotReducedGrowthFactor_le_one_of_nonnegative_LU`, `higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_and_principalBlock_inequalities`, `higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_and_principalBlock_inequalities_exists_hAmax`, `higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_det_ne_zero_and_principalBlock_inequalities`, `higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_det_ne_zero_and_principalBlock_inequalities_exists_hAmax` | `LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean`, `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for deriving `det A > 0` from total nonnegativity and nonsingularity, proving the source-cited determinant inequality in the singular `det A = 0` branch, the `p = 0` and `p = n` boundary cases, and the `2 by 2`, `p = 1` base case plus both `3 by 3` interior cases (`p = 1` and `p = 2`), proving first-pivot positivity and then all nonempty leading principal determinants positive by Schur-complement induction, constructing exact nonnegative no-pivot LU factors directly from the source hypotheses, proving both final-`U` max-entry growth and reduced-matrix no-pivot growth `rho_n <= 1`, adding source wrappers that derive the positive growth denominator from nonsingularity or from the positive determinant in the principal-block route, and proving the arbitrary-p Koteljanskii/Fischer determinant comparison. The appendix inference from the cited inequality to positive principal determinants remains recorded, and the nonsingular higher-dimensional Koteljanskii/Fischer determinant comparison is now closed by `higham9_6_principalBlock_determinantal_inequality_of_totalNonnegative`. |
| Problem 9.7, submatrix counts | `higham9_7_square_submatrix_count_with_empty`, `higham9_7_rectangular_submatrix_count_with_empty`, `higham9_7_square_submatrix_count_nonempty`, `higham9_7_rectangular_submatrix_count_nonempty` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED; nonempty forms match the problem wording, with-empty forms record the Vandermonde convention |
| Problem 9.8, checkerboard sign-matrix, inverse transport, full selected-minor Jacobi theorem, LU adapter, and total-nonnegative-checkerboard support | `higham9_8_alternatingSign`, `higham9_8_signMatrixJ`, `higham9_8_checkerboardConjugate`, `higham9_8_abs_alternatingSign`, `higham9_8_signMatrixJ_diag`, `higham9_8_signMatrixJ_offdiag`, `higham9_8_signMatrixJ_left_mul`, `higham9_8_signMatrixJ_right_mul`, `higham9_8_abs_checkerboardConjugate`, `higham9_8_alternatingSign_sq`, `higham9_8_selection_index_le_value`, `higham9_8_neg_one_pow_sub_eq_mul`, `higham9_8_selectedFinset_orderEmbOfFin_eq`, `higham9_8_selectionComplementEquiv_eq_finSumEquivOfFinset`, `higham9_8_selected_below_card`, `higham9_8_complement_below_card`, `higham9_8_prod_if_neg_one_eq_pow_card`, `higham9_8_cross_complement_product_eq_pow`, `higham9_8_selection_card_le`, `higham9_8_canonicalSelectionComplementEquiv`, `higham9_8_canonicalSelectionComplementEquiv_inl`, `higham9_8_canonicalSelectionComplementEquiv_inr_val`, `higham9_8_prod_Ioi_castAdd_split`, `higham9_8_prod_Ioi_natAdd`, `higham9_8_selectionComplementEquiv_canonical_shuffle_sign_eq_cross_prod`, `higham9_8_selectionComplementEquiv_canonical_shuffle_sign`, `higham9_8_selectionComplementEquiv_perm_sign_of_canonical_shuffle_signs`, `higham9_8_selectionComplementEquiv_perm_sign`, `higham9_8_signMatrixJ_involutive`, `higham9_8_signMatrixJ_mul_mul_eq_checkerboardConjugate`, `higham9_8_det_inv_topLeft_fromBlocks_eq_det_D_mul_inv_det`, `higham9_8_det_inv_topLeft_fromBlocks_mul_det_eq_det_D`, `higham9_8_det_inv_selected_eq_det_complement_mul_inv_det_reindexed`, `higham9_8_det_inv_selected_mul_det_reindexed_eq_det_complement`, `higham9_8_checkerboardConjugate_nonsingInv_principal_minor_nonneg_of_complement_det_ne_zero`, `higham9_8_det_selectionComplementEquiv_reindex_eq_perm_sign`, `higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg_of_complement_det_ne_zero_of_reindex_det`, `higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg_of_complement_det_ne_zero_of_perm_sign`, `higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg_of_complement_det_ne_zero`, `higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg`, `higham9_8_checkerboardConjugate_id`, `higham9_8_checkerboardConjugate_left_inverse`, `higham9_8_checkerboardConjugate_right_inverse`, `higham9_8_checkerboardConjugate_inverse`, `higham9_8_checkerboardConjugate_inverse_swapped`, `higham9_8_succAbove_val_strictMono`, `higham9_8_checkerboardConjugate_nonsingInv_entry_nonneg_of_det_pos`, `higham9_8_checkerboardConjugate_nonsingInv_entry_nonneg_of_det_ne_zero`, `higham9_8_checkerboardConjugate_nonsingInv_empty_minor_nonneg`, `higham9_8_checkerboardConjugate_nonsingInv_orderOne_minor_nonneg`, `higham9_8_adjugate_nonsingInv_eq_det_nonsingInv_smul`, `higham9_8_checkerboardConjugate_nonsingInv_codimOne_minor_nonneg`, `higham9_8_checkerboardConjugate_det_eq`, `higham9_8_checkerboardConjugate_nonsingInv_det_nonneg`, `higham9_8_checkerboardConjugate_nonsingInv_full_order_minor_nonneg`, `higham9_8_checkerboardConjugate_minor_det_scale`, `higham9_8_abs_checkerboardConjugate_minor_det`, `higham9_8_checkerboardConjugate_involutive`, `higham9_8_checkerboardConjugate_eq_abs_of_nonneg`, `higham9_8_checkerboardConjugate_matMul`, `higham9_8_checkerboard_lu_product_eq`, `higham9_8_lu_of_checkerboard_lu`, `higham9_8_abs_conjugated_lu_product_eq_abs`, `higham9_8_abs_lu_product_eq_abs_of_checkerboard_totalNonnegative_and_pos`, `higham9_8_abs_lu_product_eq_abs_of_checkerboard_principalBlock_inequalities` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | CLOSED for the local alternating-sign matrix definitions, diagonal/off-diagonal facts, `J^2 = I`, row/column multiplication by `J`, selected-index counting/parity, sorted-finset split adapters, selected/complement below-count and cross-block product lemmas, canonical one-sided shuffle formulas, and the full selected/complement permutation-sign theorem, `J*A*J` agreement with entrywise checkerboard conjugation, identity preservation and left/right/two-sided inverse transport under checkerboard conjugation, the Schur-complement/top-left and arbitrary selected-minor Jacobi identities both with and without the complementary-minor nonsingularity hypothesis, the conditional principal-minor and nonsingular-complement nonnegativity consequences for `J A^{-1} J`, the full arbitrary selected-minor nonnegativity theorem `higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg`, the cofactor-level entrywise checkerboard sign pattern for `nonsingInv` of a nonsingular totally nonnegative matrix, the empty-, `1 by 1`, codimension-one, full-determinant, and full-order minor nonnegativity wrappers for `J A^{-1} J`, full determinant preservation under checkerboard conjugation, absolute-value preservation, all-minor determinant scaling and absolute-minor preservation under checkerboard conjugation, `J`-conjugation product algebra, induced LU certificate, componentwise `|JLJ||JUJ| = |A|` adapter under explicit nonnegative LU factors, and the total-nonnegative-checkerboard route to those factors using the recursive Problem 9.6 theorem under visible hypotheses. |

### Chapter 9 External Proof-Source Bottlenecks

These rows track source-cited proof bottlenecks audited during the Chapter 9
pass. Problem 9.6 and Problem 9.8 are now closed locally; neither row has an
unresolved Split 1 blocker.

| Source row | Current classification | Previous-split dependency | Source-cited imported theorem | Local closure already proved | Smallest remaining theorem |
| --- | --- | --- | --- | --- | --- |
| Problem 9.6 source hint inequality | CLOSED | No integrated previous-split blocker | Koteljanskii/Fischer-style principal determinant inequality for totally nonnegative matrices, cited in Chapter 9 Problem 9.6 as `[454, 1959, p. 100]`: `det A <= det A(1:p,1:p) * det A(p+1:n,p+1:n)` | The main Problem 9.6 conclusion is now closed without this inequality: source total-nonnegative minor API, Schur determinant identities, first-pivot positivity, all leading principal determinant positivity from total nonnegativity plus `det A != 0`, recursive nonnegative no-pivot LU construction, final-`U` max-entry growth, and reduced-matrix no-pivot growth endpoints are proved. The singular `det A = 0` branch is proved by `higham9_6_principalBlock_determinantal_inequality_of_det_eq_zero`, the `p = 0` and `p = n` boundary cases are proved by `higham9_6_principalBlock_determinantal_inequality_zero` and `higham9_6_principalBlock_determinantal_inequality_full`, the `2 by 2`, `p = 1` base case is proved by `higham9_6_principalBlock_determinantal_inequality_fin_two`, and both `3 by 3` interior cases are proved by `higham9_6_middle_entry_pos_of_fin_three_totalNonnegative_det_pos`, `higham9_6_principalBlock_determinantal_inequality_fin_three_one_of_middle_pos`, `higham9_6_principalBlock_determinantal_inequality_fin_three_one`, `higham9_6_principalBlock_determinantal_inequality_fin_three_two_of_middle_pos`, and `higham9_6_principalBlock_determinantal_inequality_fin_three_two`; the appendix adapter from this inequality to positive principal determinants remains available. The reordered block Desnanot identity and inequality corollaries are proved by `higham9_6_desnanot_schur_core`, `higham9_6_desnanot_schur_core_inequality`, and `higham9_6_desnanot_schur_core_inequality_of_offdiag_product_nonneg`; the source-indexed determinant adapters and adjacent conditional bridge are proved by `higham9_6_det_middleEndpoints_fromBlocks_eq_source`, `higham9_6_det_middleEndpoint0_fromBlocks_eq_leadingPrincipalBlock`, `higham9_6_det_middleEndpoint1_fromBlocks_eq_trailingPrincipalBlock`, and `higham9_6_adjacent_desnanot_inequality_of_offdiag_product_nonneg`. The off-diagonal bordered-minor product side condition is proved by `higham9_6_adjacent_offdiag_product_nonneg_of_totalNonnegative`, and the arbitrary-p Koteljanskii/Fischer comparison is closed by `higham9_6_principalBlock_determinantal_inequality_of_totalNonnegative`. | Closed by `higham9_6_adjacent_offdiag_product_nonneg_of_totalNonnegative` and `higham9_6_principalBlock_determinantal_inequality_of_totalNonnegative` |
| Problem 9.8 | CLOSED | No integrated previous-split blocker | Jacobi/complementary-minor inverse theorem, cited in Appendix A Problem 9.8 as `[26, 1987, Thm. 3.3]`: if `C` is totally nonnegative and nonsingular, then `J C^{-1} J` is totally nonnegative | Checkerboard algebra, inverse transport, selected/complement sorted-finset adapters, canonical split reduction, one-sided shuffle formulas, the full selected/complement permutation-sign theorem, Schur-complement/top-left and selected-minor Jacobi identities, the no-complement-nonsingularity block determinant identity `higham9_8_det_inv_topLeft_fromBlocks_mul_det_eq_det_D`, the selected-minor identity `higham9_8_det_inv_selected_mul_det_reindexed_eq_det_complement`, cofactor/empty/order-one/codimension-one/full-order wrappers, and the full selected-minor nonnegativity theorem `higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg` | Closed; no remaining theorem for Problem 9.8 |
| Theorem 9.11 Bohte banded GEPP growth theorem | PROVE-NOW-SPLIT | No integrated previous-split blocker | Bohte's banded partial-pivoting growth theorem, cited in Chapter 9 Theorem 9.11 as `Bohte [146, 1975]`: if `A` has upper and lower bandwidth `p`, then `rho_n^p <= 2^(2p-1) - (p-1)2^(p-2)`, with near attainability for `n = 2p + 1` | Local scalar and example support is closed by `higham9_11_bohteBound`, `higham9_11_bohteBound_nonneg`, `higham9_11_bohteBound_tridiagonal`, `higham9_11_bohteBound_pentadiagonal_formula`, `higham9_11_bohteBound_bandwidth_four_formula`, and `higham9_11_bohte_banded_solve_tight`. A source/PDF audit confirmed the chapter supplies no proof beyond the Bohte citation, and a quick primary-source search did not locate an accessible proof artifact. | Formalize the actual banded GEPP trace theorem: for every nonsingular banded matrix with equal lower/upper bandwidth `p`, recursive GEPP produces an upper-factor trace whose max-entry growth is bounded by `higham9_11_bohteBound p`, plus the near-attainability witness when the external proof route is explicit. |

Continuation note: `higham9_8_selectionComplementEquiv_perm_sign` proves
the pure selected/complement permutation-sign formula,
`higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg_of_complement_det_ne_zero`
retains the nonsingular-complement branch, and
`higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg` closes the full
arbitrary selected-minor case with no complementary-minor nonsingularity
hypothesis.

Public navigation was updated in `docs/LIBRARY_LOOKUP.md` and
`examples/LibraryLookup.lean`.

Continuation note: Theorem 9.10 now has the upper-Hessenberg GEPP trace
growth-value/supremum endpoint
`higham9_10_hessenbergGEPPUTraceGrowthValues`,
`higham9_10_hessenbergGEPPUTraceGrowthSup`,
`higham9_10_hessenbergGEPPUTraceGrowthValues_le_card`,
`higham9_10_hessenbergGEPPUTraceGrowthValues_bddAbove`,
`higham9_10_hessenbergGEPPUTraceGrowth_le_sup`,
`higham9_10_hessenbergGEPPUTraceGrowthValues_nonempty`, and
`higham9_10_hessenbergGEPPUTraceGrowthSup_le_card`. This closes the
source-facing trace-family value-set/supremum endpoint for the existing real
exact nonsingular upper-Hessenberg trace theorem; complex/fully algorithmic
Hessenberg coverage remains open.

Continuation note: Theorem 9.13 now has a direct row-dominant exact-LU
existential package for the source matrix `A`, not only for `Aᵀ`.  The bridge
`higham9_13_LUFactSpec_of_transpose_LUFactSpec_nonzero_pivots` rescales an
exact LU certificate of `Aᵀ` with nonzero pivots into unit-lower/upper exact
factors of `A`, and the source-facing wrappers
`higham9_13_rowDiagDom_exists_LUFactSpec_growth_bound_3` and
`higham9_13_rowDiagDom_exists_LUFactSpec_growthFactorEntry_le_three` combine
that construction with the direct row-dominant tridiagonal growth theorem.
The remaining tridiagonal work is executable trace coverage, rounded
perturbation-model production, and general special-class existence not already
covered by explicit `LUFactSpec`, recurrence, or direct row-dominant packages.

## Working Inventory

Classification values are exactly: `CLOSED`, `PROVE-NOW-SPLIT`,
`PROVE-NOW-SPLIT2`, `DEFER-LATER-SPLIT`, `DEFER-LATER-CHAPTER`, and `SKIP`.
Rows with `PROVE-NOW-SPLIT` are selected Split-2 work that remains open after
this pass; the open status is the reason the selected-scope gate fails.

### Primary Labels

| Source item | Classification | Previous-split dependency | Reason and Lean status |
| --- | --- | --- | --- |
| Theorem 9.1, LU existence/uniqueness iff nonsingular proper leading principal submatrices | CLOSED | No integrated previous-split blocker | The determinant-pivot product direction is closed by `higham9_1_det_eq_pivot_product` and `higham9_1_det_ne_zero_iff_pivots_ne_zero` for an exact LU certificate; the first-Schur-complement construction is closed by `higham9_1_lu_exists_of_firstSchurComplement`; the source-strength proper Schur-complement leading-minor inheritance step is closed by `higham9_1_firstSchurComplement_properLeadingPrincipalBlock_det_ne_zero`; exact LU existence and uniqueness from Higham's `k = 1 : n-1` condition are closed by `higham9_1_lu_exists_and_unique_of_properLeadingPrincipalBlock_det_ne_zero`; the converse, including the singular case isolated in Problem 9.1, is closed by `higham_problem9_1_properLeadingPrincipalBlock_det_ne_zero_of_unique_lu` and the source iff is packaged as `higham9_1_lu_exists_unique_iff_properLeadingPrincipalBlock_det_ne_zero`. |
| Algorithm 9.2, Doolittle method | PROVE-NOW-SPLIT | No integrated previous-split blocker | Square dense-loop certificate handoffs, row/complete-pivoted dense-loop and absolute-budget certificate adapters for `PA`/`PAQ`, the exact-target-gap-to-absolute-budget handoff, square exact-LU recurrence converse theorems, and rectangular exact source identities for (9.3)--(9.5) exist as `higham9_2_*`/`higham9_5_*`; the printed rational leading flop polynomial is recorded as `higham9_2_doolittleSourceFlopPolynomial`; the concrete executable rectangular/pivoting loops remain open. |
| Theorem 9.3, LU factorization backward error | PROVE-NOW-SPLIT | No integrated previous-split blocker for the remaining gap | Certificate forms `higham9_3_doolittle_backward_error`, `higham9_3_denseLoopCertificate_backward_error`, `higham9_3_absBudgetCertificate_backward_error`, `higham9_3_lu_backward_error_gamma`, the row-permuted pivoted adapters `higham9_3_permuted_lu_backward_error_gamma` and `higham9_3_permuted_lu_backward_error_gamma_of_LUFactSpec`, the row-column-permuted complete-pivoting adapters `higham9_3_complete_permuted_lu_backward_error_gamma` and `higham9_3_complete_permuted_lu_backward_error_gamma_of_LUFactSpec`, and the nonsingular complete-pivoted exact-certificate package `higham9_3_exists_complete_permuted_lu_backward_error_gamma_of_det_ne_zero` are closed using available Split-1 gamma algebra where needed. The full arbitrary rounded GE/pivoted executable surface depends on current Split-2 pivot traces and rectangular LU. |
| Theorem 9.4, LU solve backward error | CLOSED | Yes, direct previous-split reliance on already available Split-1 `gamma`/roundoff infrastructure | `higham9_4_lu_solve_backward_error` closes the square certificate form through `lu_solve_backward_error_tight`; the previous-split dependency is available, not an unproved hypothesis. |
| Theorem 9.5, Wilkinson GEPP normwise bound | PROVE-NOW-SPLIT | Yes, direct previous-split reliance on already available Split-1 `gamma` infrastructure for the closed certificate part | `higham9_5_wilkinson_normwise_infNorm_tight`, `higham9_5_wilkinson_source_bound_of_growth_bridge`, `higham9_5_wilkinson_source_bound_of_entry_growth`, `higham9_5_wilkinson_source_bound_of_PartialPivotGEPPUTrace`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_denseLoop`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_absBudget`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_literalSourceBudgets`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_componentDominance`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_exactProductMargins`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_exactProductNumeratorMargins`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_exactTargetGaps`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_LUFactSpec`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_denseLoop`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_absBudget`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_literalSourceBudgets`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_componentDominance`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_exactProductMargins`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_exactProductNumeratorMargins`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_exactTargetGaps`, and `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_LUFactSpec` are genuine. The max-entry-to-infinity bridge is closed, the explicit partial-pivoting and row-pivoted `U` trace specializations instantiate equation (9.10)'s `2^(n-1)` growth factor, and the complete-pivoted explicit-certificate wrapper is closed at the elementary trace-bound strength; the dense-loop, absolute-budget, literal source-budget, component-dominance, exact-product margin, exact-product numerator-margin, exact-target-gap, and exact-certificate variants remove free certificate layers. The remaining source gap is constructing the computed GEPP/GEPQ traces and their visible dense-loop/backward-error certificates from an executable pivoting loop. |
| Theorem 9.5, complete-pivot trace-derived exact solve wrapper | CLOSED for the exact trace/certificate surface; PROVE-NOW-SPLIT remains for rounded executable dense-loop production and the sharp product bound | Yes, direct previous-split reliance on available Split-1 `gamma` infrastructure for the solve perturbation certificate | `higham9_2_rowColPermutedMatrix_det_ne_zero`, `higham9_8_CompletePivotGECPUTrace_exists_CompletePermutedLUFactSpec_L_bound_maxEntryNorm_le`, `higham9_5_wilkinson_source_bound_of_CompletePermutedLUFactSpec_growth`, and `higham9_5_wilkinson_source_bound_exists_of_CompletePivotGECPUTrace` are genuine. A recursive complete-pivoting `U` trace now yields an exact cumulative `PAQ = LU` certificate with `|L_ij| <= 1`, transfers the certificate `U` growth through the trace `U`, and returns the Theorem 9.5 normwise perturbation witness at the elementary `2^(n-1)` strength. This does not prove the rounded GEPQ dense-loop certificate or Wilkinson's sharper complete-pivoting product estimate. |
| Lemma 9.6, no-pivot `|| |L||U| ||_inf` bound | CLOSED | No integrated previous-split blocker | The full-prefix, terminal-residual, rank-one stage estimate, stage-pair row-sum bridge, uniform row-budget accumulation, exact source counting, and the printed `1 + 2(n^2-n)rho_n` constant are closed by `higham9_5_rectPrefixRange_full_eq_matMul`, `higham9_5_rectGEReducedEntry_full_eq_zero_of_LUFactSpec`, `higham9_6_rankOne_abs_le_reduced_add_succ`, `higham9_6_absLU_infNorm_le_of_reduced_stage_pair_rows`, `higham9_6_absLU_infNorm_le_two_card_mul_of_reduced_stage_row_bounds`, `higham9_6_sum_stage_pair_eq_endpoints_add_two_range`, `higham9_6_absLU_infNorm_le_source_constant_of_reduced_entry_growth`, `higham9_6_absLU_infNorm_le_source_constant_of_noPivotReducedGrowthFactor`, and `higham9_6_absLU_infNorm_le_source_constant_of_noPivotReducedGrowthFactor_exists_hAmax`. |
| Theorem 9.7, extremal GEPP growth `2^(n-1)` | CLOSED | No integrated previous-split blocker | The first-step partial-pivoting max-entry doubling inequality is closed by `higham9_7_firstPivotRowSwap`, `higham9_7_partialPivot_firstSchurComplement_entry_abs_le_two`, and `higham9_7_partialPivot_firstSchurComplement_maxEntryNorm_le_two`; the stage recurrence to `growthFactorEntry <= 2^(n-1)` from explicit stage bounds is closed by `higham9_7_partialPivot_stageMax_le_pow_two` and `higham9_7_partialPivot_growthFactorEntry_le_pow_two_of_stage_bounds`; the arbitrary nonsingular recursive partial-pivoting `U` trace and source-facing exact growth upper bound are closed by `higham9_7_PartialPivotGEPPUTrace`, `higham9_7_PartialPivotGEPPUTrace_entry_abs_le_pow_two`, `higham9_7_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two`, `higham9_7_exists_PartialPivotGEPPUTrace_of_det_ne_zero`, and `higham9_7_exists_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero`; the trace-level source growth-value family and supremum upper-bound form are closed by `higham9_partialPivotingUTraceGrowthValues`, `higham9_partialPivotingUTraceGrowthSup`, `higham9_partialPivotingUTraceGrowthValues_bddAbove`, `higham9_partialPivotingUTraceGrowth_le_sup`, `higham9_partialPivotingUTraceGrowthValues_nonempty`, and `higham9_7_partialPivotingUTraceGrowthSup_le_pow_two`; the displayed Wilkinson matrix family is closed algebraically by `higham9_7_wilkinsonGrowth_lu`, `higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_eq_one`, `higham9_7_wilkinsonGrowthU_maxEntryNorm_eq_pow`, and `higham9_7_wilkinsonGrowth_growthFactorEntry_eq_pow`; the no-interchange partial-pivoting trace is closed by `higham9_7_wilkinsonGrowth_noInterchangeTrace`; and `higham9_7_wilkinsonGrowth_attains_partialPivoting_bound` plus `higham9_7_partialPivoting_growth_bound_and_attainment` package the selected real exact-arithmetic upper-bound and attainability statement. |
| Theorem 9.8, `theta <= n` and `rho >= theta` | PROVE-NOW-SPLIT for the broader complete-pivoting theorem family; CLOSED for the real/complex `theta <= rho` construction rows | No integrated previous-split blocker for the remaining gap | Real max-entry subclaims, the unpermuted exact-LU final-pivot/inverse-entry growth bridge, the explicit `P A Q = L U` complete-permuted inverse-entry instantiation, the cumulative real complete-pivoting `PAQ = LU` certificate existence theorem, the real complete-pivoting existential `theta <= rho` bridge, the recursive complete-pivoting `U` trace existence/upper-triangularity layer, the elementary recursive complete-pivoting trace growth bound `rho <= 2^(n-1)`, the trace-level Problem 9.11 `g(2n)` lower-bound bridge, the complex max-entry `theta <= n` row-identity estimate, the explicit complex `PAQ = LU` certificate-level final-pivot bridge for the Fourier/Vandermonde row, the complex recursive complete-pivoting trace construction, the complex cumulative `PAQ = LU` certificate construction, the complex trace-to-cumulative-certificate max-entry transfer, and the Fourier/Vandermonde trace-level `n <= rho` existence theorem are now closed. Remaining local work under this complete-pivoting family is the separate sharp Wilkinson complete-pivoting product upper-bound theorem for equation (9.14). |
| Theorem 9.9, diagonally dominant matrices | DEFER-LATER-CHAPTER for the full `rho_n <= 2` growth theorem; CLOSED for the local column-dominant no-pivot LU and multiplier support | No integrated previous-split blocker for the full growth theorem; later-Chapter-13 dependency. Equation (9.17) is now closed separately via Chapter 8 Lemma 8.8. | The source proof explicitly says the full row/column diagonal-dominance growth theorem follows from later Theorems 13.7 and 13.8 for block diagonally dominant matrices, so the prompt's Chapter 13/14 exclusion prevents proving that full source theorem locally. Local support is closed: conditional wrapper, nonsingular diagonal-entry side condition, row/column off-diagonal and first-ratio support, column-dominant first-column multiplier-sum, first Schur-complement preservation/max-entry/off-diagonal/nonsingularity support, exact no-pivot LU existence/uniqueness with unit-bounded lower multipliers, real-transpose row/column dominance adapters, and the final scalar adapter from `|U_ij| <= 2 * maxEntryNorm A` to `rho_n <= 2` all exist. |
| Theorem 9.10, upper Hessenberg GEPP growth | PROVE-NOW-SPLIT for source-general complex/algorithmic coverage; CLOSED for the selected real exact nonsingular `U`-trace growth theorem | No integrated previous-split blocker for the exact growth proof; direct reliance on available Split-1 `gamma` infrastructure for the closed solve wrapper | The first-stage and one-stage invariant Hessenberg GEPP trace support is closed by `higham9_7_firstPivotRowSwap_involutive`, `higham9_7_firstPivotRowSwap_isPermutation`, `higham9_7_firstPivotRowSwap_det_ne_zero`, `higham9_10_hessenberg_firstColumn_nonzero_row_le_one`, `higham9_10_exists_first_active_column_nonzero_of_det_ne_zero`, `higham9_10_exists_first_partialPivotChoice_pivot_ne_zero_of_det_ne_zero`, `higham9_10_hessenberg_firstPivotRowSwap_tail`, `higham9_10_hessenberg_firstSchurComplement_tail_rows_eq_original`, `higham9_10_hessenberg_firstSchurComplement_isUpperHessenberg`, `higham9_10_firstSchurComplement_det_ne_zero_of_det_ne_zero`, `higham9_10_hessenberg_firstSchurComplement_row_bound`, `higham9_10_HessenbergStageBound`, `higham9_10_hessenberg_firstSchurComplement_stageBound`, `higham9_10_HessenbergStageBound_one_of_maxEntryNorm`, `higham9_10_HessenbergGEPPTrace`, `higham9_10_HessenbergGEPPTrace_upperHessenberg_and_stageBound`, `higham9_10_HessenbergGEPPTrace_isUpperHessenberg`, `higham9_10_HessenbergGEPPTrace_stageBound`, `higham9_10_HessenbergGEPPTrace_stage_pos`, `higham9_10_HessenbergGEPPUTrace`, `higham9_10_HessenbergGEPPUTrace_upper_zero`, `higham9_10_HessenbergGEPPUTrace_row_bound`, `higham9_10_exists_HessenbergGEPPTrace_terminal`, `higham9_10_exists_HessenbergGEPPTrace_terminal_of_det_ne_zero`, `higham9_10_exists_HessenbergGEPPUTrace_of_trace_det_ne_zero`, `higham9_10_exists_HessenbergGEPPUTrace_of_det_ne_zero`, `higham9_10_HessenbergGEPPUTrace_growthFactorEntry_le_card`, and `higham9_10_exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_of_det_ne_zero`; the source scalar implication from the row-indexed pivot-row bound to `rho_n^p <= n` is closed by `higham9_10_hessenberg_growthFactorEntry_le_card_of_row_bounds`, and conditional factorization and solve backward-error consequences are closed by `higham9_10_hessenberg_growth_backward_error` and `higham9_10_hessenberg_lu_solve_backward_stable_tight`. The remaining source-general gap is complex-valued/fully algorithmic coverage, not the real exact nonsingular trace. |
| Theorem 9.11, banded GEPP growth formula | PROVE-NOW-SPLIT | No integrated previous-split blocker | Conditional solve bound exists, and the Bohte scalar expression, its nonnegativity, the tridiagonal `p = 1` arithmetic special case, the formal-expression `p = 2` arithmetic value `7`, the source `p = 4` arithmetic value `116`, and a solve wrapper specialized to the Bohte constant are closed by `higham9_11_bohteBound`, `higham9_11_bohteBound_nonneg`, `higham9_11_bohteBound_tridiagonal`, `higham9_11_bohteBound_pentadiagonal_formula`, `higham9_11_bohteBound_bandwidth_four_formula`, and `higham9_11_bohte_banded_solve_tight`. The book gives only `Proof. See Bohte [146, 1975]`; no Split 1 or later-chapter gate is involved, but the full banded GEPP growth proof and attainability now remain open as an external proof-source bottleneck rather than an assumed local certificate. |
| Theorem 9.12, tridiagonal special classes | PROVE-NOW-SPLIT | No integrated previous-split blocker | The SPD branch's local algebraic step is closed under the visible positive-`D L^T` tridiagonal LU certificate by `tridiag_spd_shape_absLU_eq_absA`, `higham9_12_spd_tridiag_absLU_eq_of_positive_DLT`, `higham9_12_spd_tridiag_growthFactorEntry_le_one`, `higham9_12_spd_tridiag_growthFactorEntry_le_one_of_spd`, and `higham9_12_spd_tridiag_lu_backward_error_of_positive_DLT`; the explicit `TridiagData` builder and equation-(9.19) exact-recurrence forms are closed by `higham9_12_spd_tridiag_builder_absLU_eq_of_positive_DLT`, `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one`, `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_spd`, `higham9_12_spd_tridiag_builder_lu_backward_error_of_positive_DLT`, `higham9_12_spd_tridiag_builder_absLU_eq_of_recurrence`, `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_recurrence`, `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_spd_recurrence`, and `higham9_12_spd_tridiag_builder_lu_backward_error_of_recurrence`. Other class-specific wrappers exist, and the optimal-growth-to-`rho <= 1` max-entry consequence is closed by `higham9_growthFactorEntry_le_one_of_absLU_le_absA`, `higham9_12_nonneg_lu_growthFactorEntry_le_one`, `higham9_12_mmatrix_lu_growthFactorEntry_le_one`, and `higham9_12_sign_equiv_growthFactorEntry_le_one`; full source derivation for all printed tridiagonal/special classes, including existence of the SPD `LDL^T`/LU certificate and the cited totally-nonnegative/M-matrix equivalence/existence results, is not complete. |
| Theorem 9.13, tridiagonal diagonally dominant `|L||U| <= 3|A|` and `rho <= 3` | PROVE-NOW-SPLIT | No integrated previous-split blocker | Column-dominant bidiagonal LU proof, column-dominant multiplier bound, direct row-dominant bidiagonal LU proof for `A` itself, exact-`LUFactSpec` to bidiagonal-structure handoff, generic componentwise-to-max-entry growth bridge, `rho <= 3` max-entry consequences, transpose/tridiagonal orientation adapters, ordinary exact-LU source-facing wrappers with `det A != 0`, column-dominant existential exact-LU growth wrappers `higham9_13_colDiagDom_exists_LUFactSpec_growth_bound_3` and `higham9_13_colDiagDom_exists_LUFactSpec_growthFactorEntry_le_three`, row-dominant transpose existential exact-LU growth wrappers `higham9_13_rowDiagDom_transpose_exists_LUFactSpec_growth_bound_3` and `higham9_13_rowDiagDom_transpose_exists_LUFactSpec_growthFactorEntry_le_three`, the transpose-LU rescaling bridge `higham9_13_LUFactSpec_of_transpose_LUFactSpec_nonzero_pivots`, direct row-dominant existential exact-LU growth wrappers `higham9_13_rowDiagDom_exists_LUFactSpec_growth_bound_3` and `higham9_13_rowDiagDom_exists_LUFactSpec_growthFactorEntry_le_three`, and exact source-data recurrence-to-product builder wrappers are closed. Remaining local gap is executable algorithmic trace coverage and general special-class exact-LU existence packaging not already covered by `LUFactSpec`/recurrence hypotheses. |
| Theorem 9.14, tridiagonal backward error | PROVE-NOW-SPLIT | Yes, direct reliance on available Split-1 `gamma` infrastructure for closed subclaims | `higham9_14_tridiag_diagDom_fu_bound_tight` is closed for the absorbed `gamma(6)` form. The structural wrappers now supply its growth hypothesis from local Theorem 9.13 under explicit bidiagonal-LU/exact-product assumptions, exact source-data recurrence assumptions, ordinary exact `LUFactSpec` certificates, and source-data exact-LU existential packages via `higham9_14_tridiag_diagDom_fu_bound_from_structural_growth`, `higham9_14_tridiag_rowDiagDom_fu_bound_from_structural_growth`, `higham9_14_tridiag_colDiagDom_fu_bound_from_recurrence`, `higham9_14_tridiag_rowDiagDom_fu_bound_from_recurrence`, `higham9_14_tridiag_colDiagDom_fu_bound_from_LUFactSpec`, `higham9_14_tridiag_rowDiagDom_fu_bound_from_LUFactSpec`, `higham9_14_colDiagDom_exists_LUFactSpec_fu_bound`, and `higham9_14_rowDiagDom_exists_LUFactSpec_fu_bound`. The printed source scalars, coefficient aggregation, and certificate-production bridges are closed by `higham9_14_f`, `higham9_14_h`, `higham9_14_h_eq_f_div`, `higham9_14_f_nonneg`, `higham9_14_h_mul_one_sub_eq_f`, `higham9_20_tridiag_lu_perturbation_model_of_LUBackwardError_le`, `higham9_21_tridiag_solve_perturbation_model_of_fl_triangular_solves_gamma_le`, `LUFactSpec.to_LUBackwardError_zero`, `higham9_14_source_f_bound`, `higham9_14_source_h_bound_of_absLUhat_bound`, `higham9_14_source_h_bound_of_absLUhat_mul_one_sub_bound`, `higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models`, `higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le`, `higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma`, `higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le`, `higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves`, `higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_spd`, `higham9_14_nonnegative_lu_source_f_bound_actual_triangular_solves`, `higham9_14_mmatrix_lu_source_f_bound_actual_triangular_solves`, `higham9_14_sign_equiv_source_f_bound_actual_triangular_solves`, `higham9_14_totalNonnegative_exists_source_f_bound_actual_triangular_solves`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_builders`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_LUBackwardError_fl_triangular_solves`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_LUBackwardError_fl_triangular_solves`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence_LUBackwardError_fl_triangular_solves`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence_LUBackwardError_fl_triangular_solves`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence_LUFactSpec_fl_triangular_solves`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence_LUFactSpec_fl_triangular_solves`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_LUFactSpec`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUFactSpec`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves`, `higham9_14_colDiagDom_exists_LUFactSpec_source_f_bound_of_models`, `higham9_14_rowDiagDom_exists_LUFactSpec_source_f_bound_of_models`, `higham9_14_colDiagDom_exists_LUFactSpec_source_f_bound_actual_triangular_solves`, and `higham9_14_rowDiagDom_exists_LUFactSpec_source_f_bound_actual_triangular_solves`; the full rounded tridiagonal backward-error theorem for all classes remains open. |
| Theorem 9.15, LU sensitivity | PROVE-NOW-SPLIT | Yes, direct integrated Split 1 dependency; not an unresolved wait | Componentwise algebraic identity, relative propagation, and the componentwise forward coefficient wrapper are closed; equation (9.27)'s `G = L^{-1} ΔA U^{-1}` Frobenius/operator-2 product and denominator-ratio bridges are closed by `higham9_27_GMatrix_frobenius_le`, `higham9_27_GMatrix_opNorm2Le`, and `higham9_27_GMatrix_ratio_le_product_ratio`; the source `χ(A)` condition-number chain and displayed min form are closed by `higham9_15_chi_condition_chain_of_inverse_product_bounds`, `higham9_15_chi_condition_chain_min_of_inverse_product_bounds`, `higham9_15_chi_condition_chain_of_inverse_products`, and `higham9_15_chi_condition_chain_min_of_inverse_products`; the normalized algebraic identities for the normwise and componentwise routes are closed by `higham9_15_normalized_G_factorization_matrix` and `higham9_15_normalized_Gtilde_factorization_matrix`; the strict-lower/upper split equations are closed by `higham9_15_normalized_G_split_matrix` and `higham9_15_normalized_Gtilde_split_matrix`, their Frobenius projection-bound corollaries are closed by `higham9_15_normalized_G_split_frobNorm_bounds` and `higham9_15_normalized_Gtilde_split_frobNorm_bounds`, the local nonlinear one-step bounds are closed by `higham9_15_normalized_G_split_frobNorm_step_bound` and `higham9_15_normalized_Gtilde_split_frobNorm_step_bound`, and the scalar denominator handoff from a future linearized step is closed by `higham9_15_scalar_bound_of_le_add_mul` and `higham9_15_normalized_G_frobNorm_ratio_bound_of_linear_step`; the auxiliary Frobenius-denominator assembly is closed by `higham9_15_frobenius_relative_assembly_bound`, and the printed operator-denominator assembly is closed by `higham9_15_frobenius_relative_assembly_bound_opNorm`; the componentwise original-variable assembly is closed by `higham9_15_componentwise_original_assembly`; the inverse-normalized assembly wrappers are closed by `higham9_15_frobenius_relative_assembly_of_inverse_normalized_bounds`, `higham9_15_frobenius_relative_assembly_of_inverse_normalized_bounds_opNorm`, `higham9_15_frobenius_relative_assembly_of_inverse_normalized_bounds_opNorm_of_inverse_identities`, and `higham9_15_componentwise_original_assembly_of_inverse_normalized_bounds`; positive printed denominators are derived on nonempty dimensions by `higham9_15_opNorm2_pos_of_rectMatMul_right_inverse` and `higham9_15_opNorm2_pos_of_rectMatMul_left_inverse`; the printed-denominator conditional normwise source endpoints are closed by normalized-bound, split/min-factor, two-sided factorization, and one-sided source-inverse factorization wrappers, with explicit-positivity and Frobenius-denominator variants retained as auxiliary wrappers; the conditional componentwise source endpoints are closed by normalized-majorant, split-majorant, two-sided factorization, and one-sided source-inverse factorization wrappers; the full Barrlund/Sun normwise and spectral-radius theorem still requires the Frobenius Schur-induction and nonnegative spectral-radius majorant source surfaces. |

### Numbered Equations

| Equation | Classification | Previous-split dependency | Reason and Lean status |
| --- | --- | --- | --- |
| (9.1) | CLOSED | No integrated previous-split blocker | Closed for an exact LU certificate by `higham9_1_det_eq_pivot_product` and `higham9_1_det_ne_zero_iff_pivots_ne_zero`; the leading-principal-block determinant consequences are closed by `higham9_1_leadingPrincipalBlock_det_eq_pivot_product` and `higham9_1_leadingPrincipalBlock_det_ne_zero_iff_pivots_ne_zero`; Higham's proper-leading-block existence/uniqueness iff is closed by `higham9_1_lu_exists_unique_iff_properLeadingPrincipalBlock_det_ne_zero`. |
| (9.2a), (9.2b) | PROVE-NOW-SPLIT | No integrated previous-split blocker | The row-permuted `PA` model, row-column-permuted `PAQ` model, explicit `PA = LU` adapter, explicit `PAQ = LU` adapter, and corresponding pivoted backward-error adapters are closed by the `higham9_2_*Permuted*` and `higham9_3_*permuted*` declarations; constructing those certificates from pivoting traces remains open Split-2 work. |
| (9.3), (9.4) | CLOSED | No integrated previous-split blocker | Closed for the rectangular exact Doolittle update identities by `higham9_2_rectDoolittleU_source_identity` and `higham9_2_rectDoolittleL_source_identity`; the square exact-LU converse recurrences are closed by `higham9_2_rectDoolittleUUpdate_eq_of_LUFactSpec` and `higham9_2_rectDoolittleLUpdate_eq_of_LUFactSpec`; the enclosing Algorithm 9.2 executable-loop row remains open. |
| (9.5) | CLOSED | No integrated previous-split blocker | Closed by `higham9_5_rectGEReducedEntry_succ_of_lt`, `higham9_5_rectGEReducedEntry_eq_DoolittleUUpdate`, `higham9_5_rectGEReducedEntry_eq_DoolittleLUpdate_mul_pivot`, `higham9_5_rectPrefixRange_full_eq_matMul`, and `higham9_5_rectGEReducedEntry_full_eq_zero_of_LUFactSpec`. |
| (9.6) | CLOSED | Yes, direct reliance on available Split-1 `gamma` infrastructure | Closed in certificate form by `higham9_3_doolittle_backward_error` and `higham9_3_lu_backward_error_gamma`. |
| (9.7) | CLOSED | Yes, direct reliance on available Split-1 `gamma` infrastructure | Closed by `higham9_4_lu_solve_backward_error`. |
| (9.8) | CLOSED | No integrated previous-split blocker | Closed by `higham9_8_nonneg_factor_bound`. |
| (9.9) | CLOSED | Yes, direct reliance on available Split-1 `gamma` infrastructure | Closed by `higham9_9_nonneg_lu_solve_backward_error`. |
| (9.10) | PROVE-NOW-SPLIT for computed GEPP certificate connection; CLOSED for exact trace-growth-family and explicit pivoted/complete-pivoted certificate surfaces | Yes, direct reliance on available Split-1 `gamma` infrastructure for the closed normwise bound | `higham9_5_wilkinson_source_bound_of_growth_bridge`, `higham9_5_wilkinson_source_bound_of_entry_growth`, `higham9_5_wilkinson_source_bound_of_PartialPivotGEPPUTrace`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_denseLoop`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_absBudget`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_LUFactSpec`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_denseLoop`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_absBudget`, and `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_LUFactSpec` are closed; the explicit trace wrappers derive the source-shaped `2^(n-1)` factor from the partial- and complete-pivoting trace growth theorems, and the dense-loop/exact-certificate variants consume Algorithm 9.2-style certificates on `PA`/`PAQ`. The trace-level value set, boundedness, nonemptiness, supremum adapter, and supremum upper-bound form are closed by `higham9_partialPivotingUTraceGrowthValues`, `higham9_partialPivotingUTraceGrowthSup`, `higham9_partialPivotingUTraceGrowthValues_bddAbove`, `higham9_partialPivotingUTraceGrowth_le_sup`, `higham9_partialPivotingUTraceGrowthValues_nonempty`, and `higham9_7_partialPivotingUTraceGrowthSup_le_pow_two`. The remaining equation-level gap is constructing the computed pivot traces and dense-loop/backward-error certificates from a concrete executable GEPP/GEPQ loop. |
| (9.11) | CLOSED | No integrated previous-split blocker | The max-entry witness bridge, unpermuted exact-LU final-pivot identity, explicit `P A Q = L U` complete-permuted inverse-entry instantiation, cumulative real complete-pivoting `PAQ = LU` certificate existence, and real complete-pivoting existential `theta <= rho` bridge are closed by `higham9_8_growth_factor_ge_theta_real`, `higham9_8_finalPivot_mul_inverse_entry_eq_one`, `higham9_8_finalPivot_inverse_entry_abs_inv_le_maxEntryNorm`, `higham9_8_growth_factor_ge_theta_of_lu_right_inverse`, `higham9_2_rowColPermutedMatrix_right_inverse`, `higham9_8_finalPivot_mul_inverse_entry_eq_one_of_completePermutedLUFactSpec`, `higham9_8_finalPivot_inverse_entry_abs_inv_le_maxEntryNorm_of_completePermutedLUFactSpec`, `higham9_8_growth_factor_ge_theta_of_completePermutedLUFactSpec_right_inverse`, `higham9_8_exists_CompletePermutedLUFactSpec_of_det_ne_zero`, and `higham9_8_exists_completePivoting_growth_factor_ge_theta_real`. |
| (9.12) | CLOSED | No integrated previous-split blocker | The source sine matrix definition, symmetry, entrywise/max-entry scale bounds, positive `(0,0)` entry, positive max-entry norm, finite cosine-sum parity package, unscaled discrete sine orthogonality, scaled self-inverse formula, conditional/candidate theta lower-bound arithmetic, and block-doubled sine theta bridge are closed by `higham9_12_sineMatrix`, `higham9_12_sineMatrix_symm`, `higham9_12_sineMatrix_entry_abs_le_scale`, `higham9_12_sineMatrix_maxEntryNorm_le_scale`, `higham9_12_sineMatrix_zero_zero_pos`, `higham9_12_sineMatrix_maxEntryNorm_pos`, `higham9_12_cos_sum_even`, `higham9_12_cos_sum_odd`, `higham9_12_cos_sum_pos_lt_two_mul`, `higham9_12_cos_sum_eq_of_mod_two_eq`, `higham9_12_sine_product_sum`, `higham9_12_sineMatrix_mul_self`, `higham9_12_sineMatrix_inverse_formula`, `higham9_12_theta_ge_half_succ_of_maxEntryNorm_le_scale`, `higham9_12_two_theta_ge_succ_of_maxEntryNorm_le_scale`, `higham9_12_sineMatrix_theta_candidate_ge_half_succ`, `higham9_12_sineMatrix_two_theta_candidate_ge_succ`, and `higham9_11_sine_block_theta_candidate_ge_succ`; the trace-level complete-pivoting `g(2n)` lower-bound consequence is closed separately by `higham9_11_completePivotingUTraceGrowthSup_ge_succ`. |
| (9.13) | CLOSED for the complex Fourier/Vandermonde certificate-level and trace-level growth theorems | No integrated previous-split blocker | The source complex Fourier/Vandermonde matrix definition, symmetry, first row/column identities, unit-circle entry norm, roots-of-unity cancellation, full row/column Gram identities, entrywise inverse formula `V_n^{-1} = n^{-1} V_nᴴ`, general complex max-entry `theta <= n`, max-entry `theta(V_n)=n` witness, complex growth factor, complex `rho >= theta` bridge, conditional `rho(V_n) >= n` bridge, complex `PAQ = LU` certificate surface, permutation transport of the visible right inverse, explicit complex final-pivot inverse-entry instantiation, full complex recursive trace construction, full complex cumulative certificate construction, complex trace-to-certificate max-entry transfer, Fourier/Vandermonde certificate-level existence theorem, and Fourier/Vandermonde trace-level growth existence theorem are closed by the `higham9_13_fourierVandermonde*`, `higham9_13_fourierRoot*`, scaled-adjoint inverse, complex max-entry, complex growth, complex certificate, complex trace, and complex construction families plus `higham9_8_theta_le_card_complex`, `higham9_8_ComplexCompletePivotGECPUTrace_exists_ComplexCompletePermutedLUFactSpec_complexMaxEntryNorm_le`, `higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card_of_ComplexCompletePivotGECPUTrace`, and `higham9_13_exists_fourierVandermonde_ComplexCompletePivotGECPUTrace_growth_ge_card`. |
| (9.14) | PROVE-NOW-SPLIT | No integrated previous-split blocker | The displayed Wilkinson scalar product/RHS and scalar nonnegativity/positivity are closed by `higham9_14_completePivotWilkinsonProduct`, `higham9_14_completePivotWilkinsonBound`, `higham9_14_completePivotWilkinsonProduct_nonneg`, `higham9_14_completePivotWilkinsonProduct_pos`, `higham9_14_completePivotWilkinsonBound_nonneg`, and `higham9_14_completePivotWilkinsonBound_pos`; recursive complete-pivoting `U` trace existence/upper-triangularity, the cumulative real `PAQ = LU` certificate existence, elementary trace-level `rho <= 2^(n-1)` boundedness, and the Problem 9.11 trace-level `g(2n)` lower-bound bridge are closed. The actual sharp Wilkinson complete-pivoting product upper-bound theorem remains open Split-2 work. |
| (9.15) | CLOSED | No integrated previous-split blocker | The trace-level complete-pivoting value set, boundedness, supremum adapter, sine-block trace witness, and source-shaped lower bound `n + 1 <= g(2n)` are closed by `higham9_completePivotingUTraceGrowthValues`, `higham9_completePivotingUTraceGrowthSup`, `higham9_completePivotingUTraceGrowthValues_bddAbove`, `higham9_completePivotingUTraceGrowth_le_sup`, `higham9_8_CompletePivotGECPUTrace_exists_CompletePermutedLUFactSpec_maxEntryNorm_le`, `higham9_8_CompletePivotGECPUTrace_growth_factor_ge_theta_real`, `higham9_11_exists_completePivotingUTrace_sine_block_growth_ge_succ`, `higham9_11_completePivotingUTraceGrowthValues_exists_ge_succ`, and `higham9_11_completePivotingUTraceGrowthSup_ge_succ`. The sharper Wilkinson product-bound family remains a separate equation (9.14) row. |
| (9.16) | PROVE-NOW-SPLIT | No integrated previous-split blocker | Foster's displayed rook-pivoting scalar RHS and scalar nonnegativity/positivity are closed by `higham9_16_rookPivotFosterBound`, `higham9_16_rookPivotFosterBound_nonneg`, and `higham9_16_rookPivotFosterBound_pos`; recursive rook-pivoting `U` trace existence, upper-triangularity, first-Schur-complement doubling, elementary cumulative trace bound `rho <= 2^(n-1)`, nonsingular source-facing existential growth package, trace-level value-set/supremum endpoint, and exact trace-to-solve Wilkinson perturbation wrapper are closed by `higham9_16_RookPivotGEUTrace`, `higham9_16_RookPivotGEUTrace_upper_zero`, `higham9_16_rookPivot_firstSchurComplement_entry_abs_le_two`, `higham9_16_rookPivot_firstSchurComplement_maxEntryNorm_le_two`, `higham9_16_RookPivotGEUTrace_entry_abs_le_pow_two`, `higham9_16_RookPivotGEUTrace_growthFactorEntry_le_pow_two`, `higham9_16_exists_RookPivotGEUTrace_of_det_ne_zero`, `higham9_16_exists_RookPivotGEUTrace_upper_zero_of_det_ne_zero`, `higham9_16_exists_RookPivotGEUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero`, `higham9_16_rookPivotingUTraceGrowthValues`, `higham9_16_rookPivotingUTraceGrowthSup`, `higham9_16_rookPivotingUTraceGrowthValues_le_pow_two`, `higham9_16_rookPivotingUTraceGrowthValues_bddAbove`, `higham9_16_rookPivotingUTraceGrowth_le_sup`, `higham9_16_rookPivotingUTraceGrowthValues_nonempty`, `higham9_16_rookPivotingUTraceGrowthSup_le_pow_two`, `higham9_16_RookPivotGEUTrace_exists_CompletePermutedLUFactSpec_L_bound_maxEntryNorm_le`, and `higham9_16_wilkinson_source_bound_exists_of_RookPivotGEUTrace`; Foster's sharper rook-pivoting growth upper-bound theorem remains open. |
| (9.17) | CLOSED | Yes, indirect integrated Split 1 dependency reused through Chapter 8 Lemma 8.8 | Closed by the source-faithful norm predicate `higham9_17_rowDiagDom_absLU_bound`, the exact-LU-to-`condSkeel` bridge `higham9_17_absLU_infNorm_le_condSkeel_of_LUFactSpec`, and the row-diagonal-dominance wrapper `higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec`, which combine exact LU algebra with `higham8_8_rowDiagDominantUpper_condSkeel_bound` to prove `|| |L||U| ||_inf <= (2n - 1) ||A||_inf`. |
| (9.18) | CLOSED | No integrated previous-split blocker | Closed by `higham9_18_TridiagData`, `higham9_18_tridiag_to_matrix`, and structural predicate bridge `higham9_18_tridiag_to_matrix_isTridiagonal`. |
| (9.19) | CLOSED | No integrated previous-split blocker | Closed by `higham9_19_tridiag_lu` for the displayed recurrence surface, by `higham9_19_TridiagExactLURecurrence` for the exact-arithmetic recurrence predicate, by `higham9_19_tridiag_exact_product_of_recurrence` for the local algebraic product consequence, and by `higham9_19_tridiag_LUFactSpec_of_exact_product`/`higham9_19_tridiag_LUFactSpec_of_recurrence` for the ordinary exact-LU certificate handoff. |
| (9.20) | CLOSED for source model surface and coefficient-dominated `LUBackwardError` production; PROVE-NOW-SPLIT for every sharper rounded tridiagonal class | Yes, direct reliance on available Split-1 `gamma` infrastructure for existing subclaims | The printed perturbation model `Lhat Uhat = A + DeltaA_LU`, `|DeltaA_LU| <= u |Lhat||Uhat|` is recorded as `higham9_20_tridiag_lu_perturbation_model`, and `higham9_20_tridiag_lu_perturbation_model_of_LUBackwardError_le` produces it from any existing `LUBackwardError` certificate whose coefficient is bounded by `u`. Proving the sharper source-class/executable rounded tridiagonal recurrence model for every printed class remains open. |
| (9.21) | CLOSED for source model surface and coefficient-dominated actual triangular solves; PROVE-NOW-SPLIT for every sharper rounded triangular-solve path | Yes, direct reliance on available Split-1 `gamma` infrastructure for existing subclaims | The printed triangular-solve perturbation model with `|DeltaL| <= u|Lhat|` and `|DeltaU| <= (2u+u^2)|Uhat|` is recorded as `higham9_21_tridiag_solve_perturbation_model`, and `higham9_21_tridiag_solve_perturbation_model_of_fl_triangular_solves_gamma_le` produces it for the actual `fl_forwardSub`/`fl_backSub` pair when `gamma fp n <= u`. Proving every sharper source rounded solve path supplies the printed coefficients remains open. |
| (9.22) | CLOSED for source aggregation, coefficient-dominated certificate-production wrappers, and selected optimal-/constant-growth final scalar wrappers; PROVE-NOW-SPLIT for full all-class tridiagonal backward-error theorem | Yes, direct reliance on available Split-1 `gamma` infrastructure for existing subclaims | Absorbed `gamma(6)` form exists. The printed scalar `f(u) = 4u + 3u^2 + u^3`, the `h(u)=f(u)/(1-u)` bridge, the algebraic aggregation from `(9.20)`/`(9.21)` coefficients to `f(u)`, the model-consuming wrapper `higham9_22_source_f_bound_of_9_20_9_21_models`, the constant-growth wrapper `higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models`, the certificate-produced constant-growth wrappers `higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le` and `higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma`, and the divided/source-shaped conditional `h(u)` bounds including model-consuming variants are closed. The SPD positive-`D L^T`, nonnegative-LU, M-matrix LU, sign-equivalent, and total-nonnegative/nonsingular optimal-growth surfaces now feed the final `h(u)|A|` bound once the source perturbation models are supplied, and the builder/recurrence, ordinary exact-LU, and source-data exact-LU column/direct-row diagonally-dominant packages feed the `3 f(u)|A|` bound once those same models are supplied; producing the sharper models for all rounded tridiagonal classes remains open. |
| (9.23) | CLOSED | Yes, direct integrated Split 1 dependency reused through Chapter 7 and the repository `FirstOrderLe` vocabulary | Closed by `higham9_23_condSkeel_nonneg`, `higham9_23_forward_error_exact_condSkeel`, `higham9_23_firstOrderLe_of_backward_error_coeff`, and `higham9_23_forward_error_firstOrder_cond_product`: an unperturbed-right-hand-side row-wise backward-error coefficient `eta` gives the exact denominator forward-error bound, and `eta <= 3 n u cond(U)` gives the printed `3 n u cond(A) cond(U) + O(u^2)` source shape. |
| (9.24) | CLOSED | No integrated previous-split blocker | Closed by `higham9_24_scaledMatrix`, `higham9_24_scaledRhs`, `higham9_24_scaledUnknown`, and `higham9_24_scaled_system_equiv`. |
| (9.25) | CLOSED | No integrated previous-split blocker | Formalized as `higham9_25_trailingRowInf` and `higham9_25_implicitRowScalingPivotRule`. |
| (9.26) | CLOSED | Yes, direct reuse of integrated Split 1 Holder/norm infrastructure | Closed by `higham9_26_prefixLpNorm`, `higham9_26_holder_prefix_dot_abs_le`, `higham9_26_stage_entry_abs_le`, and `higham9_26_stage_entry_abs_le_of_uniform_bounds`; the source Holder prefix dot-product bound and explicit uniform-budget form are compiled. |
| (9.27) | PROVE-NOW-SPLIT for the full Barrlund/Sun source theorem; CLOSED for the `G` norm-product and denominator-ratio support | Yes, direct integrated Split 1 dependency; not an unresolved wait | `higham9_27_GMatrix`, `higham9_27_GMatrix_frobenius_le`, `higham9_27_GMatrix_opNorm2Le`, `higham9_15_ratio_le_of_norm_bounds`, and `higham9_27_GMatrix_ratio_le_product_ratio` close the Frobenius/operator-2 product bridges and source denominator ratio for `G = L^{-1} ΔA U^{-1}`. The full normwise/spectral statement still needs the nonlinear perturbation and spectral-radius source wrapper. |

### Problems and Appendix Solutions

The split problem ledger lists Problems 9.1--9.11 and 9.13--9.18. Appendix A
solutions for this chapter were inspected, including source solution 9.5 even
though the split contract's Appendix ledger omits it.

| Problem | Classification | Previous-split dependency | Reason and Lean status |
| --- | --- | --- | --- |
| 9.1 | CLOSED | No integrated previous-split blocker | The full-matrix and leading-principal-block determinant-pivot consequences are closed from exact `LUFactSpec` certificates, source-strength proper Schur-complement leading-minor inheritance is closed, exact LU existence and uniqueness from proper nonzero leading principal determinants are closed by `higham9_1_lu_exists_and_unique_of_properLeadingPrincipalBlock_det_ne_zero`, and the singular unique-LU converse is closed by `higham9_1_lu_nonunique_of_zero_proper_pivot` and `higham_problem9_1_properLeadingPrincipalBlock_det_ne_zero_of_unique_lu`. |
| 9.2 | CLOSED | No integrated previous-split blocker | Appendix finite-union count, characteristic-polynomial danger-set bridge, source leading-principal-block union, "outside danger union gives nonzero shifted determinant" adapter, and the final finite-exception shifted-matrix LU theorem are closed by `higham9_2_danger_shift_count_bound`, `higham9_2_charpoly_danger_shift_count_bound`, `higham9_2_leadingBlockDangerSet_count_bound`, `higham9_2_shiftedLeadingBlock_det_ne_zero_of_not_mem_danger_union`, `higham9_2_shiftedMatrix_properLeadingPrincipalBlock_det_ne_zero_of_not_mem_danger`, `higham9_2_shiftedMatrix_lu_exists_unique_of_not_mem_danger`, and `higham_problem9_2_shiftedMatrix_lu_exists_unique_except_card_bound`; the final theorem reuses the closed Theorem 9.1 source-strength proper-leading-principal LU criterion and introduces no Split 1 dependency. |
| 9.3 | CLOSED | Yes, direct reuse of integrated complex quadratic-form/norm infrastructure | Closed by `higham_problem9_3_zeroNotInFieldOfValues`, `higham_problem9_3_properLeadingPrincipalBlock_det_ne_zero_of_zeroNotInFieldOfValues`, and `higham_problem9_3_lu_exists_unique_of_zeroNotInFieldOfValues`: zero exclusion from the field of values rules out singular proper leading principal blocks, then the closed Theorem 9.1 source iff gives unique exact no-pivot LU. |
| 9.4 | CLOSED | Yes, direct reliance on available Split-1 `gamma`/triangular-solve infrastructure for the Theorem 9.4 analogue | Row- and complete-pivoted permutation analogues of Theorems 9.3 and 9.4 are closed by the `higham9_3_*permuted*` certificate adapters and `higham_problem9_4_permuted_lu_solve_backward_error` / `higham_problem9_4_complete_permuted_lu_solve_backward_error`. |
| 9.5 | CLOSED | No integrated previous-split blocker | Closed by the new exact 2 by 2 witness and no-componentwise-bound theorem. |
| 9.6 | CLOSED | No integrated previous-split blocker | Source total-nonnegative support, inherited-submatrix closure, the all-square-minors to order-two adapter, the `2 by 2` minor determinant formula, local and arbitrary-size denominator-cleared Schur determinant identities, selected `3 by 3` minor nonnegativity, first Schur-update `2 by 2` minor preservation, the basic determinantal inequality, entrywise nonnegativity projection, nonnegative first multiplier, first Schur-update nonnegativity, first Schur-update no-growth bound, first-step all-minors total-nonnegativity preservation on strictly trailing square submatrices, trailing nonnegativity/absolute-entry/max-entry no-growth, principal-block determinant nonnegativity, full determinant nonnegativity, the singular `det A = 0` branch, the `p = 0`/`p = n` boundary cases, and the `2 by 2`, `p = 1` base case plus both `3 by 3` interior cases (`p = 1` and `p = 2`) of the principal-block determinant inequality, `det A ≠ 0` to `det A > 0`, first-pivot positivity, all-leading-principal-minor positivity from total nonnegativity plus `det A != 0`, recursive exact nonnegative LU construction from source nonsingularity, final max-entry `rho <= 1`, and reduced-matrix no-pivot growth-factor `rho_n <= 1` endpoints are closed by the `higham9_6_*` family including `higham9_6_principalBlock_determinantal_inequality_of_det_eq_zero`, `higham9_6_principalBlock_determinantal_inequality_zero`, `higham9_6_principalBlock_determinantal_inequality_full`, `higham9_6_principalBlock_determinantal_inequality_fin_two`, `higham9_6_leadingPrincipalBlock_det_pos_of_totalNonnegative_det_ne_zero`, `higham9_6_lu_exists_nonnegative_of_totalNonnegative_det_ne_zero`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero`, `higham_problem9_9_noPivotReducedGrowthFactor_le_one_of_nonnegative_LU`, and `higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_det_ne_zero`; the arbitrary-p Koteljanskii/Fischer determinant comparison is closed by `higham9_6_principalBlock_determinantal_inequality_of_totalNonnegative`. |
| 9.7 | CLOSED | No integrated previous-split blocker | Closed by with-empty and nonempty binomial count theorems. |
| 9.8 | CLOSED | No integrated previous-split blocker | Checkerboard sign matrix `J`, alternating signs, sign conjugation, diagonal/off-diagonal facts, absolute-value preservation, checkerboard identity preservation, left/right/two-sided inverse transport, the cofactor-level entrywise checkerboard sign pattern for `nonsingInv`, empty-, `1 by 1`, codimension-one, full-determinant, and full-order minor nonnegativity wrappers, selected/complement permutation-sign support, the nonsingular-complement arbitrary selected-minor consequence, the no-complement-nonsingularity block identity `higham9_8_det_inv_topLeft_fromBlocks_mul_det_eq_det_D`, the selected-minor identity `higham9_8_det_inv_selected_mul_det_reindexed_eq_det_complement`, the full arbitrary selected-minor theorem `higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg`, `J`-conjugation involution and product algebra, induced LU certificate, the source algebraic conclusion `|JLJ||JUJ| = |A|` under explicit nonnegative LU factors, and the total-nonnegative-checkerboard route from `J A J` to those factors are closed by the `higham9_8_*` support family. |
| 9.9 | CLOSED | No integrated previous-split blocker | Closed by `higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_absLU_infNorm_div`, which defines source `rho_n` as the max-entry growth over equation (9.5) exact no-pivot reduced matrices, together with the final-`U` specialization `higham_problem9_9_growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div`. |
| 9.10 | CLOSED | No integrated previous-split blocker | Closed by `higham_problem9_10_rankOne_blunder_solution`, `higham_problem9_10_rankOne_blunder_error`, and `higham_problem9_10_multiplier_blunder_error`; the prior later-chapter deferral was removed because the source Sherman-Morrison update follows directly from the visible left-inverse equation and rank-one matrix-vector algebra. |
| 9.11 | CLOSED | No integrated previous-split blocker | Block inverse formula, the identities `alpha(B)=alpha(A)`, `beta(B)=beta(A)/2`, `theta(B)=2 theta(A)`, the block-doubled sine theta lower bound, the visible-witness, flattened sine-block, and flattened max-entry bridges, the bounded-family supremum step from a witness to `g(2n)`, including the ordinary max-entry-norm flattened form, the source sine-matrix definition/symmetry/scale/positivity support, finite-sum orthogonality, self-inverse certificate, theta lower-bound arithmetic, the concrete cumulative complete-pivoting sine-block certificate with growth at least `n + 1`, trace-level complete-pivoting growth-value boundedness, the trace-to-certificate max-entry bridge, and the source-shaped trace-level lower bound `n + 1 <= g(2n)` are closed by `higham9_11_*`, `higham9_completePivotGrowth*`, `higham9_completePivotingUTraceGrowth*`, `higham9_8_CompletePivotGECPUTrace_exists_CompletePermutedLUFactSpec_maxEntryNorm_le`, `higham9_8_CompletePivotGECPUTrace_growth_factor_ge_theta_real`, `higham9_12_sineMatrix*`, `higham9_12_sine_product_sum`, `higham9_12_sineMatrix_inverse_formula`, and the `higham9_12_*theta*` lemmas. |
| 9.13 | CLOSED | No integrated previous-split blocker | Closed by `higham9_13_threshold_update_abs_bound`, `higham9_13_column_growth_by_modification_count`, and `higham9_13_growthFactorEntry_bound_from_column_modifications`, which formalize the appendix modification-count proof and max-entry growth-factor consequence. |
| 9.14 | CLOSED | No integrated previous-split blocker | Full selected exact-arithmetic Problem 9.14 scope is closed. Branch (a), the first §9.9 method on the original pre-pivoted matrix `A`, is closed by `higham_problem9_14_RecursiveFirstMethodTrace_of_PrePivotedGEPP`, `higham_problem9_14_exists_RecursiveFirstMethodLUFactSpec_of_PrePivotedGEPP`, and `higham_problem9_14_RecursiveFirstMethodLUFactSpec_same_as_PrePivotedGEPP`. Branch (b), pairwise pivoting with natural multiplier-bounded pivoting on `ΠA`, is closed by `higham_problem9_14_RecursivePairwiseBubbleTrace_of_PrePivotedGEPP`, `higham_problem9_14_exists_RecursivePairwiseLUFactSpec_of_PrePivotedGEPP`, and `higham_problem9_14_RecursivePairwiseLUFactSpec_same_as_PrePivotedGEPP`. The shared GEPP/no-interchange exact LU side is closed by `higham_problem9_14_PrePivotedGEPP_exists_unique_LUFactSpec` and `higham_problem9_14_PrePivotedGEPP_lu_unique`; exact-LU uniqueness provides the same `L,U` bridge. |
| 9.15 | SKIP | No integrated previous-split blocker | Research problem asking for sharp unknown bounds; not a determinate theorem in the source. |
| 9.16 | SKIP | No integrated previous-split blocker | Research/qualitative empirical claim "almost always small in practice"; no precise theorem. |
| 9.17 | SKIP | No integrated previous-split blocker | Research problem about an unknown limit and Hadamard equality; not a proved source theorem. |
| 9.18 | SKIP | No integrated previous-split blocker | Research/search problem with empirical lower-bound table; exact general theorem is not supplied. |

### Other Precise Prose, Definitions, and Exclusions

| Source item | Classification | Previous-split dependency | Reason and Lean status |
| --- | --- | --- | --- |
| Growth factor definitions for no pivoting and GEPP | CLOSED | No integrated previous-split blocker | Real max-entry `growthFactorEntry` and normwise `growthFactor` exist. The source growth-family layer now includes the no-pivot exact-LU value set/supremum/nonempty witness (`higham9_noPivotingLUFactSpecGrowthValues`, `higham9_noPivotingLUFactSpecGrowthSup`, `higham9_noPivotingLUFactSpecGrowthValues_nonempty`), the shared no-pivot/partial/complete/rook index (`higham9_PivotingGrowthKind`, `higham9_pivotingGrowthValues`, `higham9_pivotingGrowthSup`), and the trace-only partial/complete/rook index with uniform elementary `2^(n-1)` value/supremum bounds (`higham9_TracePivotingGrowthKind`, `higham9_tracePivotingGrowthValues`, `higham9_tracePivotingGrowthValues_le_pow_two`, `higham9_tracePivotingGrowthSup_le_pow_two`). |
| Partial, complete, and rook first-stage pivoting definitions and immediate multiplier bounds | CLOSED | No integrated previous-split blocker | `higham9_1_partialPivotChoice`, `higham9_1_completePivotChoice`, `higham9_1_rookPivotChoice`, the complete-pivoting active-entry ratio lemma, and the column/row multiplier lemmas are closed. |
| Partial, complete, and rook recursive growth equations | PROVE-NOW-SPLIT | No integrated previous-split blocker | The recursive partial-, complete-, and rook-pivoting `U` trace existence/upper-triangularity layers are closed, the real partial-pivoting cumulative `PA = LU` and complete-pivoting cumulative `PAQ = LU` certificate layers are closed, the elementary partial-, complete-, and rook-pivoting trace growth bounds `rho <= 2^(n-1)` are closed, the complete- and rook-trace value families have nonempty positive-dimensional supremum endpoints, the exact partial-/complete-/rook-trace-to-solve Wilkinson wrappers are closed at elementary growth strength, and the trace-level Problem 9.11 `g(2n)` lower-bound surface is closed. Equation (9.14) still requires the sharp Wilkinson product upper-bound proof, and equation (9.16) still requires Foster's sharper rook-pivoting product-bound proof. |
| Diagonal dominance, upper Hessenberg, and tridiagonal orientation predicates | CLOSED | No integrated previous-split blocker | `IsDiagDominant`, `IsRowDiagDominant`, and `IsUpperHessenberg` exist; `higham9_9_colDiagDominant_transpose_iff_rowDiagDominant`, `higham9_9_rowDiagDominant_transpose_iff_colDiagDominant`, and `higham9_13_tridiagonal_transpose_iff` close the real-transpose row/column/tridiagonal orientation adapters; `higham9_9_rowDiagDominant_offdiag_abs_le_diag`, `higham9_9_colDiagDominant_offdiag_abs_le_diag`, and the four entry-ratio lemmas close the immediate diagonal-dominance off-diagonal/first-ratio support facts. |
| Tridiagonal matrix data and LU recurrence definitions | CLOSED | No integrated previous-split blocker | `higham9_18_TridiagData`, `higham9_18_tridiag_to_matrix`, `higham9_19_tridiag_lu`. |
| Scaling equivalence for linear systems | CLOSED | No integrated previous-split blocker | `higham9_24_scaled_system_equiv`. |
| Rank-revealing LU section 9.12 prose | DEFER-LATER-SPLIT | Yes, later deferred block also has Split-1 norm/SVD gates | Not in the Chapter 9 primary/equation/problem contract as a selected Split-2 theorem; destination is the later rank-revealing/SVD factorization work. |
| Historical perspective, notes, LAPACK routine list | SKIP | No integrated previous-split blocker | Editorial, bibliographic, or software-descriptive material. |
| Figures, tables, and printed empirical growth-factor observations | SKIP | No integrated previous-split blocker | Empirical or historical outputs without a fully specified computation. |

## Previous-Split Dependency Ledger

| Open item | Dependency kind | Previous split | Contract family or missing result | Why not local |
| --- | --- | --- | --- | --- |
| Theorem 9.15 full normwise/spectral sensitivity and equation (9.27) | Direct | Split 1 | Chapter 6 norm, Frobenius/operator norm, and spectral-radius infrastructure | Chapter 6 owns the shared norm and spectral foundations; duplicating them in Chapter 9 would create a parallel API. The local `G` Frobenius/operator-2 product bridge, `χ(A)` condition-number chain, normalized algebraic identities, normalized split equations, inverse-normalization bridges, auxiliary Frobenius-denominator assembly, source-correct operator-denominator assembly with inverse-derived denominator positivity, componentwise original-variable assembly, and conditional normwise/componentwise source wrappers are now closed locally; the remaining gap is the full Schur-induction/spectral-radius theorem surface. |
| Rank-revealing LU prose in section 9.12 | Indirect | Split 1 | Norm/SVD/rank foundations that later rank-revealing work should own or import | The section is not a Split-2 primary theorem; proving it locally would mix ownership. |

Available previous-split results used by closed rows are not blockers. In
particular, the Chapter 3 `gamma`/roundoff infrastructure is already present in
the repository and is used by several closed Chapter 9 wrappers.

## Formalized End-To-End Without Unresolved Previous-Split Blocking

| Source label/name | Lean declaration(s) | File path | Newly proved or reused | Genuine proof confirmation |
| --- | --- | --- | --- | --- |
| Problem 9.6 leading-principal first-Schur determinant identity | `higham9_6_pivot_mul_firstSchur_leadingPrincipalBlock_det_eq` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Specializes the arbitrary-size denominator-cleared first-pivot Schur determinant identity to leading principal blocks by explicit `Fin` reindexing; it is local proof infrastructure and does not assume the Koteljanskii/Fischer determinant comparison. |
| Problem 9.6 block Desnanot/Sylvester Schur determinant core, source reindexing adapters, and adjacent source-indexed inequality bridge | `higham9_6_desnanot_schur_core`, `higham9_6_desnanot_schur_core_inequality`, `higham9_6_desnanot_schur_core_inequality_of_offdiag_product_nonneg`, `higham9_6_det_middleEndpoints_fromBlocks_eq_source`, `higham9_6_det_middleEndpoint0_fromBlocks_eq_leadingPrincipalBlock`, `higham9_6_det_middleEndpoint1_fromBlocks_eq_trailingPrincipalBlock`, `higham9_6_adjacent_desnanot_inequality_of_offdiag_product_nonneg` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Derives the adjacent bordered-minor condensation identity from Mathlib's Schur-complement determinant formula and a `2 by 2` determinant expansion, proves the immediate inequality when either the two off-diagonal bordered determinants or their product are nonnegative, reindexes the reordered block determinants back to the source full/leading/trailing principal blocks, and proves the adjacent source-indexed inequality under the explicit off-diagonal product condition. These are pure algebraic infrastructure and do not assume the full source-indexed determinant inequality. |
| Section 9.1 first-stage pivot choices and multiplier bounds | `higham9_1_partialPivotChoice`, `higham9_1_completePivotChoice`, `higham9_1_rookPivotChoice`, `higham9_1_partialPivot_multiplier_abs_le_one`, `higham9_1_completePivot_column_multiplier_abs_le_one`, `higham9_1_completePivot_active_entry_ratio_abs_le_one`, `higham9_1_rookPivot_column_multiplier_abs_le_one`, `higham9_1_rookPivot_row_multiplier_abs_le_one` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in the Split 2 unifying pass and this continuation | Predicates encode source pivot choices; multiplier and active-entry ratio lemmas divide by a nonzero selected pivot and use the corresponding maximality property directly. |
| Section 9.1 finite active-set pivot-choice existence | `higham9_1_exists_partialPivotChoice`, `higham9_1_exists_completePivotChoice`, `higham9_1_rookPivotChoice_of_completePivotChoice`, `higham9_1_exists_rookPivotChoice` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Uses `Finset.exists_max_image` on the active finite column or active finite submatrix; a complete-pivot maximum supplies the row and column maximality required for the rook-pivot predicate. |
| Section 9.1 selected pivot nonzero support | `higham9_1_partialPivotChoice_pivot_ne_zero_of_exists`, `higham9_1_completePivotChoice_pivot_ne_zero_of_exists`, `higham9_1_exists_partialPivotChoice_pivot_ne_zero`, `higham9_1_exists_completePivotChoice_pivot_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Uses maximality plus `abs_eq_zero`: if the selected maximum were zero, every active candidate would have zero absolute value, contradicting an explicitly supplied nonzero active entry. |
| Section 9.1 first-stage nonzero pivot and ratio-bound packages | `higham9_1_exists_partialPivot_nonzero_and_multiplier_bound`, `higham9_1_exists_completePivot_nonzero_and_ratio_bounds`, `higham9_1_exists_rookPivot_nonzero_and_ratio_bounds` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Packages the finite-max existence, nonzero selected-pivot support, and partial/complete/rook ratio-bound lemmas into source-facing one-stage consequences under explicit active nonzero hypotheses. |
| Algorithm 9.2 dense square executable-loop handoff and Theorem 9.3 backward-error bridge | `higham9_2_DoolittleDenseLoopCertificate`, `higham9_2_DoolittleDenseLoopAbsBudgetCertificate`, `higham9_2_denseLoopCertificate_to_DoolittleLU`, `higham9_2_absBudgetCertificate_to_DoolittleLU`, `higham9_2_absBudgetCertificate_of_literal_doolittle_source_budgets`, `higham9_2_absBudgetCertificate_of_literal_doolittle_component_dominance`, `higham9_2_absBudgetCertificate_of_literal_doolittle_exact_product_margins`, `higham9_2_absBudgetCertificate_of_literal_doolittle_exact_product_numerator_margins`, `higham9_2_absBudgetCertificate_of_literal_doolittle_exact_target_gaps`, `higham9_2_permutedDenseLoopCertificate_to_PermutedLUBackwardError`, `higham9_2_permutedAbsBudgetCertificate_to_PermutedLUBackwardError`, `higham9_2_completePermutedDenseLoopCertificate_to_CompletePermutedLUBackwardError`, `higham9_2_completePermutedAbsBudgetCertificate_to_CompletePermutedLUBackwardError`, `higham9_3_denseLoopCertificate_backward_error`, `higham9_3_absBudgetCertificate_backward_error` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly added Chapter 9 wrappers reusing the compiled LU/Doolittle proof chain; the source-budget/component-dominance/exact-product-margin wrappers, exact-target gap handoff, and pivoted dense-loop certificate adapters were added in proof-completion continuations | The literal dense-loop and absolute-budget certificates expose their compression/dominance obligations as fields; the source-budget, component-dominance, exact-product-margin, exact-product-numerator, and exact-target theorems derive the absolute-budget certificate from visible literal-loop hypotheses, then the chain genuinely feeds `DoolittleLU`, `doolittle_backward_error`, and the row/complete-pivoted `PA`/`PAQ` backward-error certificate surfaces; the wrappers do not assume Theorem 9.3 or a concrete pivot trace as free hypotheses. |
| Algorithm 9.2 equations (9.3)--(9.5), rectangular exact Doolittle updates, exact-LU recurrence converse, and reduced matrix identity | `higham9_2_rectDoolittleU_source_identity`, `higham9_2_rectDoolittleL_source_identity`, `higham9_2_rectDoolittleUUpdate_eq_of_LUFactSpec`, `higham9_2_rectDoolittleLUpdate_eq_of_LUFactSpec`, `higham9_5_rectGEReducedEntry_succ_of_lt`, `higham9_5_rectGEReducedEntry_eq_DoolittleUUpdate`, `higham9_5_rectGEReducedEntry_eq_DoolittleLUpdate_mul_pivot` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in the Split 2 unifying pass continuation; exact-LU recurrence converse newly proved in this continuation | Algebraic exact-update and reduced-entry proofs over `Fin m -> Fin n` matrices; the lower identities use the explicit nonzero pivot hypothesis. The new converse theorems decompose an exact `LUFactSpec` product by triangularity to prove its square factors satisfy the Doolittle upper and lower recurrences. |
| Lemma 9.6 reduced-stage absolute-product source constant | `higham9_5_rectPrefixRange_full_eq_matMul`, `higham9_5_rectGEReducedEntry_full_eq_zero_of_LUFactSpec`, `higham9_6_rankOne_abs_le_reduced_add_succ`, `higham9_6_absLU_infNorm_le_of_reduced_stage_pair_rows`, `higham9_6_absLU_infNorm_le_two_card_mul_of_reduced_stage_row_bounds`, `higham9_6_sum_stage_pair_eq_endpoints_add_two_range`, `higham9_6_absLU_infNorm_le_source_constant_of_reduced_entry_growth`, `higham9_6_absLU_infNorm_le_source_constant_of_noPivotReducedGrowthFactor` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Uses the exact equation (9.5) recurrence to prove the rank-one stage estimate, proves terminal residual zero from `LUFactSpec`, converts neighboring-stage row-sum budgets into an infinity-norm bound, proves the source endpoint/intermediate-stage count, and derives the printed `1 + 2(n^2-n)rho_n` constant from the no-pivot reduced growth factor. |
| Theorem 9.5 max-entry growth bridge and explicit-trace/certificate specializations | `entry_abs_le_infNorm`, `maxEntryNorm_le_infNorm`, `infNorm_le_card_mul_maxEntryNorm`, `infNorm_le_card_mul_growthFactorEntry_bound`, `higham9_5_wilkinson_source_bound_of_entry_growth`, `higham9_5_wilkinson_source_bound_of_PartialPivotGEPPUTrace`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_denseLoop`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_absBudget`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_LUFactSpec`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_denseLoop`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_absBudget`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_LUFactSpec` | `LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean`; `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in the Split 2 unifying pass and extended in this proof-completion continuation | Finite row-sum/max-entry inequalities convert the source max-entry growth bound into the infinity-norm bridge. The explicit partial-pivoting, row-pivoted, complete-pivoted, dense-loop, absolute-budget, and exact-certificate trace/certificate wrappers instantiate the growth factor from proved `U`-trace theorems while keeping the concrete pivot-loop construction, computed GEPP connection, and sharp complete-pivoting product theorem visible. |
| Theorem 9.7 arbitrary partial-pivoting `U` trace growth upper bound and Wilkinson attainability package | `higham9_7_PartialPivotGEPPUTrace`, `higham9_7_PartialPivotGEPPUTrace_upper_zero`, `higham9_7_PartialPivotGEPPUTrace_entry_abs_le_pow_two`, `higham9_7_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two`, `higham9_7_exists_PartialPivotGEPPUTrace_of_det_ne_zero`, `higham9_7_exists_PartialPivotGEPPUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero`, `higham9_7_wilkinsonGrowth_attains_partialPivoting_bound`, `higham9_7_partialPivoting_growth_bound_and_attainment` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved/packaged in this continuation | Defines the explicit recursive partial-pivoting upper-factor trace, proves the exposed `U` is upper triangular and satisfies `|U i j| <= 2^(n-1) maxEntryNorm A`, constructs such a trace for nonsingular inputs by recursive nonzero partial pivots and Schur-complement determinant inheritance, derives the source exact-arithmetic growth bound `rho_n^p <= 2^(n-1)`, and packages this upper bound with the displayed Wilkinson no-interchange witness attaining `2^(n-1)`. |
| Theorem 9.5 / Theorem 9.7 partial-pivoting exact trace-to-solve bridge | `higham9_7_luFirstSchurComplement_trailingRowPerm`, `higham9_5_wilkinson_source_bound_of_PermutedLUFactSpec_growth`, `higham9_7_PartialPivotGEPPUTrace_exists_PermutedLUFactSpec_L_bound_maxEntryNorm_le`, `higham9_5_wilkinson_source_bound_exists_of_PartialPivotGEPPUTrace` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Proves that a recursive GEPP trace yields a cumulative exact `PA = LU` certificate with unit-bounded multipliers and certificate `U` no larger than the trace, then applies the generic row-pivoted exact-certificate growth bridge at elementary `2^(n-1)` strength. The rounded GEPP implementation-to-certificate construction remains open. |
| Problem 9.9 exact no-pivot reduced-matrix and final-`U` growth bounds | `higham_problem9_9_noPivotReducedEntryMax`, `higham_problem9_9_noPivotReducedGrowthFactor`, `higham_problem9_9_noPivotReducedEntryMax_le_maxEntryNorm_add_absLU_infNorm`, `higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_absLU_infNorm_div`, `growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div`, `higham_problem9_9_growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div` | `LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean`; `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | The reduced-matrix growth-factor theorem is newly proved in this continuation; the final-`U` exact-LU theorem was newly proved in the prior continuation | Bounds each equation (9.5) reduced entry by `maxEntry(A) + || |L||U| ||_inf`, takes the source stage maximum, divides by `maxEntry(A)`, and uses the existing `infNorm_le_card_mul_maxEntryNorm` bridge; the final-`U` theorem isolates a unit-lower LU row and follows the same norm bridge. |
| Theorem 9.8 real max-entry `theta <= n` subclaim | `inverse_row_identity_le_card_mul_maxEntryNorm`, `theta_le_card_of_inverse_row_identity`, `higham9_8_theta_le_card_real` | `LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean`; `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved | Finite-sum triangle inequality and max-entry bounds; no theorem-equivalent hypothesis. |
| Theorem 9.8 / equation (9.13) complex max-entry `theta <= n` subclaim | `higham9_13_inverse_row_identity_le_card_mul_complexMaxEntryNorm`, `higham9_8_theta_le_card_complex` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Uses complex norm triangle inequality, multiplicativity of complex norm, and finite max-entry bounds from `higham9_13_complexMaxEntryNorm`; no pivot trace or inverse theorem is assumed. |
| Theorem 9.8 / equation (9.13) complex `rho >= theta` bridge | `higham9_13_complexGrowthFactorEntry`, `higham9_8_complexGrowthFactorEntry_ge_inverse_entry_theta`, `higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Mirrors the real max-entry growth bridge for complex entry norms and specializes `theta(V_n)=n`; the standalone bridge still exposes the final-pivot inverse-entry witness, and the later complex certificate construction discharges that witness for the Fourier/Vandermonde certificate-level row. |
| Theorem 9.8 / equation (9.13) complex complete-pivoting trace/certificate construction and final-pivot bridge | `higham9_13_complexMaxEntryNorm_nonneg`, `higham9_13_complexMaxEntryNorm_le_of_entry_le_bound`, `higham9_13_complexMaxEntryNorm_le_of_entry_le_max`, `higham9_8_complexCompletePivotChoice`, `higham9_8_exists_complexCompletePivotChoice`, `higham9_8_complexCompletePivotChoice_pivot_ne_zero_of_exists`, `higham9_8_complex_exists_entry_ne_zero_of_det_ne_zero`, `higham9_8_exists_first_complexCompletePivotChoice_pivot_ne_zero_of_det_ne_zero`, `higham9_8_complexFirstSchurComplement`, `higham9_8_complexLUFirstStepL`, `higham9_8_complexLUFirstStepU`, `higham9_8_complexLUFactSpec_of_firstSchurComplement_explicit`, `higham9_8_complex_firstPivotRowColSwap_det_ne_zero`, `higham9_8_complexFirstSchurComplement_det_ne_zero`, `higham9_2_complexRowColPermutedMatrix_comp`, `higham9_8_complexFirstSchurComplement_trailingPerm`, `higham9_8_exists_ComplexCompletePermutedLUFactSpec_of_det_ne_zero`, `higham9_8_complex_det_ne_zero_of_isRightInverse`, `higham9_13_exists_fourierVandermonde_complexCompletePermutedLUFactSpec_growth_ge_card`, `higham9_8_ComplexCompletePivotGECPUTrace`, `higham9_8_ComplexCompletePivotGECPUTrace_upper_zero`, `higham9_8_exists_ComplexCompletePivotGECPUTrace_of_det_ne_zero`, `higham9_8_exists_ComplexCompletePivotGECPUTrace_upper_zero_of_det_ne_zero`, `higham9_8_ComplexCompletePivotGECPUTrace_exists_ComplexCompletePermutedLUFactSpec_complexMaxEntryNorm_le`, `higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card_of_ComplexCompletePivotGECPUTrace`, `higham9_13_exists_fourierVandermonde_ComplexCompletePivotGECPUTrace_growth_ge_card`, plus the earlier complex inverse/final-pivot declarations ending in `higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card_of_completePermutedLUFactSpec` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation; the explicit final-pivot bridge was proved in the prior continuation | Constructs a recursive exact complex complete-pivoting `U` trace for every nonsingular complex input, constructs an exact cumulative complex `PAQ = LU` certificate by lifting trailing permutations through Schur complements, derives determinant nonzero from a visible complex right inverse, proves the complex trace-to-certificate max-entry transfer, and instantiates the Fourier/Vandermonde inverse formula to produce both certificate-level and trace-level complex complete-pivoting growth theorems `n <= rho`. |
| Theorem 9.8 real max-entry `rho >= theta` bridge, exact final-pivot witness, and cumulative complete-pivoting certificate | `growthFactorEntry_ge_inverse_entry_theta`, `higham9_8_growth_factor_ge_theta_real`, `higham9_8_finalPivot_mul_inverse_entry_eq_one`, `higham9_8_finalPivot_inverse_entry_abs_inv_le_maxEntryNorm`, `higham9_8_growth_factor_ge_theta_of_lu_right_inverse`, `higham9_2_rowColPermutedMatrix_right_inverse`, `higham9_8_finalPivot_mul_inverse_entry_eq_one_of_completePermutedLUFactSpec`, `higham9_8_finalPivot_inverse_entry_abs_inv_le_maxEntryNorm_of_completePermutedLUFactSpec`, `higham9_8_growth_factor_ge_theta_of_completePermutedLUFactSpec_right_inverse`, `higham9_8_luFirstSchurComplement_trailingPerm`, `higham9_8_exists_CompletePermutedLUFactSpec_of_det_ne_zero`, `higham9_8_exists_completePivoting_growth_factor_ge_theta_real` | same | Newly proved; the cumulative certificate declarations were added in this continuation | Proves the inverse-entry/final-pivot witness implication algebraically, derives the source equation (9.11) witness from either `A = L U` or an explicit complete-permuted `P A Q = L U` certificate, and constructs such a cumulative real complete-pivoting certificate for every nonsingular real input. No Wilkinson upper-bound theorem, bounded `g(n)` theorem, or hidden inverse theorem is assumed. |
| Theorem 9.8 recursive complete-pivoting `U` trace support | `higham9_8_CompletePivotGECPUTrace`, `higham9_8_CompletePivotGECPUTrace_upper_zero`, `higham9_8_exists_CompletePivotGECPUTrace_of_det_ne_zero`, `higham9_8_exists_CompletePivotGECPUTrace_upper_zero_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Defines the exact recursive complete-pivoting upper-factor trace, proves the exposed `U` is upper triangular, and constructs such a trace for every nonsingular real input by complete-pivot selection plus Schur-complement determinant inheritance. It does not assume or prove the complete-pivoting growth bound. |
| Theorem 9.8 / Problem 9.11 complete-pivoting trace growth boundedness | `higham9_2_rowColPermutedMatrix_firstPivotRowSwap_maxEntryNorm`, `higham9_1_completePivot_rowColPermuted_partialPivotChoice_zero`, `higham9_8_completePivot_firstSchurComplement_maxEntryNorm_le_two`, `higham9_8_CompletePivotGECPUTrace_entry_abs_le_pow_two`, `higham9_8_CompletePivotGECPUTrace_growthFactorEntry_le_pow_two`, `higham9_completePivotingUTraceGrowthValues`, `higham9_completePivotingUTraceGrowthSup`, `higham9_completePivotingUTraceGrowthValues_bddAbove`, `higham9_completePivotingUTraceGrowth_le_sup`, `higham9_completePivotingUTraceGrowthValues_nonempty`, `higham9_8_completePivotingUTraceGrowthSup_le_pow_two` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved and extended in this continuation | Proves the local elementary trace-level boundedness dependency: row/column first-pivot swaps preserve max-entry norm, the first complete-pivot Schur complement has max-entry norm at most twice the source, every recursive complete-pivoting `U` trace satisfies `rho <= 2^(n-1)`, and the trace-level complete-pivoting growth-value set is bounded above, nonempty in every positive dimension, and has source-shaped supremum bound `g(n) <= 2^(n-1)`. This does not prove Wilkinson's sharper product bound (9.14). |
| Problem 9.11 trace-level complete-pivoting `g(2n)` lower bound | `maxEntryNorm_le_of_entry_le_bound`, `maxEntryNorm_le_of_entry_le_max`, `higham9_8_CompletePivotGECPUTrace_exists_CompletePermutedLUFactSpec_maxEntryNorm_le`, `higham9_8_CompletePivotGECPUTrace_growth_factor_ge_theta_real`, `higham9_11_exists_completePivotingUTrace_sine_block_growth_ge_succ`, `higham9_11_completePivotingUTraceGrowthValues_exists_ge_succ`, `higham9_11_completePivotingUTraceGrowthSup_ge_succ` | `LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean`; `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Proves the source-shaped trace-level lower bound `n + 1 <= g(2n)` by converting every recursive complete-pivoting `U` trace to a cumulative `PAQ = LU` certificate with no larger certificate max-entry norm, transferring the final-pivot inverse-entry lower bound to the trace surface, instantiating the flattened sine block, and taking the trace-level complete-pivoting supremum. |
| Equation (9.16) recursive rook-pivoting `U` trace support and elementary trace growth | `higham9_16_RookPivotGEUTrace`, `higham9_16_RookPivotGEUTrace_upper_zero`, `higham9_16_rookPivot_firstSchurComplement_entry_abs_le_two`, `higham9_16_rookPivot_firstSchurComplement_maxEntryNorm_le_two`, `higham9_16_RookPivotGEUTrace_entry_abs_le_pow_two`, `higham9_16_RookPivotGEUTrace_growthFactorEntry_le_pow_two`, `higham9_16_exists_RookPivotGEUTrace_of_det_ne_zero`, `higham9_16_exists_RookPivotGEUTrace_upper_zero_of_det_ne_zero`, `higham9_16_exists_RookPivotGEUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Defines the exact recursive rook-pivoting upper-factor trace, proves the exposed `U` is upper triangular, constructs such a trace for every nonsingular real input by using a complete-pivot maximum as a valid rook pivot and then applying the row/column first-pivot Schur-complement determinant inheritance theorem, proves the elementary trace-level bound `rho <= 2^(n-1)`, and packages the nonsingular source-facing existential growth theorem under the standard positive max-entry side condition. It does not assume or prove Foster's sharper rook-pivoting growth bound. |
| Equation (9.16) rook-pivoting trace growth-value endpoint | `higham9_16_rookPivotingUTraceGrowthValues`, `higham9_16_rookPivotingUTraceGrowthSup`, `higham9_16_rookPivotingUTraceGrowthValues_le_pow_two`, `higham9_16_rookPivotingUTraceGrowthValues_bddAbove`, `higham9_16_rookPivotingUTraceGrowth_le_sup`, `higham9_16_rookPivotingUTraceGrowthValues_nonempty`, `higham9_16_rookPivotingUTraceGrowthSup_le_pow_two` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved and extended in this continuation | Adds the source-facing trace-level value set, supremum, direct elementary upper-bound theorem, boundedness proof, `le_sup` adapter, positive-dimensional nonemptiness, and source-shaped supremum upper bound for recursive rook-pivoting traces. This mirrors the partial- and complete-pivoting growth-family navigation surface and still leaves Foster's sharper product-bound theorem open. |
| Equation (9.16) rook-pivoting exact trace-to-solve bridge | `higham9_16_RookPivotGEUTrace_exists_CompletePermutedLUFactSpec_L_bound_maxEntryNorm_le`, `higham9_16_wilkinson_source_bound_exists_of_RookPivotGEUTrace` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Builds an exact complete-permuted LU certificate from a recursive rook trace with unit lower multipliers and certificate `U` bounded by the trace `U`, then applies the generic `PAQ = LU` growth bridge plus elementary rook trace growth to produce the Theorem 9.5 Wilkinson normwise perturbation witness. This does not prove Foster's sharper product bound or a rounded rook-pivoting loop certificate. |
| Equation (9.13) complex Fourier/Vandermonde matrix definition, full Gram support, inverse formula, and theta witness | `higham9_13_fourierVandermonde`, `higham9_13_fourierVandermonde_symm`, `higham9_13_fourierVandermonde_firstRow`, `higham9_13_fourierVandermonde_firstCol`, `higham9_13_fourierVandermonde_norm`, `higham9_13_fourierVandermonde_conj_mul_self`, `higham9_13_fourierVandermonde_column_norm_sq`, `higham9_13_fourierVandermonde_row_norm_sq`, `higham9_13_fourierRoot_pow_card`, `higham9_13_fourierRoot_ne_one`, `higham9_13_fourierRoot_geometric_sum_zero`, `higham9_13_fourierVandermonde_conj_mul_eq_pow_of_col_lt`, `higham9_13_fourierVandermonde_column_orthogonal_of_lt`, `higham9_13_fourierVandermonde_column_orthogonal`, `higham9_13_fourierVandermonde_column_gram`, `higham9_13_fourierVandermonde_row_orthogonal`, `higham9_13_fourierVandermonde_row_gram`, `higham9_13_fourierVandermondeScaledAdjoint`, `higham9_13_scaledAdjoint_mul_fourierVandermonde`, `higham9_13_fourierVandermonde_mul_scaledAdjoint`, `higham9_13_fourierVandermonde_inverse_formula`, `higham9_13_complexMaxEntryNorm`, `higham9_13_entry_norm_le_complexMaxEntryNorm`, `higham9_13_inverse_row_identity_le_card_mul_complexMaxEntryNorm`, `higham9_8_theta_le_card_complex`, `higham9_13_fourierVandermonde_complexMaxEntryNorm_eq_one`, `higham9_13_fourierVandermondeScaledAdjoint_norm`, `higham9_13_fourierVandermondeScaledAdjoint_complexMaxEntryNorm_eq_inv`, `higham9_13_fourierVandermonde_theta_eq_card` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved | Encodes the source roots-of-unity matrix with zero-based `Fin` indices, proves symmetry, first row/column identities, unit complex norm directly from the exponential argument and Mathlib's `Complex.norm_exp_ofReal_mul_I`, derives diagonal Gram entries from `conj v_rs * v_rs = 1`, proves nontrivial root-of-unity geometric cancellation, packages full row/column Gram identities, defines the source scaled adjoint `n^{-1}V_nᴴ`, proves it is a two-sided inverse by finite-sum identities, proves the general complex max-entry `theta <= n` row-identity estimate, and proves the complex max-entry identities `max |V_n| = 1`, `max |n^{-1}V_nᴴ| = 1/n`, hence `theta(V_n)=n`. |
| Equations (9.14) and (9.16) scalar complete-/rook-pivoting growth-bound RHS support | `higham9_14_completePivotWilkinsonProduct`, `higham9_14_completePivotWilkinsonBound`, `higham9_14_completePivotWilkinsonProduct_nonneg`, `higham9_14_completePivotWilkinsonProduct_pos`, `higham9_14_completePivotWilkinsonBound_nonneg`, `higham9_14_completePivotWilkinsonBound_pos`, `higham9_16_rookPivotFosterBound`, `higham9_16_rookPivotFosterBound_nonneg`, `higham9_16_rookPivotFosterBound_pos` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Records Wilkinson's displayed complete-pivoting scalar product/RHS from equation (9.14), Foster's displayed rook-pivoting RHS from equation (9.16), and their nonnegativity/positivity. This is scalar support only and does not prove either pivoting growth theorem; the recursive complete- and rook-pivoting `U` trace existence/upper-triangularity layers are recorded separately. |
| Problem 9.5 | `higham9_5_problem_lu_product`, `higham9_5_problem_abs_lu_bottom_right`, `higham9_5_problem_no_componentwise_bound` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved | Exhaustive `Fin 2` exact arithmetic; bottom-right zero in `A` blocks any componentwise scalar bound. |
| Problem 9.6 source total-nonnegative determinant and first Schur-update support | `higham9_6_twoByTwoSubmatrix`, `higham9_6_firstSchurUpdate`, `higham9_6_threeByThreeSubmatrix`, `higham9_6_IsTotallyNonnegative`, `higham9_6_totalNonnegative_submatrix`, `higham9_6_IsTotallyNonnegativeOrderTwo`, `higham9_6_totalNonnegative_entry_nonneg`, `higham9_6_totalNonnegative_twoByTwoSubmatrix_det_nonneg`, `higham9_6_totalNonnegative_to_orderTwo`, `higham9_6_twoByTwoSubmatrix_det`, `higham9_6_pivot_mul_schur_twoByTwo_det_eq_threeByThree_det`, `higham9_6_pivot_mul_schur_det_eq_source_minor`, `higham9_6_totalNonnegative_threeByThreeSubmatrix_det_nonneg`, `higham9_6_schur_twoByTwo_det_nonneg_of_totalNonnegative`, `higham9_6_twoByTwo_determinantal_inequality`, `higham9_6_totalNonnegativeOrderTwo_entry_nonneg`, `higham9_6_multiplier_nonneg_of_orderTwo`, `higham9_6_schur_update_nonneg_of_orderTwo`, `higham9_6_schur_update_le_original_of_orderTwo`, `higham9_6_abs_schur_update_le_abs_entry_of_orderTwo`, `higham9_6_schur_update_nonneg_of_totalNonnegative`, `higham9_6_abs_schur_update_le_abs_entry_of_totalNonnegative`, `higham9_6_firstSchurUpdate_trailing_orderTwo_of_totalNonnegative`, `higham9_6_firstSchurUpdate_trailing_totalNonnegative_of_totalNonnegative`, `higham9_6_firstSchurUpdate_trailing_nonneg_of_totalNonnegative`, `higham9_6_firstSchurUpdate_trailing_abs_le_original_of_totalNonnegative`, `higham9_6_firstSchurUpdate_trailing_maxEntryNorm_le_original`, `maxEntryNorm_submatrix_le`, `higham9_6_firstSchurUpdate_trailing_maxEntryNorm_le_source` | `LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean`, `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved | Defines the source all-square-minors total-nonnegative predicate, proves inherited total nonnegativity for strictly ordered square submatrices, proves its `1 by 1` and `2 by 2` consequences, packages the order-two support predicate, computes the `2 by 2` minor determinant, proves both the local `3 by 3` Sylvester identity and the arbitrary-size denominator-cleared first-pivot Schur determinant identity, derives first Schur-update `2 by 2` minor nonnegativity on trailing rows/columns, proves first-step all-minors total-nonnegativity preservation on strictly trailing square submatrices after a positive pivot, proves that a positive first pivot gives a nonnegative multiplier, no absolute-entry growth, trailing-submatrix nonnegativity, trailing absolute-entry no-growth, trailing max-entry no-growth relative to both the selected trailing submatrix and the full source matrix, and an order-two trailing-submatrix package. |
| Problem 9.6 principal-block positivity, recursive nonnegative LU construction, and growth endpoint | `higham9_6_trailingPrincipalBlock`, `higham9_6_totalNonnegative_leadingPrincipalBlock_det_nonneg`, `higham9_6_totalNonnegative_trailingPrincipalBlock_det_nonneg`, `higham9_6_totalNonnegative_det_nonneg`, `higham9_6_totalNonnegative_det_pos_of_det_ne_zero`, `higham9_6_principalBlock_determinantal_inequality_of_det_eq_zero`, `higham9_6_principalBlock_determinantal_inequality_zero`, `higham9_6_principalBlock_determinantal_inequality_full`, `higham9_6_principalBlock_determinantal_inequality_fin_two`, `higham9_6_middle_entry_pos_of_fin_three_totalNonnegative_det_pos`, `higham9_6_principalBlock_determinantal_inequality_fin_three_one_of_middle_pos`, `higham9_6_principalBlock_determinantal_inequality_fin_three_one`, `higham9_6_principalBlock_determinantal_inequality_fin_three_two_of_middle_pos`, `higham9_6_principalBlock_determinantal_inequality_fin_three_two`, `higham9_6_topLeft_pos_of_totalNonnegative_det_ne_zero`, `higham9_6_leadingPrincipalBlock_det_pos_of_totalNonnegative_det_ne_zero`, `higham9_6_principalBlock_dets_pos_of_determinantal_inequality`, `higham9_6_leadingPrincipalBlock_det_pos_of_determinantal_inequality`, `luFirstStepL`, `luFirstStepU`, `LUFactSpec.of_firstSchurComplement_explicit`, `higham9_6_luFirstStepL_nonneg`, `higham9_6_luFirstStepU_nonneg`, `higham9_6_lu_exists_nonnegative_of_totalNonnegative_and_leadingPrincipalBlock_pos`, `higham9_6_lu_exists_nonnegative_of_totalNonnegative_and_properLeadingPrincipalBlock_pos`, `higham9_6_lu_exists_nonnegative_of_totalNonnegative_det_ne_zero`, `higham9_6_nonnegativeLU_growthFactorEntry_le_one`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_and_properLeadingPrincipalBlock_pos`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero`, `higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_det_ne_zero`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_and_principalBlock_inequalities`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero_and_principalBlock_inequalities` | `LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean`, `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved; the `p = 0`/`p = n` boundary cases, the `2 by 2`, `p = 1` determinant-inequality base case, and both `3 by 3` interior cases were added in this continuation | Defines explicit one-step LU factors, proves they preserve nonnegativity for a totally nonnegative source matrix, proves the singular branch, boundary cases, `2 by 2` base case, and `3 by 3` interior determinant-inequality cases of the principal-block determinant inequality, proves first-pivot positivity and all nonempty leading principal determinants positive from total nonnegativity plus `det A != 0` by Schur-complement induction, recursively constructs exact nonnegative no-pivot LU factors from the source hypotheses, and proves final/reduced no-pivot growth endpoints. It is followed by the closed arbitrary-p Koteljanskii/Fischer determinant comparison `higham9_6_principalBlock_determinantal_inequality_of_totalNonnegative`. |
| Problem 9.7 | `higham9_7_square_submatrix_count_with_empty`, `higham9_7_rectangular_submatrix_count_with_empty`, `higham9_7_square_submatrix_count_nonempty`, `higham9_7_rectangular_submatrix_count_nonempty` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved | Reuses Mathlib binomial identities and proves shifted nonempty forms. |
| Problem 9.8 checkerboard sign-matrix, inverse transport, full selected-minor Jacobi theorem, LU adapter, and total-nonnegative-checkerboard support | `higham9_8_alternatingSign`, `higham9_8_signMatrixJ`, `higham9_8_checkerboardConjugate`, `higham9_8_abs_alternatingSign`, `higham9_8_signMatrixJ_diag`, `higham9_8_signMatrixJ_offdiag`, `higham9_8_signMatrixJ_left_mul`, `higham9_8_signMatrixJ_right_mul`, `higham9_8_abs_checkerboardConjugate`, `higham9_8_alternatingSign_sq`, `higham9_8_selected_below_card`, `higham9_8_complement_below_card`, `higham9_8_cross_complement_product_eq_pow`, `higham9_8_selectionComplementEquiv_canonical_shuffle_sign`, `higham9_8_selectionComplementEquiv_perm_sign`, `higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg_of_complement_det_ne_zero`, `higham9_8_signMatrixJ_involutive`, `higham9_8_signMatrixJ_mul_mul_eq_checkerboardConjugate`, `higham9_8_det_inv_topLeft_fromBlocks_eq_det_D_mul_inv_det`, `higham9_8_det_inv_topLeft_fromBlocks_mul_det_eq_det_D`, `higham9_8_det_inv_selected_eq_det_complement_mul_inv_det_reindexed`, `higham9_8_det_inv_selected_mul_det_reindexed_eq_det_complement`, `higham9_8_checkerboardConjugate_nonsingInv_principal_minor_nonneg_of_complement_det_ne_zero`, `higham9_8_det_selectionComplementEquiv_reindex_eq_perm_sign`, `higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg_of_complement_det_ne_zero_of_reindex_det`, `higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg`, `higham9_8_checkerboardConjugate_id`, `higham9_8_checkerboardConjugate_left_inverse`, `higham9_8_checkerboardConjugate_right_inverse`, `higham9_8_checkerboardConjugate_inverse`, `higham9_8_checkerboardConjugate_inverse_swapped`, `higham9_8_succAbove_val_strictMono`, `higham9_8_checkerboardConjugate_nonsingInv_entry_nonneg_of_det_pos`, `higham9_8_checkerboardConjugate_nonsingInv_entry_nonneg_of_det_ne_zero`, `higham9_8_checkerboardConjugate_nonsingInv_empty_minor_nonneg`, `higham9_8_checkerboardConjugate_nonsingInv_orderOne_minor_nonneg`, `higham9_8_adjugate_nonsingInv_eq_det_nonsingInv_smul`, `higham9_8_checkerboardConjugate_nonsingInv_codimOne_minor_nonneg`, `higham9_8_checkerboardConjugate_det_eq`, `higham9_8_checkerboardConjugate_nonsingInv_det_nonneg`, `higham9_8_checkerboardConjugate_nonsingInv_full_order_minor_nonneg`, `higham9_8_checkerboardConjugate_minor_det_scale`, `higham9_8_abs_checkerboardConjugate_minor_det`, `higham9_8_checkerboardConjugate_involutive`, `higham9_8_checkerboardConjugate_eq_abs_of_nonneg`, `higham9_8_checkerboardConjugate_matMul`, `higham9_8_checkerboard_lu_product_eq`, `higham9_8_lu_of_checkerboard_lu`, `higham9_8_abs_conjugated_lu_product_eq_abs`, `higham9_8_abs_lu_product_eq_abs_of_checkerboard_totalNonnegative_and_pos`, `higham9_8_abs_lu_product_eq_abs_of_checkerboard_principalBlock_inequalities` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved/reused; inverse transport, the entrywise cofactor sign-pattern theorem, empty-/order-one/codimension-one minor wrappers, full-determinant/full-order minor wrappers, Schur-complement selected-minor identities with and without a complementary-minor nonsingularity hypothesis, conditional principal inverse-minor theorem, selected/complement permutation-sign theorem, the arbitrary selected-minor nonsingular-complement consequence, and the full arbitrary selected-minor nonnegativity theorem were added across this continuation | Defines the alternating signs and diagonal checkerboard sign matrix `J`, proves diagonal/off-diagonal entries, row/column multiplication by `J`, `J^2 = I`, `J*A*J` agreement with entrywise checkerboard conjugation, proves checkerboard conjugation fixes `I` and transports left/right/two-sided inverse certificates, including the source-oriented swapped inverse direction, proves the Schur-complement/top-left and selected-minor Jacobi identities, proves the corresponding principal-minor and arbitrary selected-minor nonnegativity consequences for `J A^{-1} J`, proves the cofactor-level entrywise checkerboard sign pattern for `nonsingInv` of a nonsingular totally nonnegative matrix, packages the empty-, `1 by 1`, codimension-one, full-determinant, and full-order minor nonnegativity cases in source row/column-selection shape, proves componentwise absolute-value preservation, all-minor determinant scaling and absolute-minor preservation, proves `J`-conjugation is an involution and respects exact products, transports an LU certificate from `J A J` to `A`, proves `|JLJ||JUJ| = |A|` from explicit nonnegative `L,U` hypotheses, and uses the recursive Problem 9.6 nonnegative-LU theorem to supply those factors from visible total-nonnegative and principal-block hypotheses on `J A J`. The source-cited all-minors inverse/Jacobi complementary-minor theorem is closed locally by `higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg`; no equivalent theorem is assumed. |
| Problem 9.11 block-doubling algebra, `g(n)` supremum adapter, and equation (9.12) sine-matrix finite-sum/inverse/theta support | `higham9_11_flatBlockIndex`, `higham9_11_flatInnerIndex`, `higham9_11_flattenTwoBlock`, `higham9_11_flatIndexOfBlock`, `higham9_11_flatBlockIndex_flatIndexOfBlock`, `higham9_11_flatInnerIndex_flatIndexOfBlock`, `higham9_11_flatIndexOfBlock_flatBlockIndex_flatInnerIndex`, `higham9_11_flatBlockInner_eq_iff`, `higham9_11_flatBlockEquiv`, `higham9_11_flattenTwoBlock_entry_flatIndexOfBlock`, `higham9_11_flattenTwoBlock_maxEntryNorm_eq_blockMaxNorm`, `higham9_11_blockInverseCandidate_left`, `higham9_11_blockInverseCandidate_right`, `higham9_11_flattenTwoBlock_matMul_entry`, `higham9_11_flattenTwoBlock_right_inverse`, `higham9_det_ne_zero_of_isRightInverse`, `higham9_11_alpha_block_eq`, `higham9_11_flatten_blockMatrix_maxEntryNorm_eq`, `higham9_11_beta_blockInv_eq`, `higham9_11_flatten_blockInverseCandidate_maxEntryNorm_eq`, `higham9_11_theta_block_eq_two_theta`, `higham9_11_sine_block_theta_candidate_ge_succ`, `higham9_11_complete_pivoting_lower_bound_from_sine_block_theta`, `higham9_11_complete_pivoting_lower_bound_consequence`, `higham9_11_complete_pivoting_lower_bound_consequence_le`, `higham9_completePivotGrowthSet`, `higham9_completePivotGrowthSup`, `higham9_completePivotGrowth_le_sup`, `higham9_11_complete_pivoting_lower_bound_from_witness`, `higham9_11_complete_pivoting_lower_bound_from_witness_le`, `higham9_11_complete_pivoting_lower_bound_from_flattened_sine_block`, `higham9_11_complete_pivoting_lower_bound_from_flattened_sine_block_maxEntry`, `higham9_11_exists_completePivoting_sine_block_growth_ge_succ`, `higham9_12_sineMatrix`, `higham9_12_sineMatrix_symm`, `higham9_12_sineMatrix_entry_abs_le_scale`, `higham9_12_sineMatrix_maxEntryNorm_le_scale`, `higham9_12_sineMatrix_zero_zero_pos`, `higham9_12_sineMatrix_maxEntryNorm_pos`, `higham9_12_cos_sum_even`, `higham9_12_cos_sum_odd`, `higham9_12_cos_sum_pos_lt_two_mul`, `higham9_12_cos_sum_eq_of_mod_two_eq`, `higham9_12_sine_product_sum`, `higham9_12_sineMatrix_mul_self`, `higham9_12_sineMatrix_inverse_formula`, `higham9_12_theta_ge_half_succ_of_maxEntryNorm_le_scale`, `higham9_12_two_theta_ge_succ_of_maxEntryNorm_le_scale`, `higham9_12_sineMatrix_theta_candidate_ge_half_succ`, `higham9_12_sineMatrix_two_theta_candidate_ge_succ` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved/extended | Reuses Chapter 12's `blockMatProd`/`blockMaxNorm` API and proves the displayed block inverse formula, max-entry identities, theta doubling, the block-doubled sine theta lower bound, arithmetic lower-bound consequences from explicit equality or inequality hypotheses, the visible-witness, flattened sine-block, flattened max-entry lower-bound bridges, flattened matrix-multiplication/right-inverse transport, and the actual cumulative complete-pivoting growth certificate for the flattened real sine block with growth at least `n + 1`. It also records the source equality- and inequality-form supremum steps, the ordinary max-entry-norm flattened witness form from a concrete witness to `g(2n)` for a bounded growth family, and the source equation (9.12) sine matrix definition, symmetry, `|sin| <= 1` scale bounds, positive `(0,0)` entry, positive max-entry norm, finite roots-of-unity/cosine-sum parity support, discrete sine orthogonality, self-inverse formula, and theta lower-bound arithmetic. The trace-level source-shaped `g(2n)` lower bound is closed by the dedicated row above; Wilkinson's sharper product upper-bound theorem remains separate equation (9.14) work. |
| Theorem 9.11 Bohte scalar formula support | `higham9_11_bohteBound`, `higham9_11_bohteBound_tridiagonal`, `higham9_11_bohteBound_pentadiagonal_formula`, `higham9_11_bohteBound_bandwidth_four_formula`, `higham9_11_bohteBound_nonneg`, `higham9_11_bohte_banded_solve_tight` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved | Records the printed banded-growth scalar expression, proves the unambiguous tridiagonal `p = 1` special case `2`, records that the formal expression evaluates to `7` at `p = 2`, records the source example scalar value `116` at `p = 4`, proves the scalar is nonnegative for all natural `p`, and specializes the conditional solve wrapper to the Bohte constant. The full banded GEPP growth theorem and attainability are not claimed. |
| Problem 9.13 threshold pivoting | `higham9_13_threshold_update_abs_bound`, `higham9_13_column_growth_by_modification_count`, `higham9_13_growthFactorEntry_bound_of_column_counts`, `higham9_13_growthFactorEntry_bound_from_column_modifications` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved | Proves the scalar threshold update, iterates it over `mu_j` sparse-column modifications, and derives the max-entry growth-factor bound. |
| Problem 9.2 finite-exception shifted-matrix LU theorem | `higham9_2_danger_shift_count_bound`, `higham9_2_charpolyDangerSet`, `higham9_2_mem_charpolyDangerSet_iff_isRoot`, `higham9_2_mem_charpolyDangerSet_iff_det_shift_eq_zero`, `higham9_2_charpolyDangerSet_card_le`, `higham9_2_charpoly_danger_shift_count_bound`, `higham9_2_leadingPrincipalBlock`, `higham9_2_leadingBlockDangerSet`, `higham9_2_shiftedLeadingBlock`, `higham9_2_mem_leadingBlockDangerSet_iff_det_shift_eq_zero`, `higham9_2_shiftedLeadingBlock_det_ne_zero_of_not_mem_danger_union`, `higham9_2_leadingBlockDangerSet_card_le`, `higham9_2_leadingBlockDangerSet_count_bound`, `higham9_2_shiftedMatrix`, `higham9_2_shiftedMatrixDangerSet`, `higham9_2_shiftedMatrixDangerSet_card_le`, `higham9_2_shiftedMatrix_properLeadingPrincipalBlock_det_ne_zero_of_not_mem_danger`, `higham9_2_shiftedMatrix_lu_exists_unique_of_not_mem_danger`, `higham_problem9_2_shiftedMatrix_lu_exists_unique_except_card_bound` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved | Uses `Finset.card_biUnion_le`, `Finset.sum_range_id`, Mathlib polynomial-root cardinality, matrix characteristic-polynomial degree/evaluation facts, an explicit leading-principal-block extraction, finite-union membership, and the closed Theorem 9.1 proper-leading-minor LU criterion to prove that outside a set of at most `n(n-1)/2` shifts, `sigma I - A` has a unique exact no-pivot LU factorization. |
| Equation (9.1) determinant-pivot product for exact LU | `LUFactSpec.det_eq_prod_U_diag`, `LUFactSpec.det_ne_zero_iff_U_diag_ne_zero`, `higham9_1_det_eq_pivot_product`, `higham9_1_det_ne_zero_iff_pivots_ne_zero` | `LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean`; `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Uses Mathlib determinant multiplicativity and triangular determinant formulas to prove `det(A) = prod_i u_ii` from the repository `LUFactSpec`, with the unit lower factor contributing determinant one; no LU existence theorem is assumed. |
| Theorem 9.1 / Problems 9.1-9.2 leading-principal determinant-pivot support, first Schur-complement LU construction step, proper Schur determinant inheritance, exact LU existence/uniqueness iff, and Problem 9.1 converse | `higham9_1_firstSchurComplement`, `higham9_1_lu_exists_of_firstSchurComplement`, `higham9_1_firstSchurComplement_properLeadingPrincipalBlock_det_ne_zero`, `higham9_1_lu_exists_of_properLeadingPrincipalBlock_det_ne_zero`, `higham9_1_leadingPrincipalBlock_det_eq_pivot_product`, `higham9_1_leadingPrincipalBlock_det_ne_zero_iff_pivots_ne_zero`, `higham9_1_lu_unique_of_proper_pivots_ne_zero`, `higham9_1_lu_unique_of_properLeadingPrincipalBlock_det_ne_zero`, `higham9_1_lu_exists_and_unique_of_properLeadingPrincipalBlock_det_ne_zero`, `higham9_1_lu_nonunique_of_zero_proper_pivot`, `higham_problem9_1_properLeadingPrincipalBlock_det_ne_zero_of_unique_lu`, `higham9_1_lu_exists_unique_iff_properLeadingPrincipalBlock_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean`, `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Source-strength Schur determinant inheritance, determinant-integrated exact-LU existence/uniqueness, and the singular unique-LU converse newly proved in this continuation; earlier exact-certificate determinant support reused | The one-step theorem constructs explicit full `L,U` from a nonzero pivot and an exact LU certificate for the first Schur complement; the proper determinant inheritance theorem proves the Schur complement recursively has nonzero proper leading principal determinants; induction gives exact LU existence from Higham's `k = 1 : n-1` hypotheses; uniqueness proceeds from proper nonzero pivots and triangularity in the final column; the converse uses a lower-shear construction to show any zero proper pivot yields a distinct exact LU certificate, forcing proper leading determinants nonzero under uniqueness. |
| Equations (9.2a)--(9.2b) and Theorem 9.3 permuted LU certificate adapters | `higham9_2_rowPermutedMatrix`, `higham9_2_rowPermutedMatrix_maxEntryNorm`, `higham9_2_rowPermutedMatrix_infNorm`, `higham9_2_colPermutedMatrix`, `higham9_2_colPermutedMatrix_maxEntryNorm`, `higham9_2_colPermutedMatrix_infNorm`, `higham9_2_rowColPermutedMatrix`, `higham9_2_rowColPermutedMatrix_maxEntryNorm`, `higham9_2_rowColPermutedMatrix_infNorm`, `higham9_2_PermutedLUFactSpec`, `higham9_2_permutedLUFactSpec_to_LUFactSpec`, `higham9_2_PermutedLUBackwardError`, `higham9_2_permutedLUBackwardError_to_LUBackwardError`, `higham9_2_permutedLUFactSpec_to_PermutedLUBackwardError_zero`, `higham9_2_permutedLUFactSpec_to_PermutedLUBackwardError_gamma`, `higham9_3_permuted_lu_backward_error_gamma`, `higham9_3_permuted_lu_backward_error_gamma_of_LUFactSpec`, `higham9_2_CompletePermutedLUFactSpec`, `higham9_2_completePermutedLUFactSpec_to_LUFactSpec`, `higham9_2_CompletePermutedLUBackwardError`, `higham9_2_completePermutedLUBackwardError_to_LUBackwardError`, `higham9_2_completePermutedLUFactSpec_to_CompletePermutedLUBackwardError_zero`, `higham9_2_completePermutedLUFactSpec_to_CompletePermutedLUBackwardError_gamma`, `higham9_3_complete_permuted_lu_backward_error_gamma`, `higham9_3_complete_permuted_lu_backward_error_gamma_of_LUFactSpec`, `higham9_3_exists_complete_permuted_lu_backward_error_gamma_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved and extended in this continuation | Models the source `PA` entries as `A (sigma i) j` and `PAQ` entries as `A (sigma i) (tau j)`, converts explicit permuted LU and backward-error certificates to the existing unpermuted LU APIs for the corresponding permuted matrix, applies the compiled `gamma_n` perturbation theorem, preserves max-entry/infinity norms under row, column, and row/column permutations, and now exposes exact-certificate zero/gamma backward-error packages. It does not construct the rounded cumulative pivoted or complete-pivoted executable traces. |
| Equations (9.2a)--(9.2b), determinant-pivot consequences for explicit permuted LU certificates | `higham9_2_permutedLUFactSpec_det_eq_pivot_product`, `higham9_2_permutedLUFactSpec_det_ne_zero_iff_pivots_ne_zero`, `higham9_2_completePermutedLUFactSpec_det_eq_pivot_product`, `higham9_2_completePermutedLUFactSpec_det_ne_zero_iff_pivots_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Reuses the permuted-certificate adapters to view `PA` and `PAQ` as ordinary exact LU certificates, then applies the existing determinant-pivot theorem and nonzero-pivot consequence; it does not construct the cumulative pivoted or complete-pivoted certificate traces. |
| Theorem 9.9 / 9.13 real-transpose row-column orientation adapters | `higham9_9_colDiagDominant_transpose_iff_rowDiagDominant`, `higham9_9_rowDiagDominant_transpose_iff_colDiagDominant`, `higham9_13_tridiagonal_transpose_iff` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved | Direct finite-index unfolding proves row/column diagonal dominance equivalence under transpose and tridiagonal preservation/reflection under transpose. |
| Theorem 9.9 diagonal-dominance nonsingularity side condition | `higham9_9_rowDiagDominant_zero_diag_row_zero`, `higham9_9_colDiagDominant_zero_diag_col_zero`, `higham9_9_rowDiagDominant_diag_ne_zero_of_det_ne_zero`, `higham9_9_colDiagDominant_diag_ne_zero_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved | Finite nonnegative-sum algebra shows a zero diagonal entry forces a zero row or column under row/column diagonal dominance, and `Matrix.det_eq_zero_of_row_eq_zero`/`Matrix.det_eq_zero_of_column_eq_zero` contradict nonsingularity. |
| Theorem 9.9 diagonal-dominance off-diagonal and first-ratio bounds | `higham9_9_rowDiagDominant_offdiag_abs_le_diag`, `higham9_9_colDiagDominant_offdiag_abs_le_diag`, `higham9_9_rowDiagDominant_entry_ratio_abs_le_one`, `higham9_9_colDiagDominant_entry_ratio_abs_le_one`, `higham9_9_rowDiagDominant_entry_ratio_abs_le_one_of_det_ne_zero`, `higham9_9_colDiagDominant_entry_ratio_abs_le_one_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved | Finite nonnegative-sum comparison proves each off-diagonal entry is bounded by the corresponding row or column diagonal entry; division by the nonzero diagonal gives the visible unit first-ratio bound. |
| Theorem 9.9 column-dominant exact no-pivot LU support | `higham9_9_colDiagDominant_first_column_multiplier_sum_le_one`, `higham9_9_colDiagDominant_first_column_multiplier_sum_except_le`, `higham9_9_colDiagDominant_firstSchurComplement`, `higham9_9_colDiagDominant_firstSchurComplement_maxEntryNorm_le_two`, `higham9_9_colDiagDominant_firstSchurComplement_offdiag_le_maxEntryNorm`, `higham9_9_colDiagDominant_firstSchurComplement_det_ne_zero`, `higham9_9_colDiagDominant_lu_exists_unit_lower_of_det_ne_zero`, `higham9_9_colDiagDominant_lu_exists_unique_unit_lower_of_det_ne_zero` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved; the off-diagonal max-entry invariant was added in this continuation | Finite column-dominance sums bound the first no-pivot multiplier column, split off one selected trailing multiplier, preserve column diagonal dominance under the first Schur complement, bound the first Schur complement's max-entry norm by `2 * maxEntryNorm A`, bound its off-diagonal trailing entries by the original `maxEntryNorm A`, transfer nonsingularity by the Schur determinant identity, and recursively construct exact no-pivot LU factors whose lower entries are unit-bounded; exact-LU uniqueness follows from the determinant-pivot product. |
| Theorem 9.13 structural componentwise and max-entry `rho <= 3` consequences | `growthFactorEntry_le_of_absLU_componentwise`, `maxEntryNorm_matTranspose`, `LUFactSpec.isTridiagLU_of_tridiagonal`, `tridiag_colDom_L_entries_bounded`, `tridiag_rowDom_growth_bound_3`, `higham9_13_tridiag_growth_bound_3_of_LUFactSpec`, `higham9_13_growthFactorEntry_le_three_of_LUFactSpec`, `higham9_13_colDiagDom_L_entries_bounded_of_LUFactSpec`, `higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec`, `higham9_13_colDiagDom_growthFactorEntry_le_three_of_LUFactSpec`, `higham9_13_colDiagDom_exists_LUFactSpec_growth_bound_3`, `higham9_13_colDiagDom_exists_LUFactSpec_growthFactorEntry_le_three`, `higham9_13_rowDiagDom_transpose_exists_LUFactSpec_growth_bound_3`, `higham9_13_rowDiagDom_transpose_exists_LUFactSpec_growthFactorEntry_le_three`, `higham9_13_LUFactSpec_of_transpose_LUFactSpec_nonzero_pivots`, `higham9_13_rowDiagDom_exists_LUFactSpec_growth_bound_3`, `higham9_13_rowDiagDom_exists_LUFactSpec_growthFactorEntry_le_three`, `higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec`, `higham9_13_rowDiagDom_growthFactorEntry_le_three_of_LUFactSpec`, `higham9_13_tridiag_growthFactorEntry_le_three`, `higham9_13_rowDiagDom_transpose_tridiag_growth_bound_3`, `higham9_13_rowDiagDom_transpose_growthFactorEntry_le_three`, `higham9_13_rowDiagDom_transpose_growthFactorEntry_le_three_of_Amax`, `higham9_13_rowDiagDom_tridiag_growth_bound_3`, `higham9_13_rowDiagDom_growthFactorEntry_le_three` | `LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean`; `LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean`; `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved across this continuation and the exact-LU/multiplier handoff updates | Proves that any componentwise `|L||U| <= c|A|` bound with unit lower diagonal implies Higham max-entry growth `rho <= c`, instantiates `c = 3` using the local column-dominant tridiagonal theorem, proves the direct row-dominant componentwise theorem by induction on the tridiagonal recurrence, proves that exact `LUFactSpec` factors of a tridiagonal matrix inherit lower/upper bidiagonal structure from nonzero pivots, proves the column-dominant multiplier bound from column diagonal dominance, and provides source-facing exact-LU wrappers without a separate multiplier hypothesis, including the row-dominant transpose existential package for exact factors of `Aᵀ` and the direct row-dominant existential package for exact factors of `A` obtained by rescaling the transposed LU pivots. |
| Theorem 9.13 source-data tridiagonal builder growth surface | `tridiag_L_lower_bidiag`, `tridiag_U_upper_bidiag`, `tridiag_matrices_isTridiagLU`, `tridiag_L_matrix_entries_bounded`, `tridiag_prevIndex`, `TridiagExactLURecurrence`, `tridiag_exact_product_of_recurrence`, `higham9_19_tridiag_exact_product_of_recurrence`, `higham9_13_tridiag_builder_growth_bound_3`, `higham9_13_tridiag_builder_growthFactorEntry_le_three`, `higham9_13_rowDiagDom_tridiag_builder_growth_bound_3`, `higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three`, `higham9_13_tridiag_builder_growth_bound_3_of_recurrence`, `higham9_13_tridiag_builder_growthFactorEntry_le_three_of_recurrence`, `higham9_13_rowDiagDom_tridiag_builder_growth_bound_3_of_recurrence`, `higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three_of_recurrence` | `LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean`; `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in this continuation | Proves the explicit tridiagonal matrix builders satisfy `IsTridiagLU`, derives entrywise unit bounds for builder `L` from the stored multiplier vector, proves the exact recurrence-to-product theorem for equation (9.19), and instantiates the column- and row-dominant Theorem 9.13 componentwise/max-entry growth wrappers over source `TridiagData` without hiding exact-recurrence or dominance assumptions. |
| Theorem 9.12 optimal-growth max-entry consequence and SPD positive-`D L^T` algebraic core | `tridiag_spd_shape_absLU_eq_absA`, `higham9_12_spd_tridiag_absLU_eq_of_positive_DLT`, `higham9_12_spd_tridiag_growthFactorEntry_le_one`, `higham9_12_spd_tridiag_growthFactorEntry_le_one_of_spd`, `higham9_12_spd_tridiag_lu_backward_error_of_positive_DLT`, `higham9_12_spd_tridiag_builder_absLU_eq_of_positive_DLT`, `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one`, `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_spd`, `higham9_12_spd_tridiag_builder_lu_backward_error_of_positive_DLT`, `higham9_12_spd_tridiag_builder_absLU_eq_of_recurrence`, `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_recurrence`, `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_spd_recurrence`, `higham9_12_spd_tridiag_builder_lu_backward_error_of_recurrence`, `higham9_growthFactorEntry_le_one_of_absLU_le_absA`, `higham9_12_nonneg_lu_growthFactorEntry_le_one`, `higham9_12_mmatrix_lu_growthFactorEntry_le_one`, `higham9_12_sign_equiv_growthFactorEntry_le_one`, `higham9_12_totalNonnegative_exists_LUFactSpec_optimal_growth`, `higham9_12_totalNonnegative_exists_LUFactSpec_growthFactorEntry_le_one` | `LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean`; `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly extended in this continuation | Proves Higham's SPD "middle equality" step for tridiagonal bidiagonal LU factors satisfying `U = D L^T` with `D > 0`, yielding `|L||U| = |A|`, the corresponding `rho <= 1` growth consequence, the source-facing SPD variants deriving the positive `maxEntryNorm A` denominator from SPD nonsingularity, and the SPD backward-error handoff under explicit certificate hypotheses; the explicit `TridiagData` builder and equation-(9.19) exact-recurrence variants discharge the structural and exact-product certificates from local builder facts. Also proves that a unit-lower factor and an optimal componentwise `|L||U| <= |A|` bound force every final `U` entry to be bounded by `maxEntryNorm A`, hence Higham's max-entry growth factor is at most one; the nonnegative-LU specialization reuses `nonneg_lu_optimal_growth`, the M-matrix specialization reuses `mmatrix_lu_optimal_growth`, the sign-equivalent specialization reuses `sign_equiv_optimal_growth`, and the total-nonnegative/nonsingular source-existence wrappers reuse Problem 9.6 to produce exact nonnegative LU factors plus optimal componentwise growth and `rho <= 1`. |
| Theorem 9.14 source scalar `f(u)`/`h(u)` aggregation | `higham9_14_f`, `higham9_14_h`, `higham9_14_h_eq_f_div`, `higham9_14_f_nonneg`, `higham9_14_h_mul_one_sub_eq_f`, `higham9_14_source_f_bound`, `higham9_14_source_h_bound_of_absLUhat_bound`, `higham9_14_source_h_bound_of_absLUhat_mul_one_sub_bound` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved | The source polynomial `f(u)` is recorded, `h(u)` is defined as `f(u)/(1-u)`, nonnegativity is proved for `0 <= u`, `lu_solve_backward_error_mixed` proves that source coefficients `u`, `u`, and `2u+u^2` combine to the printed `f(u)`, and the denominator-cleared source comparison `(1-u)|Lhat||Uhat| <= |A|` is converted to the same conditional `h(u)` bound. |
| Equation (9.23) forward-error condition-product wrapper | `higham9_23_condSkeel_nonneg`, `higham9_23_forward_error_exact_condSkeel`, `higham9_23_firstOrderLe_of_backward_error_coeff`, `higham9_23_forward_error_firstOrder_cond_product` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in the 2026-06-27 proof-completion pass | Reuses the Chapter 7 relative infinity-norm forward-error theorem with `E = |A|`, `f = 0`, and `M = condSkeel(A)`, proves the exact denominator bound for an unperturbed right-hand side, and packages the source `3 n u cond(A) cond(U) + O(u^2)` form through `FirstOrderLe` from a visible row-wise coefficient hypothesis. |
| Equation (9.8) | `higham9_8_nonneg_factor_bound` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Reused wrapper | Genuine nonnegative-factor proof from LU modules. |
| Equations (9.18), (9.19) | `higham9_18_TridiagData`, `higham9_18_tridiag_to_matrix`, `higham9_18_tridiag_to_matrix_isTridiagonal`, `higham9_19_tridiag_lu`, `higham9_19_TridiagExactLURecurrence`, `higham9_19_tridiag_prevIndex`, `higham9_19_tridiag_exact_product_of_recurrence` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Reused wrappers plus new structural bridge and exact-recurrence product theorem | Tridiagonal data and LU recurrence are executable mathematical definitions, the assembled equation-(9.18) matrix is proved tridiagonal, and the exact-arithmetic recurrence version of equation (9.19) is proved to multiply back to the source tridiagonal matrix. |
| Equation (9.24) | `higham9_24_scaled_system_equiv` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Reused wrapper | Direct algebraic equivalence proof. |
| Equation (9.25) | `higham9_25_trailingRowInf`, `higham9_25_implicitRowScalingPivotRule` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Reused definitions | Source pivot rule encoded as a predicate, not counted as a theorem beyond its definition. |
| Problem 9.3 field-of-values LU existence/uniqueness route | `higham_problem9_3_complexOfReal`, `higham_problem9_3_zeroNotInFieldOfValues`, `higham_problem9_3_properLeadingPrincipalBlock_det_ne_zero_of_zeroNotInFieldOfValues`, `higham_problem9_3_lu_exists_unique_of_zeroNotInFieldOfValues` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in the 2026-06-27 proof-completion pass | Formalizes the Appendix A argument: if zero is excluded from the field of values, a singular proper leading block would give a nonzero embedded complex vector with `z^*Az = 0`; hence all proper leading blocks are nonsingular and Theorem 9.1 yields unique exact no-pivot LU. |
| Equation (9.26) a posteriori Holder bound | `higham9_26_prefixLpNorm`, `higham9_26_holder_prefix_dot_abs_le`, `higham9_26_stage_entry_abs_le`, `higham9_26_stage_entry_abs_le_of_uniform_bounds` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in the 2026-06-27 proof-completion pass | Reuses the shared finite complex `L^p` Holder theorem, bridges real LU prefix dot products through complex casts, proves the displayed one-entry stage bound, and packages the second source inequality using explicit uniform budgets for the original entry and prefix row/column norms. |
| Equation (9.27) `G = L^{-1} ΔA U^{-1}` norm-product and ratio support | `higham9_27_GMatrix`, `higham9_27_GMatrix_frobenius_le`, `higham9_27_GMatrix_opNorm2Le`, `higham9_15_ratio_le_of_norm_bounds`, `higham9_27_GMatrix_ratio_le_product_ratio` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Newly proved in the 2026-06-27 proof-completion pass | Reuses the shared Frobenius/operator-2 product lemmas and ordered-field denominator monotonicity to prove the norm-product and ratio support for the Barrlund--Sun right-hand side. This does not claim the full nonlinear/spectral Theorem 9.15. |
| Theorem 9.15 algebraic perturbation, componentwise forward wrappers, `χ(A)` condition chain, normalized identities/splits, inverse-normalization, assembly, and conditional normwise/componentwise endpoints | `higham9_15_lu_perturbation_identity`, `higham9_15_lu_perturbation_relative_bound`, `higham9_15_lu_perturbation_forward_bound`, `higham9_15_chi`, `higham9_15_chi_nonneg`, `higham9_15_rectMatMul_opNorm2Le`, `higham9_15_kappa2_le_chi_of_inverse_product_bound`, `higham9_15_chi_le_kappa2L_mul_kappa2A_of_Uinv_bound`, `higham9_15_chi_le_kappa2U_mul_kappa2A_of_Linv_bound`, `higham9_15_chi_condition_chain_of_inverse_product_bounds`, `higham9_15_chi_condition_chain_min_of_inverse_product_bounds`, `higham9_15_chi_condition_chain_of_inverse_products`, `higham9_15_chi_condition_chain_min_of_inverse_products`, `higham9_15_normalized_G_factorization_matrix`, `higham9_15_normalized_Gtilde_factorization_matrix`, `higham9_15_strilPart`, `higham9_15_triuPart`, `higham9_15_frobNormRect_strilPart_le`, `higham9_15_frobNormRect_triuPart_le`, `higham9_15_abs_strilPart_le_strilPart_of_abs_le`, `higham9_15_abs_triuPart_le_triuPart_of_abs_le`, `higham9_15_strilPart_mono`, `higham9_15_triuPart_mono`, `higham9_15_abs_matrix_mul_le_abs_mul_abs`, `higham9_15_strilPart_add_strictLower_upper`, `higham9_15_triuPart_add_strictLower_upper`, `higham9_15_normalized_G_split_matrix`, `higham9_15_normalized_G_split_frobNorm_bounds`, `higham9_15_normalized_G_split_componentwise_majorants`, `higham9_15_normalized_G_split_frobNorm_step_bound`, `higham9_15_scalar_bound_of_le_add_mul`, `higham9_15_normalized_G_frobNorm_ratio_bound_of_linear_step`, `higham9_15_mul_le_eta_mul_max_of_min_le`, `higham9_15_normalized_G_frobNorm_ratio_bound_of_min_factor_bound`, `higham9_15_normalized_Gtilde_split_matrix`, `higham9_15_normalized_Gtilde_split_frobNorm_bounds`, `higham9_15_normalized_Gtilde_split_componentwise_majorants`, `higham9_15_normalized_Gtilde_split_frobNorm_step_bound`, `higham9_15_normalized_Gtilde_frobNorm_ratio_bound_of_min_factor_bound`, `higham9_15_frobenius_relative_lower_of_left_factor`, `higham9_15_frobenius_relative_upper_of_right_factor`, `higham9_15_frobenius_relative_assembly_bound`, `higham9_15_frobenius_relative_lower_of_left_factor_opNorm`, `higham9_15_frobenius_relative_upper_of_right_factor_opNorm`, `higham9_15_frobenius_relative_assembly_bound_opNorm`, `higham9_15_abs_rectMatMul_left_le`, `higham9_15_abs_rectMatMul_right_le`, `higham9_15_componentwise_original_assembly`, `higham9_15_deltaL_eq_L_mul_normalized_of_right_inverse`, `higham9_15_deltaU_eq_normalized_mul_U_of_left_inverse`, `higham9_15_opNorm2_pos_of_rectMatMul_right_inverse`, `higham9_15_opNorm2_pos_of_rectMatMul_left_inverse`, `higham9_15_frobenius_relative_assembly_of_inverse_normalized_bounds`, `higham9_15_frobenius_relative_assembly_of_inverse_normalized_bounds_opNorm`, `higham9_15_frobenius_relative_assembly_of_inverse_normalized_bounds_opNorm_of_inverse_identities`, `higham9_15_componentwise_original_assembly_of_inverse_normalized_bounds`, `higham9_15_normwise_source_bound_of_normalized_frobenius_bounds`, `higham9_15_normwise_source_bound_of_normalized_frobenius_bounds_opNorm`, `higham9_15_normwise_source_bound_of_normalized_frobenius_bounds_opNorm_of_inverse_identities`, `higham9_15_normwise_source_bound_of_G_split_min_factor_bound_opNorm_of_inverse_identities`, `higham9_15_normwise_source_bound_of_factorization_min_factor_bound_opNorm_of_matrix_inverse_identities`, `higham9_15_componentwise_source_bound_of_normalized_majorants`, `higham9_15_componentwise_source_bound_of_Gtilde_split_majorant_of_inverse_identities`, `higham9_15_componentwise_source_bound_of_factorization_Gtilde_majorant_of_matrix_inverse_identities` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Reused wrappers plus newly surfaced source-facing forward, condition-number/min-form, normalized algebra, split-equation/projection-bound, inverse-normalization, source-correct operator-denominator Frobenius/componentwise assembly with inverse-derived denominator positivity, scalar denominator handoff, and conditional endpoint wrappers | Componentwise algebra, the `2α + α^2` forward perturbation coefficient, the source `κ₂(A) <= χ(A) <= min{κ₂(L),κ₂(U)}κ₂(A)` consequence in both separate and min-form APIs, the exact normalized equations `I + G = (I + X)(I + Y)` and `I - Gtilde = (I - X)(I - Y)`, their strict-lower/upper split consequences plus Frobenius projection, componentwise projected-majorant, and one-step nonlinear bounds, the scalar `q <= g + eta*q` to `q <= g/(1-eta)` denominator step, the inverse-normalization identities for `ΔL` and `ΔU`, the auxiliary Frobenius-denominator and printed operator-denominator assembly steps, inverse-derived positive operator denominators on nonempty dimensions, and the conditional normwise/componentwise source endpoints from normalized bounds, the source factorization plus min-factor control, or the source `Gtilde` factorization plus supplied componentwise majorant are proved under explicit hypotheses; the full normwise/spectral theorem is not claimed. |

## Formalized End-To-End While Relying On Previous-Split Results

| Source label/name | Lean declaration(s) | File path | Previous split result/contract used | Reliance | Availability confirmation |
| --- | --- | --- | --- | --- | --- |
| Theorem 9.3 certificate form | `higham9_3_doolittle_backward_error`, `higham9_3_lu_backward_error_gamma` | `LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | Split 1, Chapter 3 `gamma`/roundoff algebra | Direct | The dependency is compiled repository infrastructure, not a free hypothesis. |
| Theorem 9.4 square certificate form | `higham9_4_lu_solve_backward_error` | same | Split 1, Chapter 3 `gamma`/roundoff algebra | Direct | Available and imported through LU solve modules. |
| Theorem 9.5 certificate/normwise form | `higham9_5_wilkinson_normwise_infNorm_tight`, `higham9_5_wilkinson_source_bound_of_growth_bridge`, `higham9_5_wilkinson_source_bound_of_entry_growth`, `higham9_5_wilkinson_source_bound_of_PartialPivotGEPPUTrace`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_denseLoop`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_absBudget`, `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_LUFactSpec`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_denseLoop`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_absBudget`, `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_LUFactSpec` | same | Split 1, Chapter 3 `gamma` infrastructure | Direct for gamma; local for growth and permutation bridges | Available; the max-entry-to-infinity bridge, explicit trace wrappers, and dense-loop/absolute-budget/exact pivoted certificate entry points are compiled. The concrete executable GEPP/GEPQ trace-to-certificate construction remains open. |
| Equation (9.9) nonnegative LU solve backward error | `higham9_9_nonneg_lu_solve_backward_error` | same | Split 1, Chapter 3 `gamma` infrastructure | Direct | Available and compiled. |
| Theorem 9.10 conditional upper-Hessenberg solve backward-error form | `higham9_10_hessenberg_lu_solve_backward_stable_tight` | same | Split 1, Chapter 3 `gamma` and triangular-solve infrastructure | Direct | Available and compiled; the theorem assumes only the explicit source growth inequality and does not assume or close the algorithmic Hessenberg growth trace. |
| Theorem 9.14 absorbed tridiagonal backward-error form | `higham9_14_tridiag_diagDom_fu_bound_tight` | same | Split 1, Chapter 3 `gamma` infrastructure | Direct | Available; source scalar `f(u)`/`h(u)` facts are closed separately, while the full source all-class backward-error theorem remains open. |
| Theorem 9.14 structural tridiagonal absorbed/source-model backward-error specialization | `higham9_14_tridiag_diagDom_fu_bound_from_structural_growth`, `higham9_14_tridiag_rowDiagDom_fu_bound_from_structural_growth`, `higham9_14_tridiag_colDiagDom_fu_bound_from_LUFactSpec`, `higham9_14_tridiag_rowDiagDom_fu_bound_from_LUFactSpec`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_LUFactSpec`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUFactSpec`, `LUFactSpec.to_LUBackwardError_zero`, `higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le`, `higham9_14_colDiagDom_exists_LUFactSpec_fu_bound`, `higham9_14_rowDiagDom_exists_LUFactSpec_fu_bound`, `higham9_14_colDiagDom_exists_LUFactSpec_source_f_bound_of_models`, `higham9_14_rowDiagDom_exists_LUFactSpec_source_f_bound_of_models`, `higham9_14_totalNonnegative_exists_source_f_bound_actual_triangular_solves`, `higham9_14_colDiagDom_exists_LUFactSpec_source_f_bound_actual_triangular_solves`, `higham9_14_rowDiagDom_exists_LUFactSpec_source_f_bound_actual_triangular_solves` | same | Split 1, Chapter 3 `gamma` infrastructure plus local Theorem 9.13 tridiagonal growth theorems and source equation (9.20)/(9.21) model predicates | Direct for gamma; local for growth and source-model aggregation | Available and compiled; no unresolved Split 1 theorem is assumed. The exact-LU wrappers reuse local Theorem 9.13 source-facing growth wrappers, and the existential variants choose the total-nonnegative, column-, or direct row-dominant factors from source data before exposing perturbation hypotheses. The source-model variants expose the `(9.20)`/`(9.21)` model hypotheses and conclude `f(u)|A|` or `3 f(u)|A|` for ordinary exact-LU and source-data exact-LU surfaces; the exact-factor/actual triangular-solve variants derive the LU model with zero coefficient and then use the real `fl_forwardSub`/`fl_backSub` path. Full all-class/source perturbation production remains recorded separately. |
| Theorem 9.14 source-data builder absorbed/source-model backward-error specialization | `higham9_14_tridiag_colDiagDom_fu_bound_from_builders`, `higham9_14_tridiag_rowDiagDom_fu_bound_from_builders`, `higham9_14_tridiag_colDiagDom_fu_bound_from_recurrence`, `higham9_14_tridiag_rowDiagDom_fu_bound_from_recurrence`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_builders`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence` | same | Split 1, Chapter 3 `gamma` infrastructure plus local Theorem 9.13 builder wrappers, exact-recurrence product theorem, and source equation (9.20)/(9.21) model predicates | Direct for gamma; local for builder growth and source-model aggregation | Available and compiled; the builder structure, recurrence-to-product, and growth chain are genuine Lean proofs, while perturbation certificates/models remain visible hypotheses. |

## Current Split 2 Proof/API Targets After Previous-Split Re-Audit

| Source label/name | Dependency | Integrated result/API family | Missing source-facing result | Reason not duplicated locally | Next theorem/interface target |
| --- | --- | --- | --- | --- | --- |
| Theorem 9.15 full normwise/spectral LU sensitivity | Direct | Integrated componentwise identity/relative/forward perturbation wrappers plus local `G` norm-product, `χ(A)` condition-number, normalized algebra/split, inverse-normalization, and source-correct operator-denominator Frobenius/componentwise assembly bridges | Barrlund/Sun Schur-induction and spectral-radius source theorem surfaces | Avoid duplicate norm/spectral API in Chapter 9 | Formalize the normalized Frobenius Schur-induction lemma and the nonnegative spectral-radius majorant lemma from the Oracle proof route. |
| Equation (9.27) full source statement | Direct | Integrated spectral-radius/Frobenius/norm infrastructure where available plus local `G` product/ratio, normalized-factorization/split, inverse-normalization, and source-correct operator-denominator Frobenius/componentwise assembly bridges | Spectral-radius and nonlinear normwise perturbation theorem | Local algebraic identity, componentwise forward wrapper, `G` norm-product and denominator-ratio bridges, `χ(A)` condition-number chain, normalized algebraic identities, split equations, inverse-normalization bridges, printed operator-denominator relative assembly, and componentwise original-variable assembly are closed; full bound needs the Barrlund/Sun Schur-induction/spectral wrapper | Spectral-radius and normwise perturbation bridge. |

## Open PROVE-NOW-SPLIT Rows

These rows do not have integrated Split 1 blockers and are not valid skips or
deferments. They remain current Split-2 work after this pass.

| Source label/name | Missing local result | Attempted or available route | Next Lean target |
| --- | --- | --- | --- |
| Algorithm 9.2 executable surface | Executable rectangular Doolittle/GE loop and concrete pivot-loop trace production | Square dense-loop certificates now bridge to `DoolittleLU` and Theorem 9.3; dense-loop and absolute-budget certificates on row-permuted `PA` and row-column-permuted `PAQ` now produce the pivoted/complete-pivoted backward-error certificate surfaces; exact rectangular identities (9.3)--(9.5), exact-LU recurrence converse, and the printed rational leading flop polynomial are recorded | Extend the dense-loop certificate pattern to a concrete rectangular algorithm trace and prove executable partial/complete pivoting loops produce the visible `PA`/`PAQ` dense-loop or backward-error certificates. |
| Theorems 9.5 and 9.7 and equations (9.10)--(9.13) | Computed GEPP certificate connection | Normwise, max-entry-to-infinity, Lemma 9.6 no-pivot source constant, Theorem 9.7 first-step partial-pivoting Schur-complement doubling, the explicit-stage recurrence to `2^(n-1)`, the arbitrary nonsingular recursive GEPP `U`-trace growth upper bound, the trace-level partial-pivoting growth-value family and supremum theorem, the displayed Wilkinson matrix exact LU/max-entry/growth witness, the selected real exact-arithmetic Theorem 9.7 upper-bound/attainability package, scaled active-stage no-pivot Schur-complement doubling and exact scaled LU/growth witness, row/complete-pivoted dense-loop, absolute-budget, and exact-certificate normwise wrappers, real max-entry witness bridges, unpermuted and complete-permuted exact-LU final-pivot identities, cumulative real complete-pivoting `PAQ = LU` certificate existence, real complete-pivoting existential `theta <= rho`, the recursive complete-pivoting `U` trace, the trace-level Problem 9.11 `g(2n)` lower-bound bridge, the explicit complex `PAQ = LU` certificate-level final-pivot bridge, the complex cumulative certificate construction, the complex recursive trace construction, the complex trace-to-certificate max-entry transfer, and the Fourier/Vandermonde trace-level `n <= rho` theorem now exist | Formalize the concrete computed GEPP/GEPQ trace-to-dense-loop/backward-error certificate construction needed by Theorem 9.5. The complex Fourier/Vandermonde trace-level growth row is now closed by `higham9_13_exists_fourierVandermonde_ComplexCompletePivotGECPUTrace_growth_ge_card`. |
| Theorems 9.10--9.11 and equations (9.14)--(9.16), with local Theorem 9.9 support separated | Direct growth proofs for banded, complete/rook pivoting; Theorem 9.10 exact nonsingular Hessenberg `U`-trace growth now closed | Conditional wrappers exist; Theorem 9.9's full row/column diagonal-dominance growth theorem is now classified as `DEFER-LATER-CHAPTER` through source-cited Theorems 13.7 and 13.8, while equation (9.17) is now closed separately via Chapter 8 Lemma 8.8 and the new exact-LU norm wrapper. Theorem 9.9 local support remains closed by the determinant-nonzero diagonal lemmas, off-diagonal and entry-ratio lemmas, column-dominant first-column multiplier-sum lemmas, first Schur-complement preservation/max-entry/off-diagonal/nonsingularity support, exact no-pivot LU existence/uniqueness with unit-bounded lower multipliers, transpose adapters, and the final scalar endpoint adapter. Theorem 9.10 is closed for the explicit nonsingular exact-arithmetic Hessenberg GEPP `U` trace by `higham9_10_HessenbergGEPPTrace_stage_pos`, `higham9_10_HessenbergGEPPUTrace`, `higham9_10_HessenbergGEPPUTrace_upper_zero`, `higham9_10_HessenbergGEPPUTrace_row_bound`, `higham9_10_exists_HessenbergGEPPUTrace_of_trace_det_ne_zero`, `higham9_10_exists_HessenbergGEPPUTrace_of_det_ne_zero`, `higham9_10_HessenbergGEPPUTrace_growthFactorEntry_le_card`, and `higham9_10_exists_HessenbergGEPPUTrace_growthFactorEntry_le_card_of_det_ne_zero`, building on the earlier first-step/stage-invariant/terminal-trace declarations. The recursive complete-pivoting `U` trace existence/upper-triangularity layer, cumulative real `PAQ = LU` certificate layer, elementary trace-level `rho <= 2^(n-1)` boundedness layer, trace-level nonempty/supremum endpoint, and Problem 9.11 trace-level `g(2n)` lower-bound theorem are closed, but Wilkinson's sharp complete-pivoting product upper-bound proof still needs the source entry-growth argument. The recursive rook-pivoting `U` trace existence/upper-triangularity layer and elementary trace-level `rho <= 2^(n-1)` boundedness/value-set/supremum layer are closed by `higham9_16_RookPivotGEUTrace`, `higham9_16_RookPivotGEUTrace_upper_zero`, `higham9_16_rookPivot_firstSchurComplement_entry_abs_le_two`, `higham9_16_rookPivot_firstSchurComplement_maxEntryNorm_le_two`, `higham9_16_RookPivotGEUTrace_entry_abs_le_pow_two`, `higham9_16_RookPivotGEUTrace_growthFactorEntry_le_pow_two`, `higham9_16_exists_RookPivotGEUTrace_of_det_ne_zero`, `higham9_16_exists_RookPivotGEUTrace_upper_zero_of_det_ne_zero`, and the `higham9_16_rookPivotingUTraceGrowth*` declarations, but Foster's sharper rook-pivoting product-bound theorem remains open. Theorem 9.11 Bohte scalar expression, `p = 1`/formal-expression `p = 2`/source-example `p = 4` arithmetic, nonnegativity, and conditional solve specialization remain recorded by `higham9_11_bohteBound`, `higham9_11_bohteBound_tridiagonal`, `higham9_11_bohteBound_pentadiagonal_formula`, `higham9_11_bohteBound_bandwidth_four_formula`, `higham9_11_bohteBound_nonneg`, and `higham9_11_bohte_banded_solve_tight`; the source proof of the full banded theorem is citation-only to Bohte [146, 1975], so that row is tracked as an external proof-source bottleneck. The equation (9.14)/(9.16) displayed scalar RHS definitions and scalar nonnegativity/positivity are recorded by `higham9_14_completePivotWilkinsonProduct`, `higham9_14_completePivotWilkinsonBound`, `higham9_14_completePivotWilkinsonProduct_nonneg`, `higham9_14_completePivotWilkinsonProduct_pos`, `higham9_14_completePivotWilkinsonBound_nonneg`, `higham9_14_completePivotWilkinsonBound_pos`, `higham9_16_rookPivotFosterBound`, `higham9_16_rookPivotFosterBound_nonneg`, and `higham9_16_rookPivotFosterBound_pos` | Prove the remaining banded full max-entry growth proof from an explicit proof-source route, prove Wilkinson's sharp complete-pivoting product upper-bound theorem for (9.14), and prove Foster's sharper rook-pivoting product-bound theorem for (9.16). |
| Theorems 9.12--9.14 and equations (9.20)--(9.22) | Full tridiagonal class coverage and production of the source perturbation models | Several tridiagonal wrappers, direct row-dominant and transposed row-dominant structural wrappers, the exact-`LUFactSpec` to bidiagonal structural handoff, column-dominant multiplier bound, ordinary exact-LU column- and row-dominant `rho <= 3` wrappers with `det A != 0`, the column-dominant existential exact-LU/growth package, the row-dominant transpose existential exact-LU/growth package for factors of `Aᵀ`, the transpose-LU rescaling bridge, the direct row-dominant existential exact-LU/growth package for factors of `A`, the total-nonnegative/nonsingular Theorem 9.12 exact-LU/optimal-growth/`rho <= 1` package, the structural tridiagonal growth-to-absorbed-bound specializations, the optimal-growth-to-`rho <= 1` max-entry consequence, the explicit `(9.20)`/`(9.21)` source model predicates, the exact `f(u)`/`h(u)` source scalars plus coefficient aggregation and model-consuming denominator-cleared source adapters, the constant-growth `c f(u)|A|` source-model bridge, the builder/recurrence, ordinary exact-LU, and source-data exact-LU column/direct-row diagonally-dominant `3 f(u)|A|` packages, the final `h(u)|A|` wrappers for SPD positive-`D L^T` including the source-data recurrence specialization, nonnegative-LU, M-matrix LU, sign-equivalent, and total-nonnegative/nonsingular optimal-growth surfaces, and the SPD positive-`D L^T` recurrence `f(u)|A|` actual triangular-solve wrappers exist | Close the remaining special-class algorithmic cases not covered by total nonnegativity or visible factor/certificate hypotheses, prove general source exact-LU existence hypotheses not already covered by explicit `LUFactSpec`/recurrence/direct row-dominant packages, prove the source `(9.20)`/`(9.21)` perturbation models from all rounded tridiagonal classes, and connect structural certificates to full executable traces. |

## Not Formalized For Another Reason

| Source label/name | Classification | Previous-split dependency status | Exact reason | Destination |
| --- | --- | --- | --- | --- |
| Theorem 9.9 full row/column diagonal-dominance growth theorem `rho_n <= 2` | DEFER-LATER-CHAPTER | No integrated previous-split blocker; later-chapter dependency | The source proof explicitly says the result follows from Theorems 13.7 and 13.8 for block diagonally dominant matrices. The current pass excludes Chapter 13/14 implementation and lookup artifacts, so Split 2 should not reprove those later foundations locally. Local side conditions, column-dominant no-pivot LU/multiplier support, and the scalar endpoint adapter remain closed. | Chapter 13, Theorems 13.7 and 13.8 |
| Algorithm 9.2 exact integer flop accounting | SKIP | No integrated previous-split blocker | The printed `n^2(m-n/3)` expression is a rational leading-cost polynomial, not an exact natural-number count for the literal loop; the source does not specify which loop operations are charged. The polynomial itself is recorded by `higham9_2_doolittleSourceFlopPolynomial`. | None |
| Section 9.12 rank-revealing LU prose | DEFER-LATER-SPLIT | Later deferred block also has Split-1 norm/SVD gates | Not assigned as a Split-2 primary/equation/problem theorem; belongs with later rank-revealing/SVD work | Later rank-revealing factorization split |
| Problems 9.15--9.18 | SKIP | No integrated previous-split blocker | Research/open-ended or empirical-search prompts, not determinate source theorems | None |
| Historical perspective, notes, references, LAPACK routine list | SKIP | No integrated previous-split blocker | Editorial, bibliographic, or software-descriptive material | None |
| Figures and empirical growth-factor observations | SKIP | No integrated previous-split blocker | Machine/experiment outputs without a fully specified computation | None |

## Hidden-Hypothesis and Modeling Audit

- The new Section 9.1 pivot predicates are source conditions, not stability
  certificates. The multiplier and active-entry ratio lemmas prove the
  immediate bounds from pivot maximality and a nonzero pivot denominator.
- The new Algorithm 9.2 dense-loop wrappers expose the residual-compression
  and absolute-budget dominance obligations as certificate fields. They only
  prove the handoff from those visible executable-loop certificates to
  `DoolittleLU`, Theorem 9.3's backward-error surface, and the row/complete
  pivoted `PA`/`PAQ` backward-error certificate surfaces; they do not count the
  full rectangular Algorithm 9.2 trace or a concrete pivot-loop trace as
  closed.
- The new exact-LU recurrence converse theorems decompose an existing
  `LUFactSpec` product using the unit-lower/upper-triangular zero structure.
  They prove that explicit exact factors satisfy the Doolittle upper and lower
  update formulas; they do not construct an LU certificate from leading
  principal determinant hypotheses.
- The new exact-LU uniqueness theorem uses those recurrence converse theorems
  column by column under explicit proper nonzero pivot hypotheses. It proves
  uniqueness between two supplied `LUFactSpec` certificates, and the separate
  first-Schur-complement induction proves existence from the proper
  leading-minor hypotheses.
- The new first Schur-complement LU construction step assumes only a nonzero
  first pivot and an explicit exact LU certificate for the first Schur
  complement. It constructs the full unit-lower/upper factors and proves the
  product entrywise; it does not assume that the Schur complement certificate
  follows from leading principal determinant hypotheses.
- The new permuted LU adapters expose the source `PA` and `PAQ` matrices and
  convert explicit `PA = LU`, `PAQ = LU`, or corresponding pivoted
  backward-error certificates into ordinary certificates on the permuted
  matrices. The dense-loop adapters now prove that a supplied Doolittle
  dense-loop or absolute-budget certificate on `PA`/`PAQ` gives those pivoted
  backward-error certificates. They do not assert that a concrete pivoting loop
  produced the dense-loop certificates.
- The new Theorem 9.5 bridge assumes a source max-entry growth-factor bound for
  the final `U_hat`; the explicit-trace specialization instead derives that
  growth factor from a proved `higham9_7_PartialPivotGEPPUTrace`. The new
  dense-loop and absolute-budget wrappers remove the free pivoted
  backward-error-certificate layer for `PA`/`PAQ`, but still require the visible
  dense-loop certificates and do not assume the concrete GEPP pivot
  loop/certificate connection or count the full Wilkinson GEPP growth theorem
  as closed.
- The new Problem 9.9 reduced-matrix bridge defines source `rho_n` over the
  exact equation (9.5) no-pivot reduced matrices and proves the printed bound
  directly from prefix-dot triangle inequalities. The separate final-`U`
  theorem remains available for exact `LUFactSpec` certificates.
- The new leading-principal determinant support for Theorem 9.1/Problems 9.1-9.2
  assumes an explicit full exact `LUFactSpec` and proves the leading block
  determinant/product consequences by restricting that certificate. The
  separate source-strength theorem proves existence/uniqueness iff Higham's
  proper leading principal minors are nonzero, and the Problem 9.1 converse
  uses an explicit lower-shear construction rather than a hidden uniqueness
  assumption.
- The final Problem 9.2 theorem does not assume an LU certificate for
  `sigma I - A`. It proves that avoiding the finite danger union gives the
  proper leading-principal determinant hypothesis, then applies the closed
  Theorem 9.1 source-strength LU existence/uniqueness criterion.
- The new Lemma 9.6 source-constant theorem proves the local stage algebra:
  full prefix equals `LU`, an exact LU certificate makes the terminal reduced
  residual zero, each rank-one term is bounded by neighboring reduced stages,
  the source endpoint/intermediate-stage count is exact, and the printed
  `1 + 2(n^2-n)rho_n` bound follows from the no-pivot reduced growth factor
  defined over equation (9.5) stages. The executable GE trace remains part of
  the separate Algorithm 9.2 row.
- The new Theorem 9.8 real max-entry lemmas assume only explicit finite matrices,
  positivity of max-entry norms where division is used, and the inverse-row or
  final-pivot witness hypotheses. They do not assume the target inequalities.
- The new Theorem 9.9 column-dominant first Schur-complement lemmas use only
  column diagonal dominance, a nonzero first pivot, finite-sum splitting,
  reverse-triangle algebra, and max-entry monotonicity; the exact-LU theorem
  adds only the Schur determinant identity and the existing exact no-pivot LU
  construction. The first-step max-entry theorem does not assert the full
  growth factor `rho_n <= 2`; the row-dominant equation (9.17) route is now
  closed separately by `higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec`.
- The new equation (9.13) Fourier/Vandermonde support records the source
  roots-of-unity matrix and proves symmetry, first row/column identities, the
  unit-circle entry norm, roots-of-unity cancellation, and full row/column Gram
  identities, then proves the explicit scaled-adjoint inverse formula
  `V_n^{-1} = n^{-1}V_nᴴ` as two finite-sum identities. It does not assume the
  growth lower bound.
- The new Problem 9.5 witness uses concrete `Fin 2` matrices and exact arithmetic.
  No theorem-equivalent assumption is introduced.
- The new Problem 9.6 source total-nonnegative support predicate records every
  square minor with strictly increasing row and column selections. The
  `1 by 1` and `2 by 2` adapters, determinant formula, local and general
  denominator-cleared first-pivot Schur determinant identities, selected `3 by 3`
  source-minor nonnegativity, first Schur-update `2 by 2` minor preservation,
  first-step all-minors total-nonnegativity preservation, positive-pivot
  multiplier nonnegativity, no-growth facts, trailing absolute-entry/max-entry
  no-growth, trailing-principal-block model, direct first-pivot and
  all-leading-principal-minor positivity from total nonnegativity plus
  `det A != 0`, recursive exact nonnegative LU construction from the source
  hypotheses, certificate-based final `rho <= 1` endpoint, reduced-matrix
  no-pivot `rho_n <= 1` endpoint, and
  order-two trailing-submatrix package are proved from those hypotheses and do
  not assume the cited total-positivity determinant inequality or pivot traces.
- The new Problem 9.7 count theorems reuse Mathlib binomial identities. The
  report records the source convention issue: with-empty Vandermonde gives
  `(2n choose n)`, while the nonempty problem wording gives `(2n choose n)-1`
  for square submatrices and `(2^n-1)^2` for rectangular submatrices.
- The new Problem 9.8 adapter assumes only an explicit `LUFactSpec` for
  `J A J` and explicit entrywise nonnegativity of the supplied `L,U` factors.
  It proves the printed `J` product algebra, `J^2=I`, checkerboard inverse
  transport, the cofactor-level entrywise checkerboard sign pattern for
  `nonsingInv` under total nonnegativity and nonsingularity, the empty-,
  `1 by 1`, codimension-one, full-determinant, and full-order inverse-minor wrappers,
  determinant scaling for all
  checkerboard-conjugated square minors, absolute-minor
  preservation, and `|JLJ||JUJ| = |A|`; it does not assume the
  missing Jacobi complementary-minor theorem needed to derive total
  nonnegativity of `J A J` from total nonnegativity of `A⁻¹`, nor the full
  total-nonnegative LU existence result.
- The new Problem 9.11 block theorems prove the displayed block inverse in both
  multiplication orders before proving the `alpha`, `beta`, and `theta`
  identities. The equation (9.12) sine matrix is defined with the source's
  one-based indices and proved symmetric; its entrywise/max-entry scale bounds,
  positive `(0,0)` entry, positive max-entry norm, finite cosine-sum parity
  support, unscaled sine orthogonality, scaled self-inverse certificate,
  theta lower-bound arithmetic, block-doubled sine theta bridge, flattened
  sine-block bounded-supremum witness bridge, and trace-level complete-pivoting
  `g(2n)` lower-bound theorem are also closed. The sharp Wilkinson product
  upper-bound theorem remains separate equation (9.14) work.
- The new Theorem 9.11 Bohte scalar declarations record only the printed scalar
  expression, prove its nonnegativity, prove the unambiguous tridiagonal `p =
  1` arithmetic case, record the formal-expression `p = 2` arithmetic value
  `7`, record the source `p = 4` example scalar value `116`, and specialize
  the existing conditional solve wrapper to that constant. They do not assert
  the banded GEPP growth theorem or attainability. The stale `GrowthFactor` docstring
  claiming a `p = 2` value of `5` was removed because it is not implied by the
  printed scalar expression.
- The new Theorem 9.12 SPD positive-`D L^T` declarations prove only the local
  algebraic equality step for a supplied tridiagonal bidiagonal LU certificate:
  `U = D L^T` with `D > 0` implies `|L||U| = |LU| = |A|`, hence `rho <= 1`
  and the generic SPD LU backward-error handoff. The builder and
  exact-recurrence variants remove only the `IsTridiagLU` and exact-product
  certificate layers for the explicit equation-(9.19) builders; they do not
  assert existence of the SPD `LDL^T`/LU certificate or the cited
  totally-nonnegative/M-matrix equivalence/existence results.
- The new Problem 9.13 theorems prove the threshold update algebra, the
  modification-count iteration, and the final max-entry growth-factor bound
  from explicit column-count hypotheses. They do not assume the target
  `rho_n` inequality as a certificate.
- The new Theorem 9.9/9.13 orientation adapters unfold the repository
  row/column dominance and tridiagonal predicates under `matTranspose`. They do
  not assume or close the diagonal-dominance or tridiagonal growth theorems.
- The new Theorem 9.13 row-dominant transpose wrapper constructs exact factors
  for `Aᵀ` from source data on a nonsingular row-dominant tridiagonal `A`; the
  direct existential wrapper then rescales those transposed pivots to construct
  unit-lower/upper exact LU factors for `A` itself. These are exact algebraic
  existence packages, not executable no-pivot trace constructions.
- The new Theorem 9.13 direct row-dominant structural wrapper assumes an explicit
  bidiagonal-LU certificate for `A` and proves the source-shaped structural
  componentwise and max-entry `rho <= 3` conclusions for `A` itself by deriving
  the needed `|U_i,i+1| <= |U_i,i|` recurrence from row diagonal dominance. It
  does not construct the executable no-pivot trace.
- The new Theorem 9.14 structural tridiagonal wrapper proves only the handoff
  from explicit bidiagonal-LU, exact-product, unit-bounded-lower,
  tridiagonal, and column- or row-diagonal-dominance hypotheses to the absorbed
  `3 gamma_6` bound. The newer existential variants choose column- or direct
  row-dominant exact LU factors from source data, but still expose the
  rounded factorization/triangular-solve perturbation hypotheses explicitly.
  They do not close the all-class source theorem or the printed `h(u)` theorem
  by themselves.
- The new Theorem 9.15 `χ(A)` declarations expose the needed inverse-product
  information as either operator-2 certificates or exact matrix-product
  identities. They prove the displayed condition-number chain from
  submultiplicativity and do not assert the Barrlund--Sun nonlinear
  perturbation theorem or its spectral-radius side condition.
- The new Theorem 9.15 normalized matrix identities expose the exact inverse
  orientations they need: left inverse for the lower factor and right inverse
  for the upper factor in the `I+G` identity, with the analogous hatted
  inverse hypotheses for `I-Gtilde`. They are algebraic reductions to the
  normalized Barrlund--Sun lemmas, not the Frobenius or spectral-radius
  induction arguments themselves.
- The new Theorem 9.15 split-equation declarations introduce local `stril` and
  `triu` projections only for the normalized Barrlund--Sun equations. The
  strict-lower and upper-triangular hypotheses are explicit inputs, so the
  projections do not hide the LU normalization requirements.
- The new Theorem 9.15 Frobenius projection bounds prove only that local
  `stril`/`triu` projections are norm-nonincreasing and that the normalized
  split equations therefore bound `||X||_F` and `||Y||_F` by the residual split
  matrices. The one-step nonlinear bounds add only triangle inequality and
  Frobenius submultiplicativity. They do not prove the Schur-induction
  estimate that controls `||X||_F` and `||Y||_F` by `||G||_F/(1-||G||_2)`.
  The scalar denominator lemma closes only the final algebra after a
  linearized step inequality has already been supplied.
- The new Frobenius relative assembly declarations assume explicit product
  identities `ΔL = L X` and `ΔU = Y U`. The older auxiliary wrappers use
  positive Frobenius denominators, while the source-correct printed wrappers
  use positive operator-2 denominators for `L` and `U`. They prove only the
  final submultiplicativity/division handoff from normalized `X,Y` bounds, not
  the missing normalized Schur-induction bound.
- The new componentwise assembly declarations assume explicit product
  identities `ΔL = Lhat X` and `ΔU = Y Uhat` plus entrywise envelopes for the
  normalized perturbations. They prove only the entrywise absolute-product
  handoff to `|Lhat| B_L` and `B_U |Uhat|`, not the missing spectral-radius
  majorant that supplies those envelopes.
- The new inverse-normalization wrappers expose the opposite inverse
  orientations needed to derive `ΔL = L(L^{-1}ΔL)` and
  `ΔU = (ΔU U^{-1})U`. They do not infer inverse existence; callers still
  provide the corresponding exact inverse identities. On a nonempty dimension,
  the printed-denominator variants derive the positive `||L||_2` and
  `||U||_2` denominator facts from those identities.
- The new equation (9.27) ratio wrapper assumes the product operator bound is
  strictly below one and exposes all nonnegativity hypotheses for the product
  constants. It only converts compiled `G` product bounds into a denominator
  ratio; it does not prove the normalized Barrlund--Sun theorem that consumes
  that ratio.
- The new printed-denominator conditional normwise source wrapper assumes the
  normalized Frobenius bounds for `L^{-1}ΔL` and `ΔU U^{-1}` explicitly. It
  proves that those normalized bounds imply the source relative right-hand
  side with denominators `||L||_2` and `||U||_2`, thereby isolating the
  remaining missing normwise work to the normalized Schur induction.
- The new conditional componentwise source wrapper assumes normalized
  strict-lower/upper majorants explicitly. It proves that those majorants imply
  the source componentwise envelopes, isolating the remaining componentwise
  work to the nonnegative spectral-radius majorant theorem.
- No orphan typeclass hypotheses were introduced by the new declarations.
- No vacuous definitions were introduced; the new definitions model the source
  Section 9.1 first-stage pivot choices, the source matrices `A`, `L`, and
  `U` for Problem 9.5, Algorithm 9.2's printed leading-cost polynomial, the
  Theorem 9.10 Hessenberg stage invariant, explicit active-matrix trace
  interface, and exposed upper-factor `U` trace interface, the
  Problem 9.6 trailing principal block, the
  Theorem 9.14 source scalar polynomial `f(u)`, the block matrix `B` from
  Problem 9.11, the flattened two-block matrix surface for Problem 9.11, the
  source equation (9.12) sine matrix, the source equation
  (9.13) Fourier/Vandermonde matrix, its scaled adjoint `n^{-1}V_nᴴ`, and the
  threshold-pivoting factor from Problem 9.13. The equation (9.20)/(9.21)
  declarations are explicit source model predicates; they do not assert that
  every rounded tridiagonal recurrence has produced those perturbations. The
  Theorem 9.14 aggregation and denominator-clearing theorems are proof wrappers
  over `lu_solve_backward_error_mixed` and ordered-field algebra. The new
  optimal-growth final-bound wrappers consume either `|Lhat||Uhat| <= |A|` or
  existing SPD/nonnegative/M-matrix/sign-equivalent/total-nonnegative
  optimal-growth theorems plus the explicit (9.20)/(9.21) source models; they
  do not derive the rounded perturbation models themselves. The structural
  wrapper is a proof handoff from the local tridiagonal growth theorem, not a
  theorem-equivalent assumption, and the Theorem 9.11 definition records the
  source scalar expression rather than a hidden banded-growth certificate.

## Verification

Commands run:

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 normalized-linear-step source wrapper |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the normalized-linear-step source wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_linear_step_source_bridge.out 2>&1` | PASS after adding the lookup check for `higham9_15_normwise_source_bound_of_normalized_linear_step_opNorm_of_inverse_identities` |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_normwise_source_bound_of_normalized_linear_step_opNorm_of_inverse_identities` | PASS; the audited declaration reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the normalized-linear-step source wrapper update; no implementation or lookup matches |
| `rg -n "TODO\|FIXME\|False\\.elim\|by\\s+sorry\|by\\s+admit" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the normalized-linear-step source wrapper update; no local placeholder matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the normalized-linear-step source wrapper update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the normalized-linear-step source wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding one-sided inverse variants of the Theorem 9.15 factorization-level source wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the one-sided inverse source wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_one_sided_inverse_bridges.out 2>&1` | PASS after adding lookup checks for the inverse-side adapters and one-sided source wrappers |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_matrix_right_inverse_of_matrix_left_inverse`, `higham9_15_matrix_left_inverse_of_matrix_right_inverse`, `higham9_15_normwise_source_bound_of_factorization_min_factor_bound_opNorm`, and `higham9_15_componentwise_source_bound_of_factorization_Gtilde_majorant` | PASS; all four audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the one-sided inverse source wrapper update; no implementation or lookup matches |
| `rg -n "TODO\|FIXME\|False\\.elim\|by\\s+sorry\|by\\s+admit" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the one-sided inverse source wrapper update; no local placeholder matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the one-sided inverse source wrapper update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the one-sided inverse source wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 factorization-level normwise/componentwise source wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the factorization-level source wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_factorization_source_bridges.out 2>&1` | PASS after adding lookup checks for the two factorization-level source wrappers |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_normwise_source_bound_of_factorization_min_factor_bound_opNorm_of_matrix_inverse_identities` and `higham9_15_componentwise_source_bound_of_factorization_Gtilde_majorant_of_matrix_inverse_identities` | PASS; both audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the factorization-level source wrapper update; no implementation or lookup matches |
| `rg -n "TODO\|FIXME\|False\\.elim\|by\\s+sorry\|by\\s+admit" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the factorization-level source wrapper update; no local placeholder matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the factorization-level source wrapper update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the factorization-level source wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding Theorem 9.15 projection monotonicity and the `Gtilde` split-majorant componentwise source bridge |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the componentwise source bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_componentwise_source_bridge.out 2>&1` | PASS after adding lookup checks for the projection monotonicity helpers and `higham9_15_componentwise_source_bound_of_Gtilde_split_majorant_of_inverse_identities` |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_strilPart_mono`, `higham9_15_triuPart_mono`, and `higham9_15_componentwise_source_bound_of_Gtilde_split_majorant_of_inverse_identities` | PASS; all three audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the componentwise source bridge update; no implementation or lookup matches |
| `rg -n "TODO\|FIXME\|False\\.elim\|by\\s+sorry\|by\\s+admit" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the componentwise source bridge update; no local placeholder matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the componentwise source bridge update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the componentwise source bridge code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 normalized split plus min-factor source-bound bridge |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the min-factor source-bound bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_min_factor_source_bridge.out 2>&1` | PASS after adding the lookup check for `higham9_15_normwise_source_bound_of_G_split_min_factor_bound_opNorm_of_inverse_identities` |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_normwise_source_bound_of_G_split_min_factor_bound_opNorm_of_inverse_identities` | PASS; the audited declaration reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the min-factor source-bound bridge update; no implementation or lookup matches |
| `rg -n "TODO\|FIXME\|False\\.elim\|by\\s+sorry\|by\\s+admit" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the min-factor source-bound bridge update; no local placeholder matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the min-factor source-bound bridge update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the min-factor source-bound bridge code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding Theorem 9.15 componentwise projected majorants and conditional min-factor ratio bridges |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the componentwise majorant update |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_componentwise_majorants.out 2>&1` | PASS after rebuilding Chapter 9 and adding lookup checks for the componentwise majorant and min-factor ratio declarations |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_abs_strilPart_le_strilPart_of_abs_le`, `higham9_15_abs_triuPart_le_triuPart_of_abs_le`, `higham9_15_abs_matrix_mul_le_abs_mul_abs`, `higham9_15_normalized_G_split_componentwise_majorants`, `higham9_15_mul_le_eta_mul_max_of_min_le`, `higham9_15_normalized_G_frobNorm_ratio_bound_of_min_factor_bound`, `higham9_15_normalized_Gtilde_split_componentwise_majorants`, and `higham9_15_normalized_Gtilde_frobNorm_ratio_bound_of_min_factor_bound` | PASS; all eight audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the componentwise majorant update; no implementation or lookup matches |
| `rg -n "TODO\|FIXME\|False\\.elim\|by\\s+sorry\|by\\s+admit" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the componentwise majorant update; no local placeholder matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the componentwise majorant update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the componentwise majorant code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 scalar denominator handoff for a future linearized normwise step |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the scalar handoff update |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_scalar_handoff.out 2>&1` | PASS after adding lookup checks for the scalar handoff declarations |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_scalar_bound_of_le_add_mul` and `higham9_15_normalized_G_frobNorm_ratio_bound_of_linear_step` | PASS; both audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the scalar handoff update; no implementation or lookup matches |
| `rg -n "TODO\|FIXME\|False\\.elim\|by\\s+sorry\|by\\s+admit" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the scalar handoff update; no local placeholder matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the scalar handoff update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the scalar handoff code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding Theorem 9.15 one-step Frobenius nonlinear bounds for the normalized split equations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the step-bound update |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_step_bounds.out 2>&1` | PASS after adding lookup checks for the step-bound declarations |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_normalized_G_split_frobNorm_step_bound` and `higham9_15_normalized_Gtilde_split_frobNorm_step_bound` | PASS; both audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the step-bound update; no implementation or lookup matches |
| `rg -n "TODO\|FIXME\|False\\.elim\|by\\s+sorry\|by\\s+admit" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the step-bound update; no local placeholder matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the step-bound update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the step-bound code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding Theorem 9.15 Frobenius projection bounds for the normalized split equations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the projection-bound update |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_projection_bounds.out 2>&1` | PASS after adding lookup checks for the projection-bound declarations |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_frobNormRect_strilPart_le`, `higham9_15_frobNormRect_triuPart_le`, `higham9_15_normalized_G_split_frobNorm_bounds`, and `higham9_15_normalized_Gtilde_split_frobNorm_bounds` | PASS; all four audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the projection-bound update; no implementation or lookup matches |
| `rg -n "TODO\|FIXME\|False\\.elim\|by\\s+sorry\|by\\s+admit" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the projection-bound update; no local placeholder matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the projection-bound update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the projection-bound code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding inverse-derived positive operator-denominator wrappers for Theorem 9.15 |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the inverse-derived denominator update |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_opnorm_inverse.out 2>&1` | PASS after adding lookup checks for the inverse-derived denominator declarations |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_opNorm2_pos_of_rectMatMul_right_inverse`, `higham9_15_opNorm2_pos_of_rectMatMul_left_inverse`, `higham9_15_frobenius_relative_assembly_of_inverse_normalized_bounds_opNorm_of_inverse_identities`, and `higham9_15_normwise_source_bound_of_normalized_frobenius_bounds_opNorm_of_inverse_identities` | PASS; all four audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the inverse-derived denominator update; no implementation or lookup matches |
| `rg -n "TODO\|FIXME\|False\\.elim\|by\\s+sorry\|by\\s+admit" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the inverse-derived denominator update; no local placeholder matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the inverse-derived denominator update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the inverse-derived denominator code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the source-correct Theorem 9.15 operator-denominator assembly and normwise wrapper |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the operator-denominator Theorem 9.15 update |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the operator-denominator Theorem 9.15 declarations |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_frobenius_relative_assembly_bound_opNorm`, `higham9_15_frobenius_relative_assembly_of_inverse_normalized_bounds_opNorm`, and `higham9_15_normwise_source_bound_of_normalized_frobenius_bounds_opNorm` | PASS; all three audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the operator-denominator Theorem 9.15 update; no implementation or lookup matches |
| `rg -n "TODO\|FIXME\|False\\.elim\|by\\s+sorry\|by\\s+admit" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the operator-denominator Theorem 9.15 update; no local placeholder matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the operator-denominator Theorem 9.15 update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the operator-denominator Theorem 9.15 code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the conditional Theorem 9.15 componentwise source-bound wrapper |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the conditional componentwise wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_chi.out 2>&1` | PASS after adding lookup checks for the conditional componentwise wrapper |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_componentwise_source_bound_of_normalized_majorants` | PASS; the audited declaration reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the conditional componentwise wrapper update; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the conditional componentwise wrapper update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the conditional componentwise wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the conditional Theorem 9.15 normwise source-bound wrapper |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the conditional normwise wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_chi.out 2>&1` | PASS after adding lookup checks for the conditional normwise wrapper |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_normwise_source_bound_of_normalized_frobenius_bounds` | PASS; the audited declaration reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the conditional normwise wrapper update; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the conditional normwise wrapper update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the conditional normwise wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the equation (9.27) `G` denominator-ratio bridge |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the `G` ratio update |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_chi.out 2>&1` | PASS after adding lookup checks for the `G` ratio declarations |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_27_GMatrix_ratio_le_product_ratio` | PASS; the audited declaration reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the `G` ratio update; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the `G` ratio update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the `G` ratio code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 inverse-normalized assembly wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the inverse-normalization update |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_chi.out 2>&1` | PASS after adding lookup checks for the inverse-normalized assembly wrappers |
| `lake env lean --stdin` with fully qualified `#print axioms` for the inverse-normalized Frobenius and componentwise assembly wrappers | PASS; both audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the inverse-normalization update; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the inverse-normalization update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the inverse-normalization code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 componentwise original-variable assembly declarations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the componentwise assembly update |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_chi.out 2>&1` | PASS after adding lookup checks for the componentwise assembly declarations |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_componentwise_original_assembly` | PASS; the audited declaration reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the componentwise assembly update; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the componentwise assembly update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the componentwise assembly code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 Frobenius relative assembly declarations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the Frobenius assembly update |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_chi.out 2>&1` | PASS after adding lookup checks for the Frobenius assembly declarations |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_frobenius_relative_assembly_bound` | PASS; the audited declaration reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the Frobenius assembly update; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the Frobenius assembly update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Frobenius assembly code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 `stril`/`triu` projections and normalized split equations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the split-equation update |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_chi.out 2>&1` | PASS after adding lookup checks for the Theorem 9.15 projection/split declarations |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_normalized_G_split_matrix` and `higham9_15_normalized_Gtilde_split_matrix` | PASS; both audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the Theorem 9.15 split-equation update; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the Theorem 9.15 split-equation update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.15 split-equation code/lookup/report update |
| `oracle --engine browser --model gpt-5.5-pro --file /tmp/higham_ch9_15_oracle_packet.md` | PASS; returned a math-only proof route for the Barrlund--Sun Frobenius Schur-induction and spectral-radius majorant lemmas |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 normalized `I+G` and `I-Gtilde` algebraic identities |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the normalized identities |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_chi.out 2>&1` | PASS after adding lookup checks for the normalized Theorem 9.15 identities |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_normalized_G_factorization_matrix` and `higham9_15_normalized_Gtilde_factorization_matrix` | PASS; both audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the normalized Theorem 9.15 identity update; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the normalized Theorem 9.15 identity update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the normalized Theorem 9.15 identity code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 `χ(A)` condition-number chain |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the `χ(A)` condition-number chain |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_chi.out 2>&1` | PASS after adding lookup checks for the Theorem 9.15 `χ(A)` declarations |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_chi_condition_chain_of_inverse_product_bounds` and `higham9_15_chi_condition_chain_of_inverse_products` | PASS; both audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the Theorem 9.15 `χ(A)` update; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the Theorem 9.15 `χ(A)` update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.15 `χ(A)` code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the total-nonnegative Theorem 9.14 model-consuming existential final-bound package |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the total-nonnegative Theorem 9.14 package |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_14_totalNonnegative_exists_source_h_bound_of_models` | PASS; the audited declaration reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the total-nonnegative Theorem 9.14 package; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the total-nonnegative Theorem 9.14 package; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the total-nonnegative Theorem 9.14 package code/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the sign-equivalent Theorem 9.14 model-consuming final-bound wrapper |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the sign-equivalent Theorem 9.14 wrapper |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_14_sign_equiv_source_h_bound_of_models` | PASS; the audited declaration reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the sign-equivalent Theorem 9.14 wrapper; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the sign-equivalent Theorem 9.14 wrapper; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the sign-equivalent Theorem 9.14 wrapper code/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.14 optimal-growth model bridge and SPD/nonnegative/M-matrix final-bound wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the Theorem 9.14 optimal-growth model bridge |
| `lake env lean --stdin` with fully qualified `#print axioms` for the generic optimal-growth bridge and three special-class Theorem 9.14 final-bound wrappers | PASS; all four audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the Theorem 9.14 optimal-growth model bridge; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the Theorem 9.14 optimal-growth model bridge; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.14 optimal-growth model bridge code/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the model-consuming Theorem 9.14 `h(u)` final-bound wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the model-consuming Theorem 9.14 `h(u)` wrappers |
| `lake env lean --stdin` with fully qualified `#print axioms` for the two model-consuming Theorem 9.14 `h(u)` wrappers | PASS; both audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the model-consuming Theorem 9.14 `h(u)` wrappers; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the model-consuming Theorem 9.14 `h(u)` wrappers; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the model-consuming Theorem 9.14 `h(u)` wrapper code/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the equation (9.20)/(9.21) source model predicates and the model-to-(9.22) aggregation wrapper |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the equation (9.20)/(9.21) source model update |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_22_source_f_bound_of_9_20_9_21_models` | PASS; the audited declaration reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the equation (9.20)/(9.21) source model update; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the equation (9.20)/(9.21) source model update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the equation (9.20)/(9.21) source model code/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 componentwise forward perturbation wrapper |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the Theorem 9.15 componentwise forward wrapper |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_15_lu_perturbation_forward_bound` | PASS; the audited declaration reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the Theorem 9.15 componentwise forward wrapper; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the Theorem 9.15 componentwise forward wrapper; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.15 componentwise forward wrapper code/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the row/complete-pivoted dense-loop and absolute-budget certificate bridges |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the pivoted dense-loop bridge update |
| `lake env lean --stdin` with fully qualified `#print axioms` for the four pivoted certificate adapters and four Theorem 9.5 dense-loop/absolute-budget wrappers | PASS; all eight audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the pivoted dense-loop bridge update; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the pivoted dense-loop bridge update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the pivoted dense-loop bridge code/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the equation (9.23) exact denominator and `FirstOrderLe` condition-product wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for equation (9.23) |
| `lake env lean --stdin` with fully qualified `#print axioms` for the four equation (9.23) declarations plus the latest Problem 9.3/(9.26)/(9.27) support declarations | PASS; all audited declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the equation (9.23) update; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the equation (9.23) update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the equation (9.23) code/report update |
| `lake build` | PASS, 3511 jobs, after the equation (9.23) update; warnings only in pre-existing QR/GivensSpec and FastMatMul modules |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Problem 9.3 field-of-values route, equation (9.26) Holder wrapper, and equation (9.27) `G` norm-product support |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the compiled Chapter 9 artifact for the Problem 9.3/(9.26)/(9.27) support |
| `lake env lean --stdin` with fully qualified `#print axioms` for the new Problem 9.3, equation (9.26), and equation (9.27) support declarations | PASS; all six final-facing declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the Problem 9.3/(9.26)/(9.27) update; no implementation matches |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the Problem 9.3/(9.26)/(9.27) update; no temporary axiom or probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Problem 9.3/(9.26)/(9.27) code/report update |
| `lake build` | PASS, 3511 jobs, after the Problem 9.3/(9.26)/(9.27) update; warnings only in pre-existing QR/GivensSpec and FastMatMul modules |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.TridiagonalRecurrence` | PASS, 2981 jobs, after adding `tridiag_spd_shape_absLU_eq_absA` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.12 SPD positive-`D L^T` wrappers and their builder/exact-recurrence variants |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_9_12_spd_builders.out 2>&1` | PASS after adding lookup checks for the SPD positive-`D L^T` builder declarations; redirected output has 72357 lines |
| `lake env lean --stdin` with `#print axioms` for the generic, source-facing, builder, and exact-recurrence Theorem 9.12 SPD positive-`D L^T` declarations | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Theorem 9.12 SPD positive-`D L^T` builder update; implementation/lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Theorem 9.12 SPD positive-`D L^T` builder code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.12 SPD positive-`D L^T` builder update; only pre-existing QR/FastMatMul warnings |
| `lake env lean LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean` | PASS after adding `tridiag_prevIndex`, `TridiagExactLURecurrence`, and `tridiag_exact_product_of_recurrence` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equation (9.19) exact recurrence-to-product theorem and Theorem 9.13/9.14 exact-recurrence builder wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the exact recurrence-to-product theorem and recurrence-based tridiagonal wrappers; output was large but the process exited successfully |
| `lake env lean --stdin` with `#print axioms` for `tridiag_exact_product_of_recurrence`, `higham9_19_tridiag_exact_product_of_recurrence`, the four Theorem 9.13 recurrence builder wrappers, and the two Theorem 9.14 recurrence builder wrappers | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the equation (9.19) recurrence-to-product update; implementation/lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the equation (9.19) recurrence-to-product code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the equation (9.19) recurrence-to-product update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.10 first-pivot nonsingularity and Schur-determinant inheritance support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Theorem 9.10 first-pivot nonsingularity declarations; output was large but the process exited successfully |
| `lake env lean --stdin` with `#print axioms` for `higham9_7_firstPivotRowSwap_involutive`, `higham9_7_firstPivotRowSwap_isPermutation`, `higham9_7_firstPivotRowSwap_det_ne_zero`, `higham9_10_exists_first_active_column_nonzero_of_det_ne_zero`, `higham9_10_exists_first_partialPivotChoice_pivot_ne_zero_of_det_ne_zero`, and `higham9_10_firstSchurComplement_det_ne_zero_of_det_ne_zero` | PASS; the two row-swap function/permutation lemmas report only `propext`, and the determinant/first-pivot/Schur-complement declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14 scans | PASS after the Theorem 9.10 first-pivot nonsingularity update; no matches |
| `git diff --check` | PASS after the Theorem 9.10 first-pivot nonsingularity code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.10 first-pivot nonsingularity update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.8 / equation (9.13) complex growth bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_complex_growth.out 2>&1` | PASS after adding lookup checks for the complex growth bridge declarations; redirected output has 71593 lines |
| `lake env lean TmpCh9ComplexGrowthAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_8_complexGrowthFactorEntry_ge_inverse_entry_theta` and `higham9_13_fourierVandermonde_complexGrowthFactorEntry_ge_card` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the complex growth bridge update; no matches |
| `rg -n "TODO\|FIXME\|placeholder\|by\s+exact\s+False\.elim\|False\.elim\|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the complex growth bridge update; no matches |
| `rg -n "HighamChapter13\|HighamChapter14\|chapter13\|chapter14\|Chapter 13\|Chapter 14\|ch13\|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the complex growth bridge update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after cleanup; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the complex growth bridge update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the complex growth bridge update; only pre-existing QR/FastMatMul warnings |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_complex_certificate_bridge.out 2>&1` | PASS after adding lookup checks for the Theorem 9.8 / equation (9.13) complex certificate bridge declarations; redirected output has 72943 lines |
| `lake env lean --stdin` with `#print axioms` for the fourteen complex certificate bridge declarations | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the complex certificate bridge update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files |
| implementation/lookup Chapter 13-14 added-line scan | PASS after the complex certificate bridge update; no Chapter 13/14 implementation or lookup artifacts were added |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.8 / equation (9.13) complex complete-pivoting trace/certificate construction |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_complex_trace_certificate.out 2>&1` | PASS after adding lookup checks for the complex trace/certificate construction declarations; redirected output has 72997 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for nine final-facing complex first-step, certificate-existence, Fourier/Vandermonde certificate-growth, and trace-existence declarations | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the complex trace/certificate construction update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files |
| implementation/lookup Chapter 13-14 added-line scan | PASS after the complex trace/certificate construction update; no Chapter 13/14 implementation or lookup artifacts were added |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the complex trace-to-certificate max-entry transfer and trace-level Fourier/Vandermonde theorem |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_complex_trace_transfer.out 2>&1` | PASS after adding lookup checks for the complex trace-transfer declarations; redirected output has 73019 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the three complex max-entry helper declarations and three final-facing complex trace-transfer/Fourier trace-level declarations | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the complex trace-transfer update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files |
| implementation/lookup Chapter 13-14 added-line scan | PASS after the complex trace-transfer update; no Chapter 13/14 implementation or lookup artifacts were added |
| `rg -n "[ \t]+$" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md /home/mymel/flare-bundle/dev-logs/2026-06-22-chapter9-wilkinson-witness.md /home/mymel/flare-bundle/dev-logs/CURRENT.md` | PASS after the complex trace-transfer code/lookup/report/log update; no trailing whitespace matches |
| `git diff --check` | PASS after the complex trace-transfer code/lookup/report/log update |
| `rg -n "[ \t]+$" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md` | PASS after the complex certificate bridge report update; no trailing whitespace matches |
| `git diff --check` | PASS after the complex certificate bridge code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Section 9.1 first-stage nonzero pivot and ratio-bound packages |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_pivot_stage_package.out 2>&1` | PASS after adding lookup checks for the first-stage pivot package declarations; redirected output has 71578 lines |
| `lake env lean TmpCh9PivotStagePackageAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_1_exists_partialPivot_nonzero_and_multiplier_bound`, `higham9_1_exists_completePivot_nonzero_and_ratio_bounds`, and `higham9_1_exists_rookPivot_nonzero_and_ratio_bounds` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the first-stage pivot package update; no matches |
| `rg -n "TODO\|FIXME\|placeholder\|by\s+exact\s+False\.elim\|False\.elim\|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the first-stage pivot package update; no matches |
| `rg -n "HighamChapter13\|HighamChapter14\|chapter13\|chapter14\|Chapter 13\|Chapter 14\|ch13\|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the first-stage pivot package update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after cleanup; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the first-stage pivot package update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the first-stage pivot package update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Section 9.1 selected-pivot nonzero support lemmas |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_pivot_nonzero.out 2>&1` | PASS after adding lookup checks for the selected-pivot nonzero declarations; redirected output has 71561 lines |
| `lake env lean TmpCh9PivotNonzeroAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_1_partialPivotChoice_pivot_ne_zero_of_exists`, `higham9_1_completePivotChoice_pivot_ne_zero_of_exists`, `higham9_1_exists_partialPivotChoice_pivot_ne_zero`, and `higham9_1_exists_completePivotChoice_pivot_ne_zero` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the selected-pivot nonzero update; no matches |
| `rg -n "TODO\|FIXME\|placeholder\|by\s+exact\s+False\.elim\|False\.elim\|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the selected-pivot nonzero update; no matches |
| `rg -n "HighamChapter13\|HighamChapter14\|chapter13\|chapter14\|Chapter 13\|Chapter 14\|ch13\|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the selected-pivot nonzero update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after cleanup; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the selected-pivot nonzero update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the selected-pivot nonzero update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Section 9.1 finite active-set pivot-choice existence lemmas |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_pivot_choice_existence.out 2>&1` | PASS after adding lookup checks for the pivot-choice existence declarations; redirected output has 71550 lines |
| `lake env lean TmpCh9PivotChoiceAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_1_exists_partialPivotChoice`, `higham9_1_exists_completePivotChoice`, `higham9_1_rookPivotChoice_of_completePivotChoice`, and `higham9_1_exists_rookPivotChoice` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the pivot-choice existence update; no matches |
| `rg -n "TODO\|FIXME\|placeholder\|by\s+exact\s+False\.elim\|False\.elim\|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the pivot-choice existence update; no matches |
| `rg -n "HighamChapter13\|HighamChapter14\|chapter13\|chapter14\|Chapter 13\|Chapter 14\|ch13\|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the pivot-choice existence update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after cleanup; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the pivot-choice existence update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the pivot-choice existence update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.13/9.14 source-data tridiagonal builder wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_tridiag_builders.out 2>&1` | PASS after adding lookup checks for the tridiagonal builder declarations; redirected output has 71542 lines |
| `lake env lean TmpCh9TridiagBuilderAxioms.lean` | PASS before removing the temporary axiom-check file; `tridiag_matrices_isTridiagLU`, `tridiag_L_matrix_entries_bounded`, `higham9_13_tridiag_builder_growth_bound_3`, `higham9_13_tridiag_builder_growthFactorEntry_le_three`, `higham9_13_rowDiagDom_tridiag_builder_growth_bound_3`, `higham9_13_rowDiagDom_tridiag_builder_growthFactorEntry_le_three`, `higham9_14_tridiag_colDiagDom_fu_bound_from_builders`, and `higham9_14_tridiag_rowDiagDom_fu_bound_from_builders` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the tridiagonal builder wrapper update; no matches |
| `rg -n "TODO\|FIXME\|placeholder\|by\s+exact\s+False\.elim\|False\.elim\|Classical\.choice" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the tridiagonal builder wrapper update; no matches |
| `rg -n "HighamChapter13\|HighamChapter14\|chapter13\|chapter14\|Chapter 13\|Chapter 14\|ch13\|ch14" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the tridiagonal builder wrapper update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after cleanup; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the tridiagonal builder wrapper update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the tridiagonal builder wrapper update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_11_sine_block_theta_candidate_ge_succ` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the lookup check for `higham9_11_sine_block_theta_candidate_ge_succ` |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the block-doubled sine candidate theta bridge and report/log updates; warnings only in pre-existing QR/FastMatMul files |
| `lake env lean TmpCh9SineBlockAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_11_sine_block_theta_candidate_ge_succ` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the block-doubled sine candidate theta bridge; no matches |
| `rg -n "TODO\|FIXME\|placeholder\|by\s+exact\s+False\.elim\|False\.elim\|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the block-doubled sine candidate theta bridge; no matches |
| `rg -n "HighamChapter13\|HighamChapter14\|chapter13\|chapter14\|Chapter 13\|Chapter 14\|ch13\|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the block-doubled sine candidate theta bridge; no implementation/lookup artifacts |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*" -g "Tmp*.lean"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the block-doubled sine candidate theta bridge |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.TridiagonalRecurrence` | PASS, 2981 jobs, after adding the direct row-dominant tridiagonal recurrence proof |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the source-facing Theorem 9.13 row-dominant wrappers and Theorem 9.14 row-dominant absorbed-bound wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_rowdom_tridiag.out 2>&1` | PASS after adding lookup checks for the direct row-dominant tridiagonal declarations; redirected output has 71205 lines |
| `lake env lean TmpCh9RowDomAxioms.lean` | PASS before removing the temporary axiom-check file; the direct row-dominant Theorem 9.13 and Theorem 9.14 declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.TridiagonalRecurrence LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, in the final row-dominant verification |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_rowdom_final.out 2>&1` | PASS in the final row-dominant verification; redirected output has 71205 lines |
| `lake env lean TmpCh9RowDomAxioms.lean` | PASS in the final row-dominant verification with fully qualified names; `tridiag_rowDom_growth_bound_3`, `higham9_13_rowDiagDom_tridiag_growth_bound_3`, `higham9_13_rowDiagDom_growthFactorEntry_le_three`, and `higham9_14_tridiag_rowDiagDom_fu_bound_from_structural_growth` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.11 Bohte scalar-expression support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_bohte_final.out 2>&1` | PASS after adding lookup checks for the Theorem 9.11 Bohte declarations; redirected output has 71207 lines |
| `lake env lean TmpCh9BohteAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_11_bohteBound_tridiagonal` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_11_bohteBound_nonneg` and `higham9_11_bohte_banded_solve_tight` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_bohte_nonneg.out 2>&1` | PASS after adding lookup checks for the Bohte nonnegativity and specialized solve declarations; redirected output has 71217 lines |
| `lake env lean TmpCh9BohteAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_11_bohteBound_nonneg` and `higham9_11_bohte_banded_solve_tight` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after removing the stale `p = 2 -> 5` docstring claim and adding `higham9_11_bohteBound_pentadiagonal_formula` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_bohte_p2.out 2>&1` | PASS after adding the `p = 2` arithmetic lookup check; redirected output has 71218 lines |
| `lake env lean TmpCh9BohteAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_11_bohteBound_tridiagonal`, `higham9_11_bohteBound_pentadiagonal_formula`, `higham9_11_bohteBound_nonneg`, and `higham9_11_bohte_banded_solve_tight` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "p = 2.*5|pentadiagonal.*5|ρ ≤ 5|rho.*5" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS for implementation/lookup overclaim cleanup; only the report note explaining removal of the stale claim remains |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, in the final row-dominant verification; only pre-existing QR/FastMatMul warnings |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS in the final row-dominant verification; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS in the final row-dominant verification; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS in the final row-dominant verification; no implementation/lookup artifacts |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*" -g "Tmp*.lean"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS in the final row-dominant verification |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.11 Bohte support and report updates; warnings only in pre-existing QR/FastMatMul files |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.11 Bohte support; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.11 Bohte support; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.11 Bohte support; no implementation/lookup artifacts |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*" -g "Tmp*.lean"` | PASS after the Theorem 9.11 Bohte cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Theorem 9.11 Bohte support |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Bohte nonnegativity/specialized-solve update; warnings only in pre-existing QR/FastMatMul files |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Bohte nonnegativity/specialized-solve update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Bohte nonnegativity/specialized-solve update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Bohte nonnegativity/specialized-solve update; no implementation/lookup artifacts |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*" -g "Tmp*.lean"` | PASS after the Bohte nonnegativity/specialized-solve cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Bohte nonnegativity/specialized-solve update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Bohte `p = 2` arithmetic/docstring update; warnings only in pre-existing QR/FastMatMul files |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Bohte `p = 2` arithmetic/docstring update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Bohte `p = 2` arithmetic/docstring update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Bohte `p = 2` arithmetic/docstring update; no implementation/lookup artifacts |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*" -g "Tmp*.lean"` | PASS after the Bohte `p = 2` arithmetic/docstring cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Bohte `p = 2` arithmetic/docstring update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_11_bohteBound_bandwidth_four_formula` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_bohte_p4_lookup.out 2>&1` | PASS after adding the `p = 4` Bohte arithmetic lookup check; redirected output has 71285 lines |
| `lake env lean TmpCh9BohteP4Axioms.lean` | PASS before removing the temporary axiom-check file; `higham9_11_bohteBound_bandwidth_four_formula` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Bohte `p = 4` arithmetic update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Bohte `p = 4` arithmetic update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Bohte `p = 4` arithmetic update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the Bohte `p = 4` cleanup; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the Bohte `p = 4` report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Bohte `p = 4` arithmetic update; warnings only in pre-existing QR/FastMatMul files |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.10 rank-one multiplier-blunder proof |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_p910_lookup.out 2>&1` | PASS after adding lookup checks for the Problem 9.10 declarations; redirected output has 71316 lines |
| `lake env lean TmpCh9P910Axioms.lean` | PASS before removing the temporary axiom-check file; the Problem 9.10 rank-one action, left-inverse adapter, solution formula, error formula, and multiplier-error formula report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.10 update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.10 update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.10 update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after the Problem 9.10 cleanup; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the Problem 9.10 report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.10 update; warnings only in pre-existing QR/FastMatMul files |
| `lake env lean LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean` | PASS in the Split 2 unifying pass |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS in the Split 2 unifying pass |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor` | PASS, 2979 jobs, in the Split 2 unifying pass |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2991 jobs, in the Split 2 unifying pass |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor LeanFpAnalysis.FP.Algorithms.HighamChapter9 LeanFpAnalysis.FP.Algorithms` | PASS, 3422 jobs; warnings only in pre-existing QR/FastMatMul files |
| `lake build` | PASS, 3476 jobs; warnings only in pre-existing QR/FastMatMul files |
| `lake env lean examples/LibraryLookup.lean > /tmp/librarylookup_ch9_proof_completion.out 2>&1` | FAIL before Chapter 9 checks with Lean stack overflow at IEEE `#check` output |
| `ulimit -s 262144; lake env lean examples/LibraryLookup.lean > /tmp/librarylookup_ch9_proof_completion_bigstack.out 2>&1` | FAIL in the same pre-Chapter-9 IEEE section with stack overflow |
| `lake env lean /tmp/ch9_lookup_new.lean` | PASS; all new Chapter 9 lookup names checked |
| `lake env lean /tmp/ch9_unifying_lookup.lean` | PASS; all unifying-pass Chapter 9 and GrowthFactor lookup names checked |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_unifying_librarylookup.out 2>&1` | PASS; redirected output has 70385 lines |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding Problem 9.11 block algebra |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the Problem 9.11 lookup checks |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding Problem 9.13 threshold-count theorems |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the Problem 9.13 lookup checks |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.1 source iff and Problem 9.1 lower-shear converse |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the Theorem 9.1 / Problem 9.1 lookup checks |
| `lake env lean TmpCh9AxiomCheck.lean` | PASS before removing the temporary axiom-check file; the three new Theorem 9.1 / Problem 9.1 declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.1 / Problem 9.1 update; no matches |
| `rg -n "TODO\|FIXME\|placeholder\|by\s+exact\s+False\.elim\|False\.elim\|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.1 / Problem 9.1 update; no matches |
| `rg -n "HighamChapter13\|HighamChapter14\|chapter13\|chapter14\|Chapter 13\|Chapter 14\|ch13\|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.1 / Problem 9.1 update; no matches |
| `rg --files -g "TmpCh9*" -g "*AxiomCheck.lean"` | PASS after removing temporary check files; no matches |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the rectangular Doolittle identities (9.3)--(9.5) |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_5_librarylookup.out 2>&1` | PASS after adding the (9.5) lookup checks; redirected output has 70475 lines |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding row/column dominance and tridiagonal transpose adapters |
| `lake env lean /tmp/ch9_transpose_axioms.lean` | PASS |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_transpose_librarylookup.out 2>&1` | PASS after adding lookup checks for the transpose adapters; redirected output has 70481 lines |
| `lake build` | PASS, 3477 jobs, after adding row/column dominance and tridiagonal transpose adapters; warnings only in pre-existing QR/FastMatMul files |
| `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean examples/LibraryLookup.lean` | PASS; no matches |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis examples` | PASS; no matches in the Split 2 unifying pass |
| `rg -n "placeholder\|TODO\|FIXME\|by\s+exact\s+False\.elim\|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean` | PASS; no matches |
| `rg -n "TODO\|FIXME\|placeholder\|by\s+exact\s+False\.elim\|False\.elim" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean examples/LibraryLookup.lean docs/LIBRARY_LOOKUP.md` | PASS; no matches after the Problem 9.11 update |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean examples/LibraryLookup.lean docs/LIBRARY_LOOKUP.md` | PASS after the Problem 9.13 update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean examples/LibraryLookup.lean docs/LIBRARY_LOOKUP.md` | PASS after the Problem 9.13 update; no matches |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean examples/LibraryLookup.lean docs/LIBRARY_LOOKUP.md` | PASS after the (9.5) reduced-entry update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean examples/LibraryLookup.lean docs/LIBRARY_LOOKUP.md` | PASS after the (9.5) reduced-entry update; no matches |
| `rg -n "HighamChapter13\|HighamChapter14\|chapter13\|chapter14\|Chapter 13\|Chapter 14\|ch13\|ch14" docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS; no Chapter 13/14 artifacts |
| `rg -n "HighamChapter13\|HighamChapter14\|chapter13\|chapter14\|Chapter 13\|Chapter 14\|ch13\|ch14" docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after the Problem 9.13 update; no matches |
| `git diff --check` | PASS |
| `lake env lean /tmp/ch9_axioms.lean` | PASS |
| `lake env lean /tmp/ch9_unifying_axioms.lean` | PASS |
| `lake env lean /tmp/ch9_11_axioms.lean` | PASS |
| `lake env lean /tmp/ch9_13_axioms.lean` | PASS |
| `lake env lean /tmp/ch9_rect_doolittle_axioms.lean` | PASS |
| `lake env lean /tmp/ch9_5_axioms.lean` | PASS |
| `lake build` | PASS, 3477 jobs, after the Problem 9.11 update; warnings only in pre-existing QR/FastMatMul files |
| `lake build` | PASS, 3477 jobs, after the Problem 9.13 update; warnings only in pre-existing QR/FastMatMul files |
| `lake build` | PASS, 3477 jobs, after the (9.5) reduced-entry update; warnings only in pre-existing QR/FastMatMul files |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Algorithm 9.2 printed leading flop polynomial declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Algorithm 9.2 printed leading flop polynomial declarations |
| `lake env lean TmpCh9FlopAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS; no matches |
| `rg -n "TODO\|FIXME\|placeholder\|by\s+exact\s+False\.elim\|False\.elim\|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS; no matches |
| `git diff --check` | PASS after the Algorithm 9.2 printed leading flop polynomial update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.2 finite-union danger-value count |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the Problem 9.2 lookup check |
| `lake env lean TmpCh9Problem92Axioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.2 update; no matches |
| `rg -n "TODO\|FIXME\|placeholder\|by\s+exact\s+False\.elim\|False\.elim\|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.2 update; no matches |
| `git diff --check` | PASS after the Problem 9.2 update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.14 source scalar declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the Theorem 9.14 source scalar lookup checks |
| `lake env lean TmpCh9ScalarAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.14 source scalar update; no matches |
| `rg -n "TODO\|FIXME\|placeholder\|by\s+exact\s+False\.elim\|False\.elim\|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.14 source scalar update; no matches |
| `rg -n "HighamChapter13\|HighamChapter14\|chapter13\|chapter14\|Chapter 13\|Chapter 14\|ch13\|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.14 source scalar update; no matches |
| `git diff --check` | PASS after the Theorem 9.14 source scalar update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.14 source coefficient aggregation wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the Theorem 9.14 source coefficient aggregation lookup checks |
| `lake env lean TmpCh9SourceAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.14 source coefficient aggregation update; no matches |
| `rg -n "TODO\|FIXME\|placeholder\|by\s+exact\s+False\.elim\|False\.elim\|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.14 source coefficient aggregation update; no matches |
| `rg -n "HighamChapter13\|HighamChapter14\|chapter13\|chapter14\|Chapter 13\|Chapter 14\|ch13\|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.14 source coefficient aggregation update; no matches |
| `git diff --check` | PASS after the Theorem 9.14 source coefficient aggregation update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.2 characteristic-polynomial danger-shift adapter |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the Problem 9.2 characteristic-polynomial danger-shift lookup checks |
| `lake env lean TmpCh9CharpolyAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.2 characteristic-polynomial danger-shift update; no matches |
| `rg -n "TODO\|FIXME\|placeholder\|by\s+exact\s+False\.elim\|False\.elim\|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.2 characteristic-polynomial danger-shift update; no matches |
| `rg -n "HighamChapter13\|HighamChapter14\|chapter13\|chapter14\|Chapter 13\|Chapter 14\|ch13\|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.2 characteristic-polynomial danger-shift update; no matches |
| `git diff --check` | PASS after the Problem 9.2 characteristic-polynomial danger-shift update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.11 bounded-family `g(n)` supremum adapter |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the Problem 9.11 bounded-family `g(n)` supremum lookup checks |
| `lake env lean TmpCh9GrowthSupAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.11 bounded-family `g(n)` supremum update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.11 bounded-family `g(n)` supremum update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.11 bounded-family `g(n)` supremum update; no matches |
| `git diff --check` | PASS after the Problem 9.11 bounded-family `g(n)` supremum update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Algorithm 9.2 dense square executable-loop handoff wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Algorithm 9.2 dense square executable-loop handoff wrappers |
| `lake env lean TmpCh9DoolittleLoopAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Algorithm 9.2 dense square executable-loop handoff update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Algorithm 9.2 dense square executable-loop handoff update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Algorithm 9.2 dense square executable-loop handoff update; no matches |
| `git diff --check` | PASS after the Algorithm 9.2 dense square executable-loop handoff update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.2 source leading-principal-block and shifted-block determinant wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Problem 9.2 source leading-principal-block and shifted-block determinant wrappers |
| `lake env lean TmpCh9ShiftedBlockAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.2 source leading-principal-block and shifted-block update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.2 source leading-principal-block and shifted-block update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.2 source leading-principal-block and shifted-block update; no matches |
| `git diff --check` | PASS after the Problem 9.2 source leading-principal-block and shifted-block update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the final Problem 9.2 shifted-matrix finite-exception theorem |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the final Problem 9.2 shifted-matrix finite-exception theorem |
| `lake env lean Higham9Problem92FinalAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the final Problem 9.2 update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the final Problem 9.2 update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the final Problem 9.2 update; no matches |
| `rg -n "Problem 9\.2 remains|Problem 9\.2.*open|Problem 9\.2.*blocker|final shifted-matrix wrapper|shifted-matrix wrapper|Problems 9\.2|Problem 9\.2 is narrowed" chapter_splitting/reports/chapter9_formalization_report.md chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md /home/mymel/flare-bundle/dev-logs/2026-06-21-split2-unifying-pass.md /home/mymel/flare-bundle/dev-logs/CURRENT.md` | PASS after the final Problem 9.2 update; no stale open-row wording |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "Higham9Problem92FinalAxiomCheck.lean"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the final Problem 9.2 update |
| `lake build` | PASS, 3477 jobs after the final Problem 9.2 update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equation (9.1) exact-LU determinant-pivot product |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the equation (9.1) determinant-pivot product |
| `lake env lean TmpCh9DetAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.1) update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.1) update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.1) update; no matches |
| `git diff --check` | PASS after the equation (9.1) update |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.9 exact-LU algebraic final-`U` growth bound |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the Problem 9.9 lookup checks |
| `lake env lean TmpCh9Problem99Axioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.9 update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.9 update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.9 update; no matches |
| `rg --files | rg "TmpCh9|Problem99Axioms"` | PASS after cleanup; no temporary files remain |
| `git diff --check` | PASS after the Problem 9.9 update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.9 exact no-pivot reduced-matrix growth bound |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Problem 9.9 exact no-pivot reduced-matrix growth bound |
| `lake env lean TmpCh9NoPivot99Axioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the no-pivot reduced-matrix Problem 9.9 update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the no-pivot reduced-matrix Problem 9.9 update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the no-pivot reduced-matrix Problem 9.9 update; no matches |
| `rg --files | rg "TmpCh9NoPivot99Axioms|TmpCh9"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the no-pivot reduced-matrix Problem 9.9 update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Lemma 9.6 reduced-stage absolute-product and row-budget accumulation support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Lemma 9.6 support declarations, including the row-budget accumulation theorem |
| `lake env lean TmpCh9Lemma96Axioms.lean` | PASS before removing the temporary axiom-check file |
| `lake env lean TmpCh9Lemma96RowBudgetAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Lemma 9.6 support update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Lemma 9.6 support update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Lemma 9.6 support update; no matches |
| `rg --files \| rg "TmpCh9Lemma96RowBudgetAxioms\|TmpCh9Lemma96Axioms\|TmpCh9NoPivot99Axioms"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Lemma 9.6 support update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Lemma 9.6 source-constant theorem |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Lemma 9.6 source-constant declarations |
| `lake env lean TmpCh9Lemma96SourceAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Lemma 9.6 source-constant update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Lemma 9.6 source-constant update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Lemma 9.6 source-constant update; no matches |
| `rg --files -g "TmpCh9*"` | PASS after cleanup; no temporary axiom files remain |
| `rg -n "<stale Lemma 9.6 open-status patterns>" chapter_splitting/reports/chapter9_formalization_report.md chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md` | PASS after the Lemma 9.6 source-constant update; no stale open-status wording remains |
| `git diff --check` | PASS after the Lemma 9.6 source-constant update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.12 M-matrix max-entry growth-factor specialization |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.12 sign-equivalent max-entry growth-factor specialization |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Theorem 9.12 M-matrix and sign-equivalent max-entry growth-factor specializations |
| `lake env lean TmpCh9SpecialGrowthAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.12 M-matrix and sign-equivalent growth-factor updates; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.12 M-matrix and sign-equivalent growth-factor updates; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.12 M-matrix and sign-equivalent growth-factor updates; no matches |
| `git diff --check` | PASS after the Theorem 9.12 M-matrix and sign-equivalent growth-factor updates |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_14_source_h_bound_of_absLUhat_mul_one_sub_bound` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the lookup check for `higham9_14_source_h_bound_of_absLUhat_mul_one_sub_bound` |
| `lake env lean TmpCh9DenomAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the denominator-cleared Theorem 9.14 adapter; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the denominator-cleared Theorem 9.14 adapter; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the denominator-cleared Theorem 9.14 adapter; no matches |
| `rg --files -g "TmpCh9*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the denominator-cleared Theorem 9.14 adapter |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 order-two total-nonnegative determinant support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Problem 9.6 determinant support |
| `lake env lean TmpCh9Problem96Axioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 determinant support update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 determinant support update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 determinant support update; no matches |
| `rg --files -g "TmpCh9*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Problem 9.6 determinant support update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 first Schur-update support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Problem 9.6 first Schur-update support |
| `lake env lean TmpCh9Problem96SchurAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 first Schur-update update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 first Schur-update update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 first Schur-update update; no matches |
| `rg --files -g "TmpCh9*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Problem 9.6 first Schur-update update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 source total-nonnegative predicate and first-step adapter |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Problem 9.6 source total-nonnegative adapter |
| `lake env lean TmpCh9Problem96SourceTNAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 source total-nonnegative update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 source total-nonnegative update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 source total-nonnegative update; no matches |
| `rg --files -g "TmpCh9*" -g "TmpCh10*"` | PASS after cleanup; no temporary axiom files remain |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.6 source total-nonnegative update; only pre-existing QR/FastMatMul warnings |
| `git diff --check` | PASS after the Problem 9.6 source-total-nonnegative report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 inherited-submatrix total-nonnegative lemma |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the lookup check for `higham9_6_totalNonnegative_submatrix` |
| `lake env lean TmpCh9Problem96SubmatrixAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 inherited-submatrix update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 inherited-submatrix update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 inherited-submatrix update; no matches |
| `rg --files -g "TmpCh9*" -g "TmpCh10*"` | PASS after cleanup; no temporary axiom files remain |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.6 inherited-submatrix update; only pre-existing QR/FastMatMul warnings |
| `git diff --check` | PASS after the Problem 9.6 inherited-submatrix report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.8 checkerboard sign-matrix support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Problem 9.8 sign-matrix support |
| `lake env lean TmpCh9Problem98Axioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 sign-matrix update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 sign-matrix update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 sign-matrix update; no matches |
| `rg --files -g "TmpCh9*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Problem 9.8 sign-matrix update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.8 checkerboard LU adapter |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Problem 9.8 LU adapter |
| `lake env lean TmpCh9Problem98AdapterAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 LU adapter update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 LU adapter update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 LU adapter update; no matches |
| `rg --files -g "TmpCh9*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Problem 9.8 LU adapter update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equation (9.12) sine-matrix definition/symmetry/scale/conditional-theta support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_sine_lookup.out 2>&1` | PASS after adding lookup checks for the equation (9.12) sine-matrix support; redirected output has 70703 lines |
| `lake env lean TmpCh9SineMatrixAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.12) sine-matrix update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.12) sine-matrix update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.12) sine-matrix update; no matches |
| `rg --files -g "TmpCh9*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the equation (9.12) sine-matrix update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equation (9.13) Fourier/Vandermonde definition and unit-circle support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_fourier_lookup.out 2>&1` | PASS after adding lookup checks for the equation (9.13) Fourier/Vandermonde support; redirected output has 70711 lines |
| `lake env lean TmpCh9FourierAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.13) Fourier/Vandermonde unit-circle update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.13) Fourier/Vandermonde unit-circle update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.13) Fourier/Vandermonde unit-circle update; no matches |
| `rg --files -g "TmpCh9*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the equation (9.13) Fourier/Vandermonde unit-circle update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equation (9.13) Fourier/Vandermonde diagonal Gram support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_fourier_gram_lookup.out 2>&1` | PASS after adding lookup checks for the equation (9.13) Fourier/Vandermonde diagonal Gram support; redirected output has 70722 lines |
| `lake env lean TmpCh9FourierGramAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.13) Fourier/Vandermonde diagonal Gram update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.13) Fourier/Vandermonde diagonal Gram update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.13) Fourier/Vandermonde diagonal Gram update; no matches |
| `rg --files -g "TmpCh9*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the equation (9.13) Fourier/Vandermonde diagonal Gram update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equation (9.13) Fourier/Vandermonde full Gram support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_fourier_full_gram_lookup.out 2>&1` | PASS after adding lookup checks for the equation (9.13) Fourier/Vandermonde full Gram support; redirected output has 70744 lines |
| `lake env lean TmpCh9FourierFullGramAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.13) Fourier/Vandermonde full Gram update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.13) Fourier/Vandermonde full Gram update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.13) Fourier/Vandermonde full Gram update; no matches |
| `rg --files -g "TmpCh9*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the equation (9.13) Fourier/Vandermonde full Gram update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the equation (9.13) Fourier/Vandermonde full Gram update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equation (9.13) Fourier/Vandermonde scaled-adjoint inverse formula |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_fourier_inverse_lookup.out 2>&1` | PASS after adding lookup checks for the equation (9.13) inverse formula; redirected output has 70756 lines |
| `lake env lean TmpCh9FourierInverseAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.13) inverse-formula update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.13) inverse-formula update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.13) inverse-formula update; no matches |
| `rg --files -g "TmpCh9*" -g "TmpCh10*"` | PASS after cleanup; no temporary axiom files remain |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the equation (9.13) Fourier/Vandermonde inverse-formula update; only pre-existing QR/FastMatMul warnings |
| `git diff --check` | PASS after the equation (9.13) inverse-formula report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equation (9.13) complex max-entry theta witness |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the equation (9.13) complex max-entry theta witness |
| `lake env lean TmpCh9FourierThetaAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.13) theta-witness update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.13) theta-witness update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.13) theta-witness update; no matches |
| `rg --files -g "TmpCh9*" -g "TmpCh10*"` | PASS after cleanup; no temporary axiom files remain |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the equation (9.13) theta-witness update; only pre-existing QR/FastMatMul warnings |
| `git diff --check` | PASS after the equation (9.13) theta-witness report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 Sylvester/minor-preservation support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Problem 9.6 Sylvester/minor-preservation support |
| `lake env lean TmpCh9Problem96SchurMinorAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 Sylvester/minor-preservation update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 Sylvester/minor-preservation update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 Sylvester/minor-preservation update; no matches |
| `rg --files -g "TmpCh9*" -g "TmpCh10*"` | PASS after cleanup; no temporary axiom files remain |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.6 Sylvester/minor-preservation update; only pre-existing QR/FastMatMul warnings |
| `git diff --check` | PASS after the Problem 9.6 Sylvester/minor-preservation report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.8 checkerboard matrix-product/minor-determinant support and equation (9.18) tridiagonal structural bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Problem 9.8 matrix/determinant support and equation (9.18) structural bridge |
| `lake env lean TmpCh9Problem98MatrixAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 matrix/determinant and equation (9.18) update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 matrix/determinant and equation (9.18) update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 matrix/determinant and equation (9.18) update; no matches |
| `rg --files -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.8 matrix/determinant and equation (9.18) update; only pre-existing QR/FastMatMul warnings |
| `git diff --check` | PASS after the Problem 9.8 matrix/determinant and equation (9.18) report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.14 structural tridiagonal absorbed-bound wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Theorem 9.14 structural tridiagonal absorbed-bound wrapper |
| `lake env lean TmpCh9TridiagStructuralAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.14 structural wrapper update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.14 structural wrapper update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.14 structural wrapper update; no matches |
| `rg --files -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.14 structural wrapper update; only pre-existing QR/FastMatMul warnings |
| `git diff --check` | PASS after the Theorem 9.14 structural wrapper update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.13 row-dominant transpose tridiagonal growth wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Theorem 9.13 row-dominant transpose tridiagonal growth wrapper |
| `lake env lean TmpCh9RowTridiagAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.13 row-dominant transpose wrapper update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.13 row-dominant transpose wrapper update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.13 row-dominant transpose wrapper update; no matches |
| `rg --files -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.13 row-dominant transpose wrapper update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor` | PASS, 2979 jobs, after adding `maxEntryNorm_le_of_entry_abs_le` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 trailing no-growth package |
| `lake env lean TmpCh9Problem96NoGrowthAxioms.lean` | PASS before removing the temporary axiom-check file |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_p96_nogrowth.out 2>&1` | PASS after adding lookup checks for the Problem 9.6 trailing no-growth package and `maxEntryNorm_le_of_entry_abs_le`; redirected output has 70856 lines |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 trailing no-growth update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 trailing no-growth update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 trailing no-growth update; no matches |
| `rg --files -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.6 trailing no-growth update; only pre-existing QR/FastMatMul warnings |
| `git diff --check` | PASS after the Problem 9.6 trailing no-growth report update |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `maxEntryNorm_submatrix_le` and the Problem 9.6 full-source max-entry no-growth wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_p96_source_maxentry.out 2>&1` | PASS after adding lookup checks for `maxEntryNorm_submatrix_le` and `higham9_6_firstSchurUpdate_trailing_maxEntryNorm_le_source`; redirected output has 70909 lines |
| `lake env lean Higham9Problem96SourceMaxEntryAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 full-source max-entry no-growth update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 full-source max-entry no-growth update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 full-source max-entry no-growth update; no matches |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Problem 9.6 full-source max-entry no-growth report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equation (9.12) sine-matrix scale bounds and conditional theta arithmetic |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the new equation (9.12) sine-scale and conditional-theta declarations |
| `lake env lean TmpCh9SineScaleAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.12) sine-scale/conditional-theta update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.12) sine-scale/conditional-theta update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.12) sine-scale/conditional-theta update; no matches |
| `rg --files -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the equation (9.12) sine-scale/conditional-theta update; only pre-existing QR/FastMatMul warnings |
| `git diff --check` | PASS after the equation (9.12) sine-scale/conditional-theta update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding equation (9.12) sine-matrix positivity and candidate-theta support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for equation (9.12) sine-matrix positivity and candidate-theta declarations |
| `lake env lean Higham9SineThetaAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.12) sine-matrix positivity/candidate-theta update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.12) sine-matrix positivity/candidate-theta update; no matches |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the equation (9.12) sine-matrix positivity/candidate-theta report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.8 / equation (9.13) complex max-entry `theta <= n` row-identity estimate |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the complex max-entry `theta <= n` declarations |
| `lake env lean Higham9ComplexThetaAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the complex max-entry `theta <= n` update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the complex max-entry `theta <= n` update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the complex max-entry `theta <= n` update; no matches |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the complex max-entry `theta <= n` report update |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.13 max-entry `rho <= 3` structural consequence |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Theorem 9.13 max-entry growth declarations |
| `lake env lean Higham9TridiagGrowthFactorAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.13 max-entry growth update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.13 max-entry growth update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.13 max-entry growth update; no matches |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Theorem 9.13 max-entry growth report update |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `maxEntryNorm_matTranspose` and the Theorem 9.13 row-dominant transpose max-entry wrapper using the original source matrix denominator |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_t913_transpose_maxentry.out 2>&1` | PASS after adding lookup checks for `maxEntryNorm_matTranspose` and `higham9_13_rowDiagDom_transpose_growthFactorEntry_le_three_of_Amax`; redirected output has 70903 lines |
| `lake env lean Higham9TridiagTransposeMaxEntryAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.13 transpose max-entry normalization update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.13 transpose max-entry normalization update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/LU/GrowthFactor.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.13 transpose max-entry normalization update; no matches |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Theorem 9.13 transpose max-entry normalization report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 general Schur determinant identity and first-step all-minors total-nonnegative preservation theorem |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_p96_general_schur.out 2>&1` | PASS after adding lookup checks for `higham9_6_pivot_mul_schur_det_eq_source_minor` and `higham9_6_firstSchurUpdate_trailing_totalNonnegative_of_totalNonnegative`; redirected output has 70918 lines |
| `lake env lean Higham9Problem96GeneralSchurAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 general Schur/all-minors update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 general Schur/all-minors update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 general Schur/all-minors update; no matches |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Problem 9.6 general Schur/all-minors report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.1 / Problem 9.2 leading-principal determinant-pivot support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_t91_leading_det.out 2>&1` | PASS after adding lookup checks for `higham9_1_leadingPrincipalBlock_det_eq_pivot_product` and `higham9_1_leadingPrincipalBlock_det_ne_zero_iff_pivots_ne_zero`; redirected output has 70925 lines |
| `lake env lean Higham9LeadingBlockAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.1 leading-block determinant update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.1 leading-block determinant update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.1 leading-block determinant update; no matches |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Theorem 9.1 leading-block determinant report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equation (9.2a) and Theorem 9.3 row-permuted LU certificate adapters |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_t93_permuted.out 2>&1` | PASS after adding lookup checks for the row-permuted/permuted-LU certificate adapters; redirected output has 70941 lines |
| `lake env lean Higham9PermutedAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the row-permuted certificate adapter update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the row-permuted certificate adapter update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the row-permuted certificate adapter update; no matches |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the row-permuted certificate adapter report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the complete-pivoting active-entry ratio and rook row-side multiplier lemmas |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_pivot_ratios.out 2>&1` | PASS after adding lookup checks for the new Section 9.1 pivot-ratio lemmas; redirected output has 70947 lines |
| `lake env lean Higham9PivotRatioAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the pivot-ratio update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the pivot-ratio update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the pivot-ratio update; no matches |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the pivot-ratio report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equation (9.2b) complete-pivoting `PAQ` certificate adapters |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_t93_complete_permuted.out 2>&1` | PASS after adding lookup checks for the complete-pivoting `PAQ` certificate adapters; redirected output has 70967 lines |
| `lake env lean Higham9CompletePermutedAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the complete-pivoting `PAQ` adapter update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the complete-pivoting `PAQ` adapter update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the complete-pivoting `PAQ` adapter update; no matches |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the complete-pivoting `PAQ` adapter report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the permuted `PA`/`PAQ` determinant-pivot consequences |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_permuted_det.out 2>&1` | PASS after adding lookup checks for the permuted determinant-pivot consequences; redirected output has 70980 lines |
| `lake env lean Higham9PermutedDetAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the permuted determinant update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the permuted determinant update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the permuted determinant update; no matches |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the permuted determinant-pivot report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 principal-block positivity adapter and nonnegative-LU growth endpoint |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Problem 9.6 principal-block positivity adapter and nonnegative-LU growth endpoint |
| `lake env lean Higham9Problem96PrincipalAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 principal-block/growth endpoint update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 principal-block/growth endpoint update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 principal-block/growth endpoint update; no matches |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Problem 9.6 principal-block/growth endpoint report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Algorithm 9.2 exact-LU Doolittle recurrence converse theorems |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination` | PASS, 2972 jobs, after adding `luFirstSchurComplement` and `LUFactSpec.of_firstSchurComplement` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.1 first Schur-complement LU construction wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_t91_first_schur.out 2>&1` | PASS after adding lookup checks for `higham9_1_firstSchurComplement` and `higham9_1_lu_exists_of_firstSchurComplement`; redirected output has 71011 lines |
| `lake env lean Higham9FirstSchurAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.1 first Schur-complement update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.1 first Schur-complement update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.1 first Schur-complement update; no matches |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Theorem 9.1 first Schur-complement report update |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_doolittle_converse.out 2>&1` | PASS after adding lookup checks for the exact-LU Doolittle recurrence converse theorems; redirected output has 71005 lines |
| `lake env lean Higham9DoolittleConverseAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the exact-LU Doolittle recurrence converse update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the exact-LU Doolittle recurrence converse update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the exact-LU Doolittle recurrence converse update; no matches |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the exact-LU Doolittle recurrence converse report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the exact-LU uniqueness theorem |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_lu_unique_clean.out 2>&1` | PASS after adding the exact-LU uniqueness lookup check; redirected output has 71007 lines |
| `lake env lean Higham9LUUniqueAxiomCheck.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the exact-LU uniqueness update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the exact-LU uniqueness update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the exact-LU uniqueness update; no matches |
| `rg --files -g "*AxiomCheck.lean" -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the exact-LU uniqueness report update |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.GaussianElimination LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 explicit one-step factors and recursive nonnegative LU construction |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_p96_recursive_lu.out 2>&1` | PASS after adding lookup checks for the Problem 9.6 recursive nonnegative LU construction; redirected output has 71118 lines |
| `lake env lean TmpCh9Problem96RecursiveAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 recursive nonnegative LU update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 recursive nonnegative LU update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 recursive nonnegative LU update; no matches |
| `rg --files -g "TmpCh9*" -g "*AxiomCheck.lean" -g "Tmp*.lean"` | PASS after cleanup; no temporary axiom files remain |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.6 recursive nonnegative LU update; only pre-existing QR/FastMatMul warnings |
| `git diff --check` | PASS after the Problem 9.6 recursive nonnegative LU report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.8 total-nonnegative-checkerboard route to nonnegative LU factors |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_p98_tn_checkerboard.out 2>&1` | PASS after adding lookup checks for the Problem 9.8 total-nonnegative-checkerboard route; redirected output has 71138 lines |
| `lake env lean TmpCh9Problem98TNCheckerboardAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 total-nonnegative-checkerboard update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 total-nonnegative-checkerboard update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 total-nonnegative-checkerboard update; no matches |
| `rg --files -g "TmpCh9*" -g "*AxiomCheck.lean" -g "Tmp*.lean"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Problem 9.8 total-nonnegative-checkerboard report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.8 unpermuted exact-LU final-pivot witness |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_finalpivot.out 2>&1` | PASS after adding lookup checks for the Theorem 9.8 final-pivot declarations; redirected output has 71148 lines |
| `lake env lean TmpCh9FinalPivotAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.8 final-pivot update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.8 final-pivot update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.8 final-pivot update; no matches |
| `rg --files -g "TmpCh9*" -g "*AxiomCheck.lean" -g "Tmp*.lean"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Theorem 9.8 final-pivot update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.8 complete-permuted `P A Q = L U` inverse-entry bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_permuted_finalpivot.out 2>&1` | PASS after adding lookup checks for the complete-permuted Theorem 9.8 final-pivot declarations; redirected output has 71165 lines |
| `lake env lean TmpCh9PermFinalPivotAxioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the complete-permuted Theorem 9.8 final-pivot update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the complete-permuted Theorem 9.8 final-pivot update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the complete-permuted Theorem 9.8 final-pivot update; no matches |
| `rg --files -g "TmpCh9*" -g "*AxiomCheck.lean" -g "Tmp*.lean"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the complete-permuted Theorem 9.8 final-pivot update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.4 row- and complete-pivoted solve adapters |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_problem94_permuted_solve.out 2>&1` | PASS after adding lookup checks for the Problem 9.4 permuted solve declarations; redirected output has 71187 lines |
| `lake env lean TmpCh9Problem94Axioms.lean` | PASS before removing the temporary axiom-check file |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.4 permuted solve update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.4 permuted solve update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.4 permuted solve update; no matches |
| `rg --files -g "TmpCh9*" -g "*AxiomCheck.lean" -g "Tmp*.lean"` | PASS after cleanup; no temporary axiom files remain |
| `git diff --check` | PASS after the Problem 9.4 permuted solve update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equation (9.12) finite cosine/sine orthogonality and sine-matrix self-inverse proof |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_sine_inverse_lookup.out 2>&1` | PASS after adding lookup checks for the finite-sum orthogonality and self-inverse declarations; redirected output has 71255 lines |
| `lake env lean TmpCh9SineInverseAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_12_cos_sum_pos_lt_two_mul`, `higham9_12_sine_product_sum`, `higham9_12_sineMatrix_mul_self`, and `higham9_12_sineMatrix_inverse_formula` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.12) finite-sum/self-inverse update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.12) finite-sum/self-inverse update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.12) finite-sum/self-inverse update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after cleanup; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the equation (9.12) finite-sum/self-inverse report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the equation (9.12) finite-sum/self-inverse update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 reduced-matrix no-pivot growth endpoint |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_p96_reduced_growth_lookup.out 2>&1` | PASS after adding lookup checks for the Problem 9.6 reduced-growth declarations; redirected output has 71284 lines |
| `lake env lean TmpCh9P96ReducedGrowthAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_6_reducedEntry_abs_le_maxEntryNorm_of_nonnegative_LU`, `higham_problem9_9_noPivotReducedGrowthFactor_le_one_of_nonnegative_LU`, and `higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_and_principalBlock_inequalities` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 reduced-growth update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 reduced-growth update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 reduced-growth update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after cleanup; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the Problem 9.6 reduced-growth report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.6 reduced-growth update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 source-shaped nonsingularity wrappers from total nonnegativity plus `det A != 0` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_p96_det_ne_lookup.out 2>&1` | PASS after adding lookup checks for the Problem 9.6 `det A != 0` wrappers; redirected output has 71346 lines |
| `lake env lean TmpCh9P96DetNeAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_6_totalNonnegative_det_nonneg`, `higham9_6_totalNonnegative_det_pos_of_det_ne_zero`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero_and_principalBlock_inequalities`, and `higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_det_ne_zero_and_principalBlock_inequalities` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 `det A != 0` wrapper update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 `det A != 0` wrapper update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.6 `det A != 0` wrapper update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after cleanup; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the Problem 9.6 `det A != 0` wrapper report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.6 `det A != 0` wrapper update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.8 checkerboard inverse-transport support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_p98_inverse_transport_lookup.out 2>&1` | PASS after adding lookup checks for the Problem 9.8 checkerboard inverse-transport declarations; redirected output has 71357 lines |
| `lake env lean TmpCh9P98InverseTransportAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_8_checkerboardConjugate_id`, `higham9_8_checkerboardConjugate_left_inverse`, `higham9_8_checkerboardConjugate_right_inverse`, `higham9_8_checkerboardConjugate_inverse`, and `higham9_8_checkerboardConjugate_inverse_swapped` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 checkerboard inverse-transport update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 checkerboard inverse-transport update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 checkerboard inverse-transport update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after cleanup; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the Problem 9.8 checkerboard inverse-transport report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.8 checkerboard inverse-transport update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.8 cofactor-level nonsingular inverse checkerboard sign-pattern theorem |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Problem 9.8 cofactor-level inverse sign-pattern declarations |
| `lake env lean TmpCh9P98CofactorAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_8_succAbove_val_strictMono`, `higham9_8_checkerboardConjugate_nonsingInv_entry_nonneg_of_det_pos`, and `higham9_8_checkerboardConjugate_nonsingInv_entry_nonneg_of_det_ne_zero` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.8 empty-minor and `1 by 1` inverse-minor wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean >/tmp/ch9_p98_orderone_lookup.out` | PASS after adding lookup checks for the Problem 9.8 empty-minor and `1 by 1` inverse-minor wrappers; redirected output has 71747 lines |
| `lake env lean TmpCh9P98OrderOneAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_8_checkerboardConjugate_nonsingInv_empty_minor_nonneg` and `higham9_8_checkerboardConjugate_nonsingInv_orderOne_minor_nonneg` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 cofactor/order-one inverse-minor update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 cofactor/order-one inverse-minor update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.8 cofactor/order-one inverse-minor update; no implementation/lookup artifacts |
| `rg --files -g "TmpCh9*" -g "TmpCh10*" -g "TmpCh11*" -g "TmpCh12*" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after cleanup; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the Problem 9.8 cofactor/order-one inverse-minor report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.8 full determinant and full-order inverse-minor wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for `higham9_8_checkerboardConjugate_det_eq`, `higham9_8_checkerboardConjugate_nonsingInv_det_nonneg`, and `higham9_8_checkerboardConjugate_nonsingInv_full_order_minor_nonneg` |
| `lake env lean TmpCh9P98FullMinorAxioms.lean` | PASS before removing the temporary axiom-check file; the three new Problem 9.8 full-determinant/full-order declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.8 full-determinant/full-order inverse-minor update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.8 full-determinant/full-order inverse-minor code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean` | PASS after adding `LUFactSpec.isTridiagLU_of_tridiagonal` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.13 exact-`LUFactSpec` tridiagonal structural handoff and source-facing wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_t913_lufactspec_lookup.out 2>&1` | PASS after adding lookup checks for the Theorem 9.13 exact-`LUFactSpec` handoff declarations; redirected output has 71373 lines |
| `lake env lean TmpCh9TridiagLUFactSpecAxioms.lean` | PASS before removing the temporary axiom-check file; `LUFactSpec.isTridiagLU_of_tridiagonal`, `higham9_13_tridiag_growth_bound_3_of_LUFactSpec`, `higham9_13_growthFactorEntry_le_three_of_LUFactSpec`, `higham9_13_rowDiagDom_tridiag_growth_bound_3_of_LUFactSpec`, and `higham9_13_rowDiagDom_growthFactorEntry_le_three_of_LUFactSpec` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.13 exact-`LUFactSpec` handoff update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.13 exact-`LUFactSpec` handoff update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.13 exact-`LUFactSpec` handoff update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after cleanup; no temporary axiom or probe files remain |
| `lake env lean LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean` | PASS after adding `tridiag_colDom_L_entries_bounded` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.13 column-dominant multiplier-bound and no-separate-multiplier exact-LU wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_coldom_lufactspec_lookup.out 2>&1` | PASS after adding lookup checks for the Theorem 9.13 column-dominant multiplier-bound declarations; redirected output has 71386 lines |
| `lake env lean TmpCh9ColDomLUFactSpecAxioms.lean` | PASS before removing the temporary axiom-check file; `tridiag_colDom_L_entries_bounded`, `higham9_13_colDiagDom_L_entries_bounded_of_LUFactSpec`, `higham9_13_colDiagDom_tridiag_growth_bound_3_of_LUFactSpec`, and `higham9_13_colDiagDom_growthFactorEntry_le_three_of_LUFactSpec` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.13 column-dominant multiplier update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.13 column-dominant multiplier update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/LU/TridiagonalRecurrence.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.13 column-dominant multiplier update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after cleanup; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the Theorem 9.13 column-dominant multiplier update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.13 column-dominant multiplier update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.14 exact-`LUFactSpec` column- and row-dominant absorbed-bound wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_t914_lufactspec_lookup.out 2>&1` | PASS after adding lookup checks for the Theorem 9.14 exact-`LUFactSpec` absorbed-bound wrappers; redirected output has 71408 lines |
| `lake env lean TmpCh914LUFactSpecAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_14_tridiag_colDiagDom_fu_bound_from_LUFactSpec` and `higham9_14_tridiag_rowDiagDom_fu_bound_from_LUFactSpec` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.14 exact-`LUFactSpec` wrapper update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.14 exact-`LUFactSpec` wrapper update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.14 exact-`LUFactSpec` wrapper update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after cleanup; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the Theorem 9.14 exact-`LUFactSpec` wrapper report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the final Theorem 9.14 exact-`LUFactSpec` wrapper report/log updates; only pre-existing QR/FastMatMul warnings |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after the final Theorem 9.14 exact-`LUFactSpec` wrapper report/log updates |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_11_complete_pivoting_lower_bound_from_witness_le` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_p911_witness_le.out 2>&1` | PASS after adding the Problem 9.11 inequality-form supremum wrapper lookup check; redirected output has 71412 lines |
| `lake env lean TmpCh9Problem911WitnessLeAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_11_complete_pivoting_lower_bound_from_witness_le` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.11 inequality-form supremum wrapper update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.11 inequality-form supremum wrapper update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Problem 9.11 inequality-form supremum wrapper update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after cleanup; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the Problem 9.11 inequality-form supremum wrapper update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.11 inequality-form supremum wrapper and report/log updates; only pre-existing QR/FastMatMul warnings |
| focused placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.11 inequality-form supremum wrapper report/log updates; no matches and no temporary axiom/probe files remain |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_10_hessenberg_lu_solve_backward_stable_tight` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_hessenberg_solve.out 2>&1` | PASS after adding the Theorem 9.10 Hessenberg solve wrapper lookup check; redirected output has 71420 lines |
| `lake env lean TmpCh9HessenbergSolveAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_10_hessenberg_lu_solve_backward_stable_tight` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/Chapter 13-14/temp-file scans | PASS after the Theorem 9.10 Hessenberg solve wrapper update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Theorem 9.10 Hessenberg solve wrapper update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.10 Hessenberg solve wrapper and report/log updates; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_10_hessenberg_growthFactorEntry_le_card_of_row_bounds` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the lookup check for `higham9_10_hessenberg_growthFactorEntry_le_card_of_row_bounds`; output was large but the process exited successfully |
| `lake env lean --stdin` with `#print axioms higham9_10_hessenberg_growthFactorEntry_le_card_of_row_bounds` | PASS; the theorem reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file/Chapter 13-14 scans | PASS after the Theorem 9.10 row-bound scalar implication update; no implementation or lookup placeholder matches, no temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts added |
| `git diff --check` | PASS after the Theorem 9.10 row-bound scalar implication report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.10 row-bound scalar implication update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.10 first-step Hessenberg GEPP trace support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Theorem 9.10 first-step Hessenberg trace support; output was large but the process exited successfully |
| `lake env lean --stdin` with `#print axioms` for the Theorem 9.10 first-step Hessenberg trace declarations | PASS; `higham9_10_hessenberg_firstColumn_nonzero_row_le_one`, `higham9_10_hessenberg_firstSchurComplement_tail_rows_eq_original`, `higham9_10_hessenberg_firstSchurComplement_isUpperHessenberg`, and `higham9_10_hessenberg_firstSchurComplement_row_bound` report only `propext`, `Classical.choice`, and `Quot.sound`; `higham9_10_hessenberg_firstPivotRowSwap_tail` reports only `propext` and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file/Chapter 13-14 scans | PASS after the Theorem 9.10 first-step Hessenberg trace update; no implementation or lookup placeholder matches, no temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts added |
| `git diff --check` | PASS after the Theorem 9.10 first-step Hessenberg trace update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.10 first-step Hessenberg trace update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.10 Hessenberg stage-invariant predicate and one-stage transition |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Theorem 9.10 Hessenberg stage-invariant declarations; output was large but the process exited successfully |
| `lake env lean --stdin` with `#print axioms` for the Theorem 9.10 Hessenberg stage-invariant declarations | PASS; `higham9_10_HessenbergStageBound` and `higham9_10_hessenberg_firstSchurComplement_stageBound` report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file/Chapter 13-14 scans | PASS after the Theorem 9.10 Hessenberg stage-invariant update; no implementation or lookup placeholder matches, no temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts added |
| `git diff --check` | PASS after the Theorem 9.10 Hessenberg stage-invariant update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.10 Hessenberg stage-invariant update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.10 explicit Hessenberg GEPP trace interface and trace-invariant induction |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Theorem 9.10 explicit Hessenberg GEPP trace declarations; output was large but the process exited successfully |
| `lake env lean --stdin` with `#print axioms` for the Theorem 9.10 explicit Hessenberg GEPP trace declarations | PASS; `higham9_10_HessenbergStageBound_one_of_maxEntryNorm`, `higham9_10_HessenbergGEPPTrace`, `higham9_10_HessenbergGEPPTrace_upperHessenberg_and_stageBound`, `higham9_10_HessenbergGEPPTrace_isUpperHessenberg`, `higham9_10_HessenbergGEPPTrace_stageBound`, `higham9_10_exists_HessenbergGEPPTrace_terminal`, `higham9_10_exists_HessenbergGEPPTrace_terminal_of_det_ne_zero` report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file/Chapter 13-14 scans | PASS after the Theorem 9.10 explicit Hessenberg GEPP trace update; no implementation or lookup placeholder matches, no temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts added |
| `git diff --check` | PASS after the Theorem 9.10 explicit Hessenberg GEPP trace update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.10 explicit Hessenberg GEPP trace update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.10 terminal Hessenberg GEPP trace existence theorems |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Theorem 9.10 terminal Hessenberg GEPP trace declarations; output was large but the process exited successfully |
| `lake env lean --stdin` with `#print axioms` for `LeanFpAnalysis.FP.higham9_10_exists_HessenbergGEPPTrace_terminal` and `LeanFpAnalysis.FP.higham9_10_exists_HessenbergGEPPTrace_terminal_of_det_ne_zero` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file/Chapter 13-14 scans | PASS after the Theorem 9.10 terminal trace update; no implementation or lookup placeholder matches, no temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts added |
| `git diff --check` | PASS after the Theorem 9.10 terminal trace update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.10 terminal trace update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_11_complete_pivoting_lower_bound_from_sine_block_theta` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_sine_block_bridge.out 2>&1` | PASS after adding the Problem 9.11 sine-block visible-witness bridge lookup check; redirected output has 71430 lines |
| `lake env lean TmpCh9SineBlockBridgeAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_11_complete_pivoting_lower_bound_from_sine_block_theta` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.11 sine-block visible-witness bridge update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.11 sine-block visible-witness bridge update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.11 sine-block visible-witness bridge and report/log updates; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.11 flattened sine-block witness bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_flattened_sine_block.out 2>&1` | PASS after adding lookup checks for the flattened Problem 9.11 declarations; redirected output has 71442 lines |
| `lake env lean TmpCh9FlattenedSineBlockAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_11_complete_pivoting_lower_bound_from_flattened_sine_block` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.11 flattened sine-block witness bridge update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.11 flattened sine-block witness bridge update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.11 flattened sine-block witness bridge and report/log updates; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.11 flattened max-entry-norm witness surface |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_flattened_maxentry.out 2>&1` | PASS after adding lookup checks for the flattened max-entry-norm Problem 9.11 declarations; redirected output has 71467 lines |
| `lake env lean TmpCh9FlattenedMaxEntryAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_11_complete_pivoting_lower_bound_from_flattened_sine_block_maxEntry` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.11 flattened max-entry-norm witness update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.11 flattened max-entry-norm witness update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.11 flattened max-entry-norm witness update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equations (9.14)/(9.16) scalar upper-bound RHS definitions |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_growth_scalar_surfaces.out 2>&1` | PASS after adding lookup checks for the equations (9.14)/(9.16) scalar RHS declarations; redirected output has 71600 lines |
| `lake env lean TmpCh9GrowthScalarAxioms.lean` | PASS before removing the temporary axiom-check file; the equations (9.14)/(9.16) scalar nonnegativity lemmas report only `propext`, `Classical.choice`, and `Quot.sound` |
| `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equations (9.14)/(9.16) scalar RHS update; no matches |
| `rg -n "TODO|FIXME|placeholder|by\s+exact\s+False\.elim|False\.elim|Classical\.choice" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equations (9.14)/(9.16) scalar RHS update; no matches |
| `rg -n "HighamChapter13|HighamChapter14|chapter13|chapter14|Chapter 13|Chapter 14|ch13|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equations (9.14)/(9.16) scalar RHS update; no implementation/lookup artifacts |
| `rg --files -g "Tmp*.lean" -g "*Probe.lean" -g "*Axiom*.lean"` | PASS after removing the scalar RHS axiom-check file; no temporary axiom or probe files remain |
| `git diff --check` | PASS after the equations (9.14)/(9.16) scalar RHS report/log updates |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the equations (9.14)/(9.16) scalar RHS update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding scalar positivity lemmas for equations (9.14)/(9.16) |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_growth_scalar_pos.out 2>&1` | PASS after adding lookup checks for the scalar positivity lemmas; redirected output has 71604 lines |
| `lake env lean TmpCh9GrowthScalarPosAxioms.lean` | PASS before removing the temporary axiom-check file; the equations (9.14)/(9.16) scalar positivity lemmas report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the scalar positivity update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the scalar positivity code/lookup update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the scalar positivity update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding Theorem 9.9 diagonal-dominance nonsingularity side-condition lemmas |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_diagdom_side_conditions.out 2>&1` | PASS after adding lookup checks for the Theorem 9.9 side-condition lemmas; redirected output has 71612 lines |
| `lake env lean TmpCh9DiagDomSideAxioms.lean` | PASS before removing the temporary axiom-check file; the Theorem 9.9 side-condition lemmas report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Theorem 9.9 side-condition update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Theorem 9.9 side-condition code/lookup update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.9 side-condition update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding Theorem 9.9 diagonal-dominance off-diagonal and first-ratio lemmas |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_diagdom_ratios.out 2>&1` | PASS after adding lookup checks for the Theorem 9.9 off-diagonal and first-ratio lemmas; redirected output has 71624 lines |
| `lake env lean TmpCh9DiagDomRatioAxioms.lean` | PASS before removing the temporary axiom-check file; the Theorem 9.9 off-diagonal and first-ratio lemmas report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Theorem 9.9 off-diagonal/first-ratio update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Theorem 9.9 off-diagonal/first-ratio code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.9 off-diagonal/first-ratio update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding Theorem 9.9 column-dominant first Schur-complement support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_coldd_schur.out 2>&1` | PASS after adding lookup checks for the Theorem 9.9 column-dominant Schur support; redirected output has 71632 lines |
| `lake env lean TmpCh9ColDDSchurAxioms.lean` | PASS before removing the temporary axiom-check file; the Theorem 9.9 column-dominant first-column multiplier-sum and first-Schur-complement lemmas report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Theorem 9.9 column-dominant Schur update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Theorem 9.9 column-dominant Schur code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.9 column-dominant Schur update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding Theorem 9.9 column-dominant exact no-pivot LU support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_coldd_exact_lu.out 2>&1` | PASS after adding lookup checks for the Theorem 9.9 column-dominant exact-LU declarations; redirected output has 71640 lines |
| `lake env lean TmpCh9ColDDExactLUAxioms.lean` | PASS before removing the temporary axiom-check file; the Theorem 9.9 column-dominant exact-LU declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Theorem 9.9 column-dominant exact-LU update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Theorem 9.9 column-dominant exact-LU code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.9 column-dominant exact-LU update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding Theorem 9.9 column-dominant first-step Schur max-entry bound |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_coldd_first_max.out 2>&1` | PASS after adding lookup check for `higham9_9_colDiagDominant_firstSchurComplement_maxEntryNorm_le_two`; redirected output has 71643 lines |
| `lake env lean TmpCh9ColDDFirstStepMaxAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_9_colDiagDominant_firstSchurComplement_maxEntryNorm_le_two` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Theorem 9.9 first-step max-entry update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Theorem 9.9 first-step max-entry code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.9 first-step max-entry update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_2_absBudgetCertificate_of_literal_doolittle_exact_target_gaps` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_doolittle_exact_target.out 2>&1` | PASS after adding the lookup check for `higham9_2_absBudgetCertificate_of_literal_doolittle_exact_target_gaps`; redirected output has 71670 lines |
| `lake env lean TmpCh9DoolittleExactTargetAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_2_absBudgetCertificate_of_literal_doolittle_exact_target_gaps` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Algorithm 9.2 exact-target gap handoff update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Algorithm 9.2 exact-target gap handoff code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Algorithm 9.2 exact-target gap handoff update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_9_colDiagDominant_firstSchurComplement_offdiag_le_maxEntryNorm` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_coldd_offdiag.out 2>&1` | PASS after adding the lookup check for `higham9_9_colDiagDominant_firstSchurComplement_offdiag_le_maxEntryNorm`; redirected output has 71673 lines |
| `lake env lean TmpCh9ColDDOffdiagAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_9_colDiagDominant_firstSchurComplement_offdiag_le_maxEntryNorm` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Theorem 9.9 first-step off-diagonal update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Theorem 9.9 first-step off-diagonal code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.9 first-step off-diagonal update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding Theorem 9.7 first partial-pivoting Schur-complement growth support and the explicit-stage recurrence |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_pp_stage_recurrence.out 2>&1` | PASS after adding lookup checks for the Theorem 9.7 first-step and recurrence declarations; redirected output has 71689 lines |
| `lake env lean TmpCh9PartialPivotFirstStepAxioms.lean` | PASS before removing the temporary axiom-check file; the Theorem 9.7 first-step and recurrence declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Theorem 9.7 first-step and recurrence update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Theorem 9.7 first-step and recurrence code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.7 first-step and recurrence update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.7 displayed Wilkinson growth witness definitions, exact LU certificate, max-entry norm identities, and exact `growthFactorEntry = 2^(n-1)` theorem |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Theorem 9.7 Wilkinson witness declarations |
| `lake env lean --stdin` with `#print axioms` for the new final-facing witness theorems | PASS; `higham9_7_wilkinsonGrowth_lu`, `higham9_7_wilkinsonGrowthMatrix_maxEntryNorm_eq_one`, `higham9_7_wilkinsonGrowthU_maxEntryNorm_eq_pow`, and `higham9_7_wilkinsonGrowth_growthFactorEntry_eq_pow` report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/local-placeholder/temp-file/Chapter 13-14 scans | PASS after the Theorem 9.7 Wilkinson witness update; no touched-code placeholder matches, no temporary axiom/probe files, and no Chapter 13/14 implementation or report artifacts added |
| `git diff --check` | PASS after the Theorem 9.7 Wilkinson witness code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.7 Wilkinson witness update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the scaled Theorem 9.7 active-stage Wilkinson matrix definitions, no-pivot first-column choice, first Schur-complement doubling, power-of-two stage recurrence, and stage max-entry identities |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the scaled Theorem 9.7 active-stage Wilkinson declarations |
| `lake env lean --stdin` with `#print axioms` for the new final-facing scaled-stage theorems | PASS; `higham9_7_wilkinsonGrowthStage_partialPivotChoice_zero`, `higham9_7_wilkinsonGrowthStage_firstSchurComplement`, `higham9_7_wilkinsonGrowthStage_pow_firstSchurComplement`, `higham9_7_PartialPivotNoInterchangeTrace`, `higham9_7_wilkinsonGrowthStage_partialPivotChoice_zero_succ`, `higham9_7_wilkinsonGrowthStage_pivot_zero_ne_zero`, `higham9_7_wilkinsonGrowthStage_pow_firstSchurComplement_succ`, `higham9_7_wilkinsonGrowthStage_noInterchangeTrace`, `higham9_7_wilkinsonGrowth_noInterchangeTrace`, and `higham9_7_wilkinsonGrowthStage_maxEntryNorm_eq_pow` report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/local-placeholder/temp-file/Chapter 13-14 scans | PASS after the scaled Theorem 9.7 active-stage update; no touched-code placeholder matches, no temporary axiom/probe files, and no Chapter 13/14 implementation or report artifacts added |
| `git diff --check` | PASS after the scaled Theorem 9.7 active-stage code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the scaled Theorem 9.7 active-stage update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the scaled Theorem 9.7 active-stage exact LU certificate, scaled upper-factor max-entry identity, and scaled active-stage `growthFactorEntry = 2^(n-1)` theorem |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_scaled_stage_lu.out 2>&1` | PASS after adding lookup checks for the scaled Theorem 9.7 active-stage LU/growth declarations; redirected output has 72119 lines |
| `lake env lean --stdin` with `#print axioms` for the new final-facing scaled-stage LU/growth theorems | PASS; `higham9_7_wilkinsonGrowthStage_lu`, `higham9_7_wilkinsonGrowthStageU_maxEntryNorm_eq_scale_pow`, and `higham9_7_wilkinsonGrowthStage_growthFactorEntry_eq_pow` report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused placeholder/local-placeholder/temp-file/Chapter 13-14 scans | PASS after the scaled Theorem 9.7 active-stage LU/growth update; no touched-code placeholder matches, no temporary axiom/probe files, and no Chapter 13/14 implementation or report artifacts added |
| `git diff --check` | PASS after the scaled Theorem 9.7 active-stage LU/growth code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the scaled Theorem 9.7 active-stage LU/growth update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.7 Wilkinson no-interchange trace package |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Theorem 9.7 Wilkinson no-interchange trace declarations; output was large but the process exited successfully |
| `lake env lean --stdin` with `#print axioms` for the Theorem 9.7 Wilkinson no-interchange trace declarations | PASS; `higham9_7_wilkinsonGrowthStage_partialPivotChoice_zero_succ`, `higham9_7_wilkinsonGrowthStage_pivot_zero_ne_zero`, `higham9_7_wilkinsonGrowthStage_pow_firstSchurComplement_succ`, `higham9_7_wilkinsonGrowthStage_noInterchangeTrace`, and `higham9_7_wilkinsonGrowth_noInterchangeTrace` report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file/Chapter 13-14 scans | PASS after the Theorem 9.7 Wilkinson no-interchange trace update; no implementation or lookup placeholder matches, no temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts added |
| `git diff --check` | PASS after the Theorem 9.7 Wilkinson no-interchange trace update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.7 Wilkinson no-interchange trace update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.LU.GrowthFactor` | PASS, 2979 jobs, after adding the generic final-upper entrywise-bound to growth-factor adapter |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.9 source-facing endpoint adapter `higham9_9_growthFactorEntry_le_two_of_upper_entry_bound` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for `growthFactorEntry_le_of_entry_bound_factor` and `higham9_9_growthFactorEntry_le_two_of_upper_entry_bound` |
| `lake env lean --stdin` with `#print axioms` for the Theorem 9.9 endpoint adapter declarations | PASS; `growthFactorEntry_le_of_entry_bound_factor` and `higham9_9_growthFactorEntry_le_two_of_upper_entry_bound` report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file/Chapter 13-14 scans | PASS after the Theorem 9.9 endpoint adapter update; no implementation or lookup placeholder matches, no temporary axiom/probe files, and no Chapter 13/14 implementation/report/lookup artifacts added |
| `git diff --check` | PASS after the Theorem 9.9 endpoint adapter code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.9 endpoint adapter update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding Problem 9.14 row-reversal permutation support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_row_reversal.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 row-reversal declarations; redirected output has 71695 lines |
| `lake env lean TmpCh9Problem914RowReversalAxioms.lean` | PASS before removing the temporary axiom-check file; the Problem 9.14 row-reversal declarations report only `propext`, `Classical.choice`, and `Quot.sound`, with the row-reversal definition itself axiom-free |
| focused placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 row-reversal update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 row-reversal code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 row-reversal update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding Problem 9.14 row-reversal max-entry-norm preservation |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the lookup check for `higham_problem9_14_rowReversedMatrix_maxEntryNorm`; streamed output had 71698 lines |
| `lake env lean TmpCh9Problem914MaxEntryAxioms.lean` | PASS before removing the temporary axiom-check file; `higham_problem9_14_rowReversedMatrix_maxEntryNorm` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 max-entry-norm update; implementation/lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 max-entry-norm code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 max-entry-norm update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding Problem 9.14 denominator positivity and same-`U` growth-factor bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_growth_bridge.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 growth bridge declarations; redirected output has 71703 lines |
| `lake env lean TmpCh9Problem914GrowthAxioms.lean` | PASS before removing the temporary axiom-check file; `higham_problem9_14_rowReversedMatrix_maxEntryNorm_pos` and `higham_problem9_14_rowReversedMatrix_growthFactorEntry_eq` report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 growth bridge update; implementation/lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 growth bridge code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 growth bridge update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 direct positive-leading-minor induction and source-facing `det A != 0` nonnegative-LU/growth endpoints |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the new Problem 9.6 direct-route declarations |
| `lake env lean TmpCh9Problem96DirectAxioms.lean` | PASS before removing the temporary axiom-check file; the new Problem 9.6 direct-route declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.6 direct-route update; implementation/lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.6 direct-route update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 principal-block determinant `p = 0` and `p = n` boundary cases |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for `higham9_6_principalBlock_determinantal_inequality_zero` and `higham9_6_principalBlock_determinantal_inequality_full` |
| `lake env lean TmpCh9P96BoundaryAxioms.lean` | PASS before removing the temporary axiom-check file; the two boundary determinant lemmas report only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake env lean TmpCh9P96FinThreeProbe.lean` | FAIL for the experimental `3 by 3`, `p = 1` Koteljanskii/Fischer probe: all entry, `2 by 2`, and full `3 by 3` total-nonnegative minor inequalities were exposed, but `nlinarith` did not close the comparison. No library theorem or report claim depends on this failed temporary probe. |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.6 boundary-case update; implementation/lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.6 boundary-case update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.6 boundary-case update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 `3 by 3`, `p = 1` Sylvester/condensation determinant inequality and middle-entry positivity route |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for `higham9_6_middle_entry_pos_of_fin_three_totalNonnegative_det_pos`, `higham9_6_principalBlock_determinantal_inequality_fin_three_one_of_middle_pos`, and `higham9_6_principalBlock_determinantal_inequality_fin_three_one` |
| `lake env lean TmpCh9P96FinThreeAxioms.lean` | PASS before removing the temporary axiom-check file; the three `3 by 3`, `p = 1` Problem 9.6 declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.6 `3 by 3`, `p = 1` determinant-inequality update; implementation/lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.6 `3 by 3`, `p = 1` determinant-inequality code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.6 `3 by 3`, `p = 1` determinant-inequality update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 `3 by 3`, `p = 2` Sylvester/condensation determinant inequality |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for `higham9_6_principalBlock_determinantal_inequality_fin_three_two_of_middle_pos` and `higham9_6_principalBlock_determinantal_inequality_fin_three_two`; output was large but the process exited successfully |
| `lake env lean TmpCh9P96FinThreeTwoAxioms.lean` | PASS before removing the temporary axiom-check file; the two `3 by 3`, `p = 2` Problem 9.6 declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.6 `3 by 3`, `p = 2` determinant-inequality update; implementation/lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.6 `3 by 3`, `p = 2` determinant-inequality code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.6 `3 by 3`, `p = 2` determinant-inequality update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_6_pivot_mul_firstSchur_leadingPrincipalBlock_det_eq` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the lookup check for `higham9_6_pivot_mul_firstSchur_leadingPrincipalBlock_det_eq`; output was large but the process exited successfully |
| `lake env lean TmpCh9P96LeadingSchurAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_6_pivot_mul_firstSchur_leadingPrincipalBlock_det_eq` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the leading-principal first-Schur determinant identity update; implementation/lookup scans had no matches and no temporary axiom/probe files remain |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_6_desnanot_schur_core` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the lookup check for `higham9_6_desnanot_schur_core`; output was large but the process exited successfully |
| `lake env lean TmpCh9DesnanotCoreAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_6_desnanot_schur_core` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_6_desnanot_schur_core_inequality` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the lookup check for `higham9_6_desnanot_schur_core_inequality`; output was large but the process exited successfully |
| `lake env lean TmpCh9DesnanotIneqAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_6_desnanot_schur_core_inequality` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_6_desnanot_schur_core_inequality_of_offdiag_product_nonneg` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the lookup check for `higham9_6_desnanot_schur_core_inequality_of_offdiag_product_nonneg`; output was large but the process exited successfully |
| `lake env lean TmpCh9DesnanotProductIneqAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_6_desnanot_schur_core_inequality_of_offdiag_product_nonneg` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.6 source-indexed adjacent Desnanot bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Problem 9.6 source-indexed adjacent Desnanot bridge and determinant adapters; output was large but the process exited successfully |
| `lake env lean TmpCh9AdjDesnanotAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_6_adjacent_desnanot_inequality_of_offdiag_product_nonneg` and the three determinant adapters report only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after proving the Problem 9.6 off-diagonal bordered-minor product condition and arbitrary-p Koteljanskii/Fischer determinant comparison |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Problem 9.6 tail-block support and arbitrary-p determinant comparison; output was large but the process exited successfully |
| `lake env lean TmpCh9P96KoteljanskiiAxioms.lean` | PASS before removing the temporary axiom-check file; the Problem 9.6 off-diagonal product, total-nonnegative adjacent Desnanot, `p = 1`, tail-step, and arbitrary-p determinant comparison declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the arbitrary-p Problem 9.6 determinant comparison update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the arbitrary-p Problem 9.6 determinant comparison code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.8 selected Schur/Jacobi complementary-minor support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_p98_selected_jacobi_lookup.out 2>&1` | PASS after adding lookup checks for the selected Schur/Jacobi Problem 9.8 declarations; redirected output has 71946 lines |
| `lake env lean TmpCh9P98SelectedJacobiAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_8_det_inv_topLeft_fromBlocks_eq_det_D_mul_inv_det`, `higham9_8_det_inv_selected_eq_det_complement_mul_inv_det_reindexed`, and `higham9_8_checkerboardConjugate_nonsingInv_principal_minor_nonneg_of_complement_det_ne_zero` report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.8 selected Schur/Jacobi update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.8 selected Schur/Jacobi code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_8_det_selectionComplementEquiv_reindex_eq_perm_sign` and `higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg_of_complement_det_ne_zero_of_reindex_det` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg_of_complement_det_ne_zero_of_perm_sign` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_8_neg_one_pow_sub_eq_mul`, `higham9_8_selectedFinset_orderEmbOfFin_eq`, and `higham9_8_selectionComplementEquiv_eq_finSumEquivOfFinset` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_p98_sign_support_lookup.out 2>&1` | PASS after adding lookup checks for the Problem 9.8 sign-support declarations |
| `lake env lean TmpCh9P98SignProbe.lean` | PASS before removing the temporary axiom-check file; `higham9_8_selection_index_le_value`, `higham9_8_neg_one_pow_sub_eq_mul`, `higham9_8_selectedFinset_orderEmbOfFin_eq`, `higham9_8_selectionComplementEquiv_eq_finSumEquivOfFinset`, and `higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg_of_complement_det_ne_zero_of_perm_sign` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_8_selection_card_le`, `higham9_8_canonicalSelectionComplementEquiv`, `higham9_8_canonicalSelectionComplementEquiv_inl`, `higham9_8_canonicalSelectionComplementEquiv_inr_val`, and `higham9_8_selectionComplementEquiv_perm_sign_of_canonical_shuffle_signs` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_p98_canonical_lookup.out 2>&1` | PASS after adding lookup checks for the Problem 9.8 canonical selected/complement split-reduction declarations |
| `lake env lean TmpCh9P98CanonicalProbe.lean` | PASS before removing the temporary axiom-check file; the Problem 9.8 canonical selected/complement split-reduction declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.8 one-sided shuffle formulas, full selected/complement permutation-sign theorem, and nonsingular-complement selected-minor theorem |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Problem 9.8 selected/complement below-count, cross-product, one-sided shuffle, full permutation-sign, and nonsingular-complement declarations |
| `lake env lean TmpCh9P98ShuffleAxioms.lean` | PASS before removing the temporary axiom-check file; the new Problem 9.8 selected/complement shuffle, full permutation-sign, and nonsingular-complement declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.8 shuffle/sign update; no implementation or lookup matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.8 shuffle/sign code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.8 no-complement-nonsingularity block/selected Jacobi identity and full selected-minor theorem |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for `higham9_8_det_inv_topLeft_fromBlocks_mul_det_eq_det_D`, `higham9_8_det_inv_selected_mul_det_reindexed_eq_det_complement`, and `higham9_8_checkerboardConjugate_nonsingInv_minor_nonneg` |
| `lake env lean TmpCh9P98FullJacobiAxioms.lean` | PASS before removing the temporary axiom-check file; the three final Problem 9.8 declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the full Problem 9.8 selected-minor update; no implementation or lookup matches and no temporary axiom/probe files remain |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the full Problem 9.8 selected-minor update; only pre-existing QR/FastMatMul warnings |
| `git diff --check` | PASS after the full Problem 9.8 code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.10 exposed upper-factor `U` trace and nonsingular exact Hessenberg GEPP growth theorem |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_hessenberg_utrace.out 2>&1` | PASS after adding lookup checks for the Theorem 9.10 `U` trace declarations; redirected output has 72269 lines |
| `lake env lean --stdin` with `#print axioms` for the Theorem 9.10 `U` trace declarations | PASS; all new declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Theorem 9.10 `U` trace update; no implementation or lookup matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Theorem 9.10 `U` trace code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.10 `U` trace update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.7 arbitrary partial-pivoting `U` trace and nonsingular exact GEPP growth theorem |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_gepp_utrace.out 2>&1` | PASS after adding lookup checks for the Theorem 9.7 arbitrary `U` trace declarations; redirected output has 72282 lines |
| `lake env lean --stdin` with `#print axioms` for the Theorem 9.7 arbitrary `U` trace declarations | PASS; all new declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.7 arbitrary `U` trace update; no implementation or lookup matches and no temporary axiom/probe files remain |
| `rg -n "HighamChapter13\|HighamChapter14\|chapter13\|chapter14\|ch13\|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the Theorem 9.7 arbitrary `U` trace update; no Chapter 13/14 implementation or lookup artifacts |
| `git diff --check` | PASS after the Theorem 9.7 arbitrary `U` trace code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.7 arbitrary `U` trace update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.7 upper-bound/attainment package and the Theorem 9.12 SPD positive-`D L^T` source/builder wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_9_7_9_12_packages.out 2>&1` | PASS after adding lookup checks for the Theorem 9.7 package and Theorem 9.12 SPD positive-`D L^T` builder/recurrence declarations; redirected output has 72370 lines |
| `lake env lean --stdin` with `#print axioms` for `higham9_7_wilkinsonGrowth_attains_partialPivoting_bound`, `higham9_7_partialPivoting_growth_bound_and_attainment`, `tridiag_spd_shape_absLU_eq_absA`, and the generic/source-facing/builder/exact-recurrence Theorem 9.12 SPD positive-`D L^T` declarations | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Theorem 9.7 package and Theorem 9.12 SPD positive-`D L^T` builder/recurrence update; no implementation or lookup matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Theorem 9.7 package and Theorem 9.12 SPD positive-`D L^T` builder/recurrence code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Theorem 9.7 package and Theorem 9.12 SPD positive-`D L^T` builder/recurrence update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_5_wilkinson_source_bound_of_PartialPivotGEPPUTrace` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_9_10_trace_wrapper.out 2>&1` | PASS after adding the lookup check for `higham9_5_wilkinson_source_bound_of_PartialPivotGEPPUTrace`; redirected output has 72292 lines |
| `lake env lean --stdin` with `#print axioms higham9_5_wilkinson_source_bound_of_PartialPivotGEPPUTrace` | PASS; reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the equation (9.10) explicit partial-pivoting trace wrapper; no implementation or lookup matches and no temporary axiom/probe files remain |
| `rg -n "HighamChapter13\|HighamChapter14\|chapter13\|chapter14\|Chapter 13\|Chapter 14\|ch13\|ch14" LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` | PASS after the equation (9.10) explicit partial-pivoting trace wrapper; no Chapter 13/14 implementation or lookup artifacts |
| `git diff --check` | PASS after the equation (9.10) explicit partial-pivoting trace wrapper report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the equation (9.10) explicit partial-pivoting trace wrapper update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.7 partial-pivoting trace-growth-family supremum declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_partial_growth_sup.out 2>&1` | PASS after adding lookup checks for the Theorem 9.7 partial-pivoting trace-growth-family declarations; redirected output has 72904 lines |
| `lake env lean --stdin` with qualified `#print axioms` for the six Theorem 9.7 partial-pivoting trace-growth-family declarations | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Theorem 9.7 trace-growth-family supremum update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/report/lookup artifacts were added |
| `git diff --check` | PASS after the Theorem 9.7 trace-growth-family supremum code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the complete-pivoting first-step nonsingularity support declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_complete_pivot_first_step.out 2>&1` | PASS after adding lookup checks for the complete-pivoting first-step support declarations; redirected output has 72384 lines |
| `lake env lean --stdin` with `#print axioms` for `higham9_1_exists_entry_ne_zero_of_det_ne_zero`, `higham9_1_exists_first_completePivotChoice_pivot_ne_zero_of_det_ne_zero`, `higham9_2_firstPivotRowColSwap_det_ne_zero`, and `higham9_1_firstCompletePivotSchurComplement_det_ne_zero_of_det_ne_zero` | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the complete-pivoting first-step support update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the complete-pivoting first-step support code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the complete-pivoting first-step support update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.8 recursive complete-pivoting `U` trace support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_complete_pivot_trace.out 2>&1` | PASS after adding lookup checks for the complete-pivoting trace declarations; redirected output has 72391 lines |
| `lake env lean --stdin` with `#print axioms` for `higham9_8_CompletePivotGECPUTrace_upper_zero`, `higham9_8_exists_CompletePivotGECPUTrace_of_det_ne_zero`, and `higham9_8_exists_CompletePivotGECPUTrace_upper_zero_of_det_ne_zero` | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the complete-pivoting trace update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the complete-pivoting trace code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the complete-pivoting trace update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equation (9.16) recursive rook-pivoting `U` trace support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_rook_trace.out 2>&1` | PASS after adding lookup checks for the rook-pivoting trace declarations; redirected output has 72398 lines |
| `lake env lean --stdin` with `#print axioms` for `higham9_16_RookPivotGEUTrace_upper_zero`, `higham9_16_exists_RookPivotGEUTrace_of_det_ne_zero`, and `higham9_16_exists_RookPivotGEUTrace_upper_zero_of_det_ne_zero` | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the rook-pivoting trace update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the rook-pivoting trace update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equation (9.16) rook-pivoting elementary trace-growth declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the rook-pivoting elementary trace-growth declarations; output was unredirected and large |
| `lake env lean --stdin` with `#print axioms` for `higham9_16_rookPivot_firstSchurComplement_entry_abs_le_two`, `higham9_16_rookPivot_firstSchurComplement_maxEntryNorm_le_two`, `higham9_16_RookPivotGEUTrace_entry_abs_le_pow_two`, and `higham9_16_RookPivotGEUTrace_growthFactorEntry_le_pow_two` | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the rook-pivoting elementary trace-growth update; touched Lean surfaces had no `sorry`/`admit`/`axiom`/`unsafe`/`opaque` or placeholder-pattern matches, no temporary axiom/probe files remain, no Chapter 13/14 implementation/lookup artifacts were added, and touched files had no trailing whitespace |
| `git diff --check` | PASS after the rook-pivoting elementary trace-growth code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding `higham9_16_exists_RookPivotGEUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero` |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the lookup check for `higham9_16_exists_RookPivotGEUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero`; output was unredirected and large |
| `lake env lean --stdin` with `#print axioms` for `higham9_16_exists_RookPivotGEUTrace_growthFactorEntry_le_pow_two_of_det_ne_zero` | PASS; reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after adding the source-facing rook elementary growth adapter; touched Lean surfaces had no `sorry`/`admit`/`axiom`/`unsafe`/`opaque` or placeholder-pattern matches, no temporary axiom/probe files remain, no Chapter 13/14 implementation/lookup artifacts were added, and touched files had no trailing whitespace |
| `git diff --check` | PASS after the source-facing rook elementary growth adapter code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 pre-pivoted GEPP no-interchange exact-LU side |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_prepivot.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 pre-pivoted GEPP no-interchange exact-LU declarations; redirected output has 72403 lines |
| `lake env lean --stdin` with `#print axioms` for `higham9_7_PartialPivotNoInterchangeTrace_exists_LUFactSpec` and `higham_problem9_14_PrePivotedGEPP_exists_LUFactSpec` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 pre-pivoted GEPP update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 pre-pivoted GEPP code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 pre-pivoted GEPP update and Chapter 10 scan cleanup; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding Problem 9.14 row-reversal bijection and determinant-nonsingularity preservation |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_rowrev_det.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 row-reversal bijection and determinant declarations; redirected output has 72407 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_rowReversal_isPermutation` and `higham_problem9_14_rowReversedMatrix_det_ne_zero` | PASS; the bijection theorem reports only `propext` and `Quot.sound`, while the determinant theorem reports `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 row-reversal determinant update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 row-reversal determinant code/lookup update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 row-reversal determinant update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding Problem 9.14 row-reversal endpoint and first-column pivot support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_first_column.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 first-column pivot support; redirected output has 72418 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_rowReversal_zero_eq_last`, `higham_problem9_14_rowReversal_last_eq_zero`, `higham_problem9_14_rowReversedMatrix_firstColumn_partialPivotChoice_last`, and `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_firstColumn_pivot` | PASS; the endpoint lemmas report only `propext`, and the first-column pivot theorems report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 first-column pivot update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 first-column pivot code/lookup update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 first-column pivot update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding Problem 9.14 adjacent/natural pairwise pivot support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_pairpivot.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 pairwise-pivot declarations; redirected output has 72429 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_adjacentRows`, `higham_problem9_14_pairPivotChoice`, `higham_problem9_14_exists_pairPivotChoice`, `higham_problem9_14_pairPivotChoice_multiplier_abs_le_one`, `higham_problem9_14_pairPivotChoice_left_multiplier_abs_le_one`, and `higham_problem9_14_pairPivotChoice_right_multiplier_abs_le_one` | PASS; `adjacentRows` is axiom-free, and the pairwise-pivot choice/existence/multiplier theorems report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 pairwise-pivot update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 pairwise-pivot code/lookup update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 pairwise-pivot update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the deterministic Problem 9.14 natural pairwise pivot selector |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_pairpivot_row.out 2>&1` | PASS after adding lookup checks for the deterministic Problem 9.14 pairwise-pivot selector; redirected output has 72438 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_pairPivotRow`, `higham_problem9_14_pairPivotRow_choice`, `higham_problem9_14_pairPivotRow_left_multiplier_abs_le_one`, and `higham_problem9_14_pairPivotRow_right_multiplier_abs_le_one` | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the deterministic Problem 9.14 pairwise-pivot selector update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the deterministic Problem 9.14 pairwise-pivot selector code/lookup update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the deterministic Problem 9.14 pairwise-pivot selector update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 pair-row swap primitive |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_pairrowswap.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 pair-row swap declarations; redirected output has 72448 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_pairRowSwap`, `higham_problem9_14_pairRowSwap_left`, `higham_problem9_14_pairRowSwap_right`, `higham_problem9_14_pairRowSwap_involutive`, `higham_problem9_14_pairRowSwap_isPermutation`, and `higham_problem9_14_pairRowSwap_det_ne_zero` | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 pair-row swap update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 pair-row swap code/lookup update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 pair-row swap update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 pairwise row-operation zeroing primitive |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_pair_eliminate.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 pairwise row-operation declarations; redirected output has 72459 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_pairEliminateRow`, `higham_problem9_14_pairEliminateRow_target`, `higham_problem9_14_pairEliminateRow_of_ne`, `higham_problem9_14_pairEliminateRow_pivot`, and `higham_problem9_14_pairEliminateRow_target_active_eq_zero` | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 pairwise row-operation update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 pairwise row-operation code/lookup update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 pairwise row-operation update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 pairwise row-operation determinant-preservation support |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_pair_eliminate_det.out 2>&1` | PASS after adding lookup checks for `higham_problem9_14_pairEliminateRow_eq_updateRow_add_smul`, `higham_problem9_14_pairEliminateRow_det_eq`, and `higham_problem9_14_pairEliminateRow_det_ne_zero`; redirected output has 72468 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_pairEliminateRow_eq_updateRow_add_smul`, `higham_problem9_14_pairEliminateRow_det_eq`, and `higham_problem9_14_pairEliminateRow_det_ne_zero` | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 pairwise row-operation determinant-preservation update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 pairwise row-operation determinant-preservation code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 pairwise row-operation determinant-preservation update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 deterministic pairwise-selector tie-breaking and row-reversed last-row consequence |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_pairpivot_selector_tie.out 2>&1` | PASS after adding lookup checks for `higham_problem9_14_pairPivotRow_eq_right_of_abs_le`, `higham_problem9_14_pairPivotRow_eq_left_of_abs_gt`, `higham_problem9_14_pairPivotRow_eq_right_of_firstColumn_partialPivotChoice`, and `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotRow_last`; redirected output has 72478 lines |
| `lake env lean --stdin` with `#print axioms` for the four Problem 9.14 deterministic pairwise-selector tie-breaking declarations | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 deterministic pairwise-selector tie-breaking update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 deterministic pairwise-selector tie-breaking code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 deterministic pairwise-selector tie-breaking update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 pair pivot-to-left row permutation and matrix wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_pairpivot_to_left.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 pair pivot-to-left declarations; redirected output has 72489 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_pairPivotToLeftSwap`, `higham_problem9_14_pairPivotToLeftSwap_left`, `higham_problem9_14_pairPivotToLeftSwap_isPermutation`, `higham_problem9_14_pairPivotToLeftMatrix`, `higham_problem9_14_pairPivotToLeftMatrix_left`, and `higham_problem9_14_pairPivotToLeftMatrix_det_ne_zero` | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 pair pivot-to-left update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 pair pivot-to-left code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 pair pivot-to-left update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 pair pivot-and-eliminate one-step wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_pairpivot_eliminate_to_left.out 2>&1` | PASS after adding lookup checks for `higham_problem9_14_pairPivotEliminateToLeft`, `higham_problem9_14_pairPivotEliminateToLeft_left`, `higham_problem9_14_pairPivotEliminateToLeft_target_active_eq_zero`, and `higham_problem9_14_pairPivotEliminateToLeft_det_ne_zero`; redirected output has 72500 lines |
| `lake env lean --stdin` with `#print axioms` for the four Problem 9.14 pair pivot-and-eliminate declarations | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 pair pivot-and-eliminate update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 pair pivot-and-eliminate code/lookup checkpoint |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 pair pivot-and-eliminate update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 pair pivot-and-eliminate unit multiplier bound |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_pairpivot_eliminate_multiplier.out 2>&1` | PASS after adding the lookup check for `higham_problem9_14_pairPivotEliminateToLeft_multiplier_abs_le_one`; redirected output has 72503 lines |
| `lake env lean --stdin` with `#print axioms LeanFpAnalysis.FP.higham_problem9_14_pairPivotEliminateToLeft_multiplier_abs_le_one` | PASS; reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 pair pivot-and-eliminate unit multiplier update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 pair pivot-and-eliminate unit multiplier code/lookup checkpoint |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 pair pivot-and-eliminate unit multiplier update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 pair pivot-and-eliminate row-shape facts |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_pairpivot_eliminate_rows.out 2>&1` | PASS after adding lookup checks for `higham_problem9_14_pairPivotEliminateToLeft_target`, `higham_problem9_14_pairPivotEliminateToLeft_of_ne`, and `higham_problem9_14_pairPivotEliminateToLeft_pivot`; redirected output has 72514 lines |
| `lake env lean --stdin` with `#print axioms` for the three Problem 9.14 pair pivot-and-eliminate row-shape facts | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 pair pivot-and-eliminate row-shape update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 pair pivot-and-eliminate row-shape code/lookup checkpoint |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 pair pivot-and-eliminate row-shape update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 pre-pivoted row-reversal first-column pair-step specialization |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_prepivot_pair_step.out 2>&1` | PASS after adding lookup checks for `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_row`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_row`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_active_eq_zero`, and `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_multiplier_abs_le_one`; redirected output has 72527 lines |
| `lake env lean --stdin` with `#print axioms` for the three Problem 9.14 pre-pivoted row-reversal pair-step specialization declarations | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 pre-pivoted row-reversal pair-step update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 pre-pivoted row-reversal pair-step code/lookup checkpoint |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 pre-pivoted row-reversal pair-step update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 row-reversed pair pivot-and-eliminate determinant-preservation adapter |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_rowrev_pair_step_det.out 2>&1` | PASS after adding the lookup check for `higham_problem9_14_rowReversedMatrix_pairPivotEliminateToLeft_det_ne_zero`; redirected output has 72530 lines |
| `lake env lean --stdin` with `#print axioms LeanFpAnalysis.FP.higham_problem9_14_rowReversedMatrix_pairPivotEliminateToLeft_det_ne_zero` | PASS; reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 row-reversed pair pivot-and-eliminate determinant update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 row-reversed pair pivot-and-eliminate determinant code/lookup checkpoint |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 row-reversed pair pivot-and-eliminate determinant update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 pre-pivoted row-reversal pair-step target-row formula |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_prepivot_pair_step_target_row.out 2>&1` | PASS after adding the lookup check for `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_row`; redirected output has 72535 lines |
| `lake env lean --stdin` with `#print axioms LeanFpAnalysis.FP.higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_row` | PASS; reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 pre-pivoted row-reversal target-row formula update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 pre-pivoted row-reversal target-row formula code/lookup checkpoint |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 pre-pivoted row-reversal target-row formula update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 normalized row-reversal multiplier and one-step target-row max-entry bound |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_prepivot_pair_step_bound.out 2>&1` | PASS after adding lookup checks for `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_normalized_multiplier_abs_le_one` and `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_target_abs_le_two`; redirected output has 72543 lines |
| `lake env lean --stdin` with `#print axioms` for the Problem 9.14 normalized multiplier and target-row max-entry bound | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 target-row max-entry bound update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 target-row max-entry bound code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 target-row max-entry bound update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 one-step pair pivot-and-eliminate max-entry bound |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_prepivot_pair_step_maxentry.out 2>&1` | PASS after adding the lookup check for `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_maxEntryNorm_le_two`; redirected output has 72548 lines |
| `lake env lean --stdin` with `#print axioms LeanFpAnalysis.FP.higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_maxEntryNorm_le_two` | PASS; reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 one-step max-entry bound update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 one-step max-entry bound code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 one-step max-entry bound update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 one-step pair pivot-and-eliminate growth-factor quotient bound |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_prepivot_pair_step_growth.out 2>&1` | PASS after adding the lookup check for `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_growthFactorEntry_le_two`; redirected output has 72554 lines |
| `lake env lean --stdin` with `#print axioms LeanFpAnalysis.FP.higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_growthFactorEntry_le_two` | PASS; reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/Chapter 13-14/temp-file scans | PASS after the Problem 9.14 one-step growth-factor quotient update; implementation and lookup scans had no matches, no Chapter 13/14 implementation/lookup artifacts were added, and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Problem 9.14 one-step growth-factor quotient code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 one-step growth-factor quotient update; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 pre-pivoted nonzero-pivot/nonsingularity/exact-LU uniqueness bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Problem 9.14 pre-pivoted uniqueness bridge |
| initial unqualified `lake env lean --stdin` `#print axioms` probe for the new Problem 9.14 bridge declarations | Failed with namespace lookup errors only; rerun immediately with fully qualified names |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_7_PartialPivotNoInterchangeTrace_exists_LUFactSpec_pivots_ne_zero`, `higham9_7_PartialPivotNoInterchangeTrace_det_ne_zero`, `higham_problem9_14_PrePivotedGEPP_det_ne_zero`, `higham_problem9_14_PrePivotedGEPP_lu_unique`, and `higham_problem9_14_PrePivotedGEPP_exists_unique_LUFactSpec` | PASS; all five report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Problem 9.14 pre-pivoted uniqueness bridge; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files |
| added-line Chapter 13/14 artifact scan over touched files | PASS; no Chapter 13 or Chapter 14 implementation/report/lookup artifacts were added by this update |
| `git diff --check` | PASS after the Problem 9.14 pre-pivoted uniqueness bridge code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms` | PASS, 3423 jobs, after the Problem 9.14 pre-pivoted uniqueness bridge; only pre-existing QR/FastMatMul warnings |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.8 cumulative real complete-pivoting `PAQ = LU` certificate and `theta <= rho` existence bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_cumulative_complete.out 2>&1` | PASS after adding lookup checks for the Theorem 9.8 cumulative complete-pivoting certificate; redirected output has 72593 lines |
| `lake env lean --stdin` with `#print axioms` for `higham9_8_extendTrailingPerm_isPermutation`, `higham9_8_luFirstSchurComplement_trailingPerm`, `higham9_8_exists_CompletePermutedLUFactSpec_of_det_ne_zero`, and `higham9_8_exists_completePivoting_growth_factor_ge_theta_real` | PASS; the permutation-lift theorem reports only `propext`, and the other three report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.8 cumulative complete-pivoting certificate; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files |
| added-line Chapter 13/14 artifact scan over touched files | PASS; no Chapter 13 or Chapter 14 implementation/report/lookup artifacts were added by this update |
| `git diff --check` | PASS after the Theorem 9.8 cumulative complete-pivoting certificate code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the concrete Problem 9.11 flattened sine-block complete-pivoting witness |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_sine_block_complete.out 2>&1` | PASS after adding lookup checks for the concrete Problem 9.11 sine-block complete-pivoting witness; redirected output has 72618 lines |
| `lake env lean --stdin` with `#print axioms` for `higham9_11_flattenTwoBlock_right_inverse`, `higham9_det_ne_zero_of_isRightInverse`, and `higham9_11_exists_completePivoting_sine_block_growth_ge_succ` | PASS; all three report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the concrete Problem 9.11 sine-block complete-pivoting witness; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no temporary axiom/probe files remain |
| added-line Chapter 13/14 artifact scan over repository touched files | PASS; no Chapter 13 or Chapter 14 implementation/report/lookup artifacts were added by this update |
| `git diff --check` | PASS after the concrete Problem 9.11 sine-block complete-pivoting witness code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the fixed Problem 9.11 sine-block complete-pivoting growth-value bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the fixed Problem 9.11 growth-value bridge |
| `lake env lean TmpSplit2Ch9P911GrowthSetAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_11_sineBlockCompletePivotingGrowthSet`, `higham9_11_sineBlockCompletePivotingGrowthSet_exists_ge_succ`, and `higham9_11_sineBlockCompletePivotingGrowth_upper_bound_ge_succ` report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the fixed Problem 9.11 growth-value bridge; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, or `False.elim` matches, and no temporary axiom/probe files remain |
| added-line Chapter 13/14 artifact scan over repository touched files | PASS; no Chapter 13 or Chapter 14 implementation/report/lookup artifacts were added by this update |
| `git diff --check` | PASS after the fixed Problem 9.11 growth-value bridge code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the certificate-level Problem 9.11 `g(n)` growth surface and sine-block lower-bound theorem |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the certificate-level Problem 9.11 `g(n)` declarations |
| `lake env lean TmpSplit2Ch9CertificateGrowthAxioms.lean` | PASS before removing the temporary axiom-check file; `higham9_completePivotingCertificateGrowthSet`, `higham9_completePivotingCertificateGrowthValues`, `higham9_completePivotingCertificateGrowthSup`, `higham9_completePivotingCertificateGrowth_le_sup`, and `higham9_11_completePivotingCertificateGrowthSup_ge_succ` report only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding `higham9_11_completePivotingCertificateGrowthValues_exists_ge_succ` and refactoring the certificate-level supremum lower-bound theorem through it |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the certificate-level complete-pivoting value-set witness |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the lookup check for `higham9_11_completePivotingCertificateGrowthValues_exists_ge_succ` |
| `lake env lean --stdin` with `#print axioms` for `higham9_11_completePivotingCertificateGrowthValues_exists_ge_succ` and `higham9_11_completePivotingCertificateGrowthSup_ge_succ` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder and Chapter 13/14 scans | PASS after the certificate-level complete-pivoting value-set witness; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, `Classical.choice`, or Chapter 13/14 implementation/lookup artifacts |
| `lake build` | PASS, 3498 jobs, after the certificate-level complete-pivoting value-set witness; warnings only in pre-existing QR/Givens and FastMatMul modules |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 generic right-dominant pairwise elimination step lemmas |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the four Problem 9.14 generic right-dominant pairwise elimination step lemmas |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_pairPivotEliminateToLeft_left_eq_right_of_abs_le`, `higham_problem9_14_pairPivotEliminateToLeft_target_eq_left_sub_right`, `higham_problem9_14_pairPivotEliminateToLeft_target_active_eq_zero_of_abs_le`, and `higham_problem9_14_pairPivotEliminateToLeft_target_abs_le_two_of_abs_le` | PASS; each reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Problem 9.14 generic right-dominant pairwise elimination step; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/report/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.14 generic right-dominant pairwise elimination step code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 pair-step row-shape invariant lemmas |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_pair_step_shape.out 2>&1` | PASS after adding lookup checks for the two Problem 9.14 pair-step row-shape invariant lemmas; redirected output has 72654 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le` and `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_of_ne_pair` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Problem 9.14 pair-step row-shape invariant update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.14 pair-step row-shape invariant code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 one-step next-selector invariant lemmas |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_pair_step_selector_invariant.out 2>&1` | PASS after adding lookup checks for the two Problem 9.14 one-step next-selector invariant lemmas; redirected output has 72663 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_active_ne_zero` and `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_unchanged_abs_le_pivot` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Problem 9.14 one-step next-selector invariant update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.14 one-step next-selector invariant code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 two-step bubble trace support lemmas |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_two_step_bubble.out 2>&1` | PASS after adding lookup checks for the two Problem 9.14 two-step bubble support lemmas; redirected output has 72675 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_next_pairPivotRow` and `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_row` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Problem 9.14 two-step bubble trace support update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.14 two-step bubble trace support code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 two-step induction invariant lemmas |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_two_step_invariants.out 2>&1` | PASS after adding lookup checks for the three Problem 9.14 two-step induction invariant lemmas; redirected output has 72695 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_of_ne_triple`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_active_ne_zero`, and `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_unchanged_abs_le_pivot` | PASS; all three report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Problem 9.14 two-step induction invariant update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.14 two-step induction invariant code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 recursive pairwise-bubble schedule declarations and scheduled one-/two-step pivot-row bridges |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_recursive_bubble_schedule.out 2>&1` | PASS after adding lookup checks for the nine Problem 9.14 recursive pairwise-bubble schedule declarations; redirected output has 72716 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_pairwiseBubbleRow_zero`, `higham_problem9_14_pairwiseBubbleRows_adjacent`, `higham_problem9_14_pairwiseBubbleRows_distinct`, `higham_problem9_14_pairwiseBubbleMatrix_zero`, `higham_problem9_14_pairwiseBubbleMatrix_succ`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_one_pivot_row`, and `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_two_pivot_row` | PASS; row-zero reports only `propext`, row adjacency/distinctness report `propext` and `Quot.sound`, and the recursive matrix/scheduled bridge declarations report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Problem 9.14 recursive pairwise-bubble schedule update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.14 recursive pairwise-bubble schedule code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 general recursive pairwise-bubble prefix invariant |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_prefix_invariant.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 strict row-motion arithmetic lemma and general prefix invariant; redirected output has 72732 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_pairwiseBubbleRow_succ_val_lt` and `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_invariant` | PASS; the strict row-motion arithmetic lemma reports `propext` and `Quot.sound`, and the general prefix invariant reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Problem 9.14 recursive pairwise-bubble prefix-invariant update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.14 recursive pairwise-bubble prefix-invariant code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 terminal scheduled pivot-row and nonzero-pivot corollaries |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_terminal_bubble.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 terminal scheduled pivot-row corollaries; redirected output has 72739 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_pairwiseBubbleRow_self`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_pivot_row`, and `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_pivot_active_ne_zero` | PASS; the terminal row-index fact reports only `propext`, and the terminal pivot-row/nonzero-pivot corollaries report only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 prefix eliminated-column invariant and terminal eliminated-column corollary |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_eliminated_prefix.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 eliminated-column prefix invariant and terminal corollary; redirected output has 72747 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_eliminated_active_eq_zero` and `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_active_eq_zero_of_ne_zero` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Problem 9.14 terminal and eliminated-column scheduled-bubble updates; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.14 terminal and eliminated-column scheduled-bubble code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 source-facing pairwise-bubble trace predicate and terminal trace proof |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_trace.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 pairwise-bubble trace predicate and trace proofs; redirected output has 72753 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_pairwiseBubbleMatrix_trace` and `higham_problem9_14_pairwiseBubbleMatrix_terminal_trace` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Problem 9.14 pairwise-bubble trace update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.14 pairwise-bubble trace code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 scheduled pairwise-bubble determinant-preservation and terminal nonsingularity theorems |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_trace_det.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 scheduled pairwise-bubble determinant-preservation theorems; redirected output has 72758 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_pairwiseBubbleMatrix_det_ne_zero` and `higham_problem9_14_pairwiseBubbleMatrix_terminal_det_ne_zero` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Problem 9.14 scheduled pairwise-bubble determinant-preservation update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.14 scheduled pairwise-bubble determinant-preservation code/lookup/report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 terminal pairwise-bubble Schur bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_terminal_first_schur.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 source-row map, prefix eliminated-row formula, terminal row-reversed Schur-complement bridge, and terminal first-Schur-complement bridge; redirected output has 72778 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_pairwiseBubbleSourceRow_succ`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_eliminated_row`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_trailing_eq_rowReversed_firstSchurComplement`, and `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_firstSchurComplement_eq_rowReversed_firstSchurComplement` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Problem 9.14 terminal pairwise-bubble Schur bridge; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.14 terminal pairwise-bubble Schur bridge code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 pre-pivoted Schur-complement recursive handoff |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_prepivot_schur_handoff.out 2>&1` | PASS after adding lookup checks for `higham9_7_PartialPivotNoInterchangeTrace_reindex_time` and `higham_problem9_14_PrePivotedGEPP_firstSchurComplement`; redirected output has 72782 lines |
| `lake env lean --stdin` with `#print axioms` for `higham9_7_PartialPivotNoInterchangeTrace_reindex_time` and `higham_problem9_14_PrePivotedGEPP_firstSchurComplement` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Problem 9.14 pre-pivoted Schur-complement recursive handoff; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.14 pre-pivoted Schur-complement recursive handoff code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 recursive row-reversal pairwise trace package |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_recursive_pairwise_trace.out 2>&1` | PASS after adding lookup checks for `higham_problem9_14_RecursivePairwiseBubbleTrace` and `higham_problem9_14_RecursivePairwiseBubbleTrace_of_PrePivotedGEPP`; redirected output has 72785 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_RecursivePairwiseBubbleTrace` and `higham_problem9_14_RecursivePairwiseBubbleTrace_of_PrePivotedGEPP` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Problem 9.14 recursive row-reversal pairwise trace package; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.14 recursive row-reversal pairwise trace package code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 recursive pairwise LU certificate and same-LU bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_pairwise_lu_certificate.out 2>&1` | PASS after adding lookup checks for the four Problem 9.14 recursive pairwise LU certificate declarations; redirected output has 72795 lines |
| `lake env lean --stdin` with `#print axioms` for `higham_problem9_14_RecursivePairwiseLUFactSpec`, `higham_problem9_14_RecursivePairwiseLUFactSpec_to_LUFactSpec`, `higham_problem9_14_exists_RecursivePairwiseLUFactSpec_of_PrePivotedGEPP`, and `higham_problem9_14_RecursivePairwiseLUFactSpec_same_as_PrePivotedGEPP` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Problem 9.14 recursive pairwise LU certificate and same-LU bridge; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.14 recursive pairwise LU certificate and same-LU bridge code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.14 first §9.9 method trace/LU certificate and same-LU bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p914_first_method_final.out 2>&1` | PASS after adding lookup checks for the Problem 9.14 first §9.9 method declarations; redirected output has 72845 lines |
| `lake env lean --stdin` with `#print axioms` for the six Problem 9.14 first §9.9 method recursive trace/LU certificate declarations | PASS; all six report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the Problem 9.14 first §9.9 method closure; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.14 first §9.9 method code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the complete-pivoting trace growth boundedness declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_complete_pivot_trace_bound.out 2>&1` | PASS after adding lookup checks for the complete-pivoting trace-bound declarations; redirected output has 72871 lines |
| `lake env lean --stdin` with `#print axioms` for seven final-facing complete-pivoting trace-bound declarations | PASS; all seven report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 added-line scans | PASS after the complete-pivoting trace growth boundedness update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the complete-pivoting trace growth boundedness report/log update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.11 trace-level `g(2n)` lower-bound bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_p911_trace_g.out 2>&1` | PASS after adding lookup checks for the Problem 9.11 trace-level lower-bound declarations; redirected output has 72894 lines |
| `lake env lean --stdin` with `#print axioms` for the two max-entry helper declarations and five Problem 9.11 trace-level bridge/lower-bound declarations | PASS; all seven report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file, stale Problem 9.11 blocker, and Chapter 13/14 added-line scans | PASS after the Problem 9.11 trace-level lower-bound report/log update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, stale Problem 9.11 trace-bridge blockers remain only in historical log context that points to the new closure, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Problem 9.11 trace-level lower-bound code/lookup/report/log update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Problem 9.11 complete-pivoting trace supremum endpoint |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Problem 9.11 complete-pivoting trace supremum endpoint |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for `higham9_completePivotingUTraceGrowthValues_nonempty` and `higham9_8_completePivotingUTraceGrowthSup_le_pow_two` |
| focused implementation/lookup placeholder/local-placeholder and Chapter 13/14 scans | PASS after the complete-pivoting trace supremum endpoint update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, `Classical.choice`, or Chapter 13/14 implementation/lookup artifacts |
| `lake env lean --stdin` with `#print axioms` for the two new complete-pivoting trace supremum endpoint declarations | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake build` | PASS, 3498 jobs, after the complete-pivoting trace supremum endpoint update; warnings only in pre-existing QR/Givens and FastMatMul modules |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the equation (9.16) rook-pivoting trace supremum endpoint |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the equation (9.16) rook-pivoting trace supremum endpoint |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for `higham9_16_rookPivotingUTraceGrowthValues_nonempty` and `higham9_16_rookPivotingUTraceGrowthSup_le_pow_two` |
| focused implementation/lookup placeholder/local-placeholder and Chapter 13/14 scans | PASS after the rook-pivoting trace supremum endpoint update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, `Classical.choice`, or Chapter 13/14 implementation/lookup artifacts |
| `lake env lean --stdin` with `#print axioms` for the two new rook-pivoting trace supremum endpoint declarations | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake build` | PASS, 3498 jobs, after the rook-pivoting trace supremum endpoint update; warnings only in pre-existing QR/Givens and FastMatMul modules |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.10 upper-Hessenberg GEPP trace growth-value/supremum endpoint |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after refreshing the compiled module artifact for the Theorem 9.10 Hessenberg endpoint |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the seven Theorem 9.10 Hessenberg trace growth-value/supremum declarations |
| `lake env lean --stdin` with `#print axioms` for the five theorem declarations in the Theorem 9.10 Hessenberg trace growth-value/supremum endpoint | PASS; all five report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 scans | PASS after the Theorem 9.10 Hessenberg endpoint update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, placeholder, `False.elim`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the Theorem 9.10 Hessenberg endpoint code/lookup/report update |
| `lake build` | PASS, 3498 jobs, after the Theorem 9.10 Hessenberg endpoint update; warnings only in pre-existing QR/Givens and FastMatMul modules |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the row-pivoted Theorem 9.5 GEPP/Wilkinson adapter and row-permutation norm lemmas |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the row-pivoted Theorem 9.5 GEPP/Wilkinson adapter and refreshing compiled artifacts |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_pivoted_wilkinson.out 2>&1` | PASS after adding lookup checks for `higham9_2_rowPermutedMatrix_maxEntryNorm`, `higham9_2_rowPermutedMatrix_infNorm`, and `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace`; redirected output has 260 lines |
| `lake env lean --stdin` with `#print axioms` for the three row-pivoted Theorem 9.5 adapter declarations | PASS; all three report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file and Chapter 13/14 scans | PASS after the row-pivoted Theorem 9.5 adapter update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, `False.elim`, `Classical.choice`, or temporary axiom/probe files, and no Chapter 13/14 implementation/lookup artifacts were added |
| `git diff --check` | PASS after the row-pivoted Theorem 9.5 adapter code/lookup/report update |
| `lake build` | PASS, 3498 jobs, after the row-pivoted Theorem 9.5 adapter update; warnings only in pre-existing QR/Givens and FastMatMul modules |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the full row/column permutation norm-preservation endpoint |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after rebuilding the full permutation norm-preservation endpoint |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the four full permutation norm-preservation declarations |
| `lake env lean --stdin` with fully qualified `#print axioms` for the four full permutation norm-preservation declarations | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the full permutation norm-preservation endpoint update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, `False.elim`, `Classical.choice`, or temporary axiom/probe files |
| `git diff --check` | PASS after the full permutation norm-preservation code/lookup/report update |
| `lake build` | PASS, 3498 jobs, after the full permutation norm-preservation endpoint update; warnings only in pre-existing QR/Givens and FastMatMul modules |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the complete-pivoted explicit-certificate normwise wrapper |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after rebuilding the complete-pivoted explicit-certificate normwise wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding the lookup check for `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace` |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace` | PASS; reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the complete-pivoted explicit-certificate normwise wrapper update; implementation and lookup scans had no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, `False.elim`, `Classical.choice`, or temporary axiom/probe files |
| `git diff --check` | PASS after the complete-pivoted explicit-certificate code/lookup/report update |
| `lake build` | PASS, 3498 jobs, after the complete-pivoted explicit-certificate normwise wrapper update; warnings only in pre-existing QR/Givens and FastMatMul modules |

`#print axioms` results for final-facing new declarations:

| Declaration family | Axioms reported |
| --- | --- |
| Equation (9.19) exact recurrence-to-product theorem plus Theorem 9.13/9.14 recurrence-based tridiagonal builder wrappers | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.8 max-entry lemmas and wrappers | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.8 cumulative real complete-pivoting `PAQ = LU` certificate and `theta <= rho` existence bridge | `higham9_8_extendTrailingPerm_isPermutation` reports only `propext`; `higham9_8_luFirstSchurComplement_trailingPerm`, `higham9_8_exists_CompletePermutedLUFactSpec_of_det_ne_zero`, and `higham9_8_exists_completePivoting_growth_factor_ge_theta_real` report only `propext`, `Classical.choice`, and `Quot.sound` |
| Problem 9.11 concrete flattened sine-block complete-pivoting witness | `higham9_11_flattenTwoBlock_right_inverse`, `higham9_det_ne_zero_of_isRightInverse`, and `higham9_11_exists_completePivoting_sine_block_growth_ge_succ` report only `propext`, `Classical.choice`, and `Quot.sound` |
| Problem 9.11 fixed sine-block complete-pivoting growth-value bridge | `higham9_11_sineBlockCompletePivotingGrowthSet`, `higham9_11_sineBlockCompletePivotingGrowthSet_exists_ge_succ`, and `higham9_11_sineBlockCompletePivotingGrowth_upper_bound_ge_succ` report only `propext`, `Classical.choice`, and `Quot.sound` |
| Problem 9.11 certificate-level `g(n)` surface and sine-block lower bound | `higham9_completePivotingCertificateGrowthSet`, `higham9_completePivotingCertificateGrowthValues`, `higham9_completePivotingCertificateGrowthSup`, `higham9_completePivotingCertificateGrowth_le_sup`, `higham9_11_completePivotingCertificateGrowthValues_exists_ge_succ`, and `higham9_11_completePivotingCertificateGrowthSup_ge_succ` report only `propext`, `Classical.choice`, and `Quot.sound` |
| Theorem 9.10 upper-Hessenberg GEPP trace growth-value/supremum endpoint | `higham9_10_hessenbergGEPPUTraceGrowthValues_le_card`, `higham9_10_hessenbergGEPPUTraceGrowthValues_bddAbove`, `higham9_10_hessenbergGEPPUTraceGrowth_le_sup`, `higham9_10_hessenbergGEPPUTraceGrowthValues_nonempty`, and `higham9_10_hessenbergGEPPUTraceGrowthSup_le_card` report only `propext`, `Classical.choice`, and `Quot.sound` |
| Theorem 9.5 row-pivoted GEPP/Wilkinson adapter and row-permutation norm preservation | `higham9_2_rowPermutedMatrix_maxEntryNorm`, `higham9_2_rowPermutedMatrix_infNorm`, and `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace` report only `propext`, `Classical.choice`, and `Quot.sound` |
| Equations (9.2a)--(9.2b) full row/column permutation norm preservation | `higham9_2_colPermutedMatrix_maxEntryNorm`, `higham9_2_colPermutedMatrix_infNorm`, `higham9_2_rowColPermutedMatrix_maxEntryNorm`, and `higham9_2_rowColPermutedMatrix_infNorm` report only `propext`, `Classical.choice`, and `Quot.sound` |
| Theorem 9.5 complete-pivoted explicit-certificate normwise wrapper | `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace` reports only `propext`, `Classical.choice`, and `Quot.sound` |
| Algorithm 9.2 dense-loop certificate handoff, exact-target gap handoff, and Theorem 9.3 dense-loop backward-error wrappers | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.5 witness theorems | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.6 source total-nonnegative determinant, source-shaped `det A != 0` nonsingularity wrappers, principal-block determinant singular/boundary/`2 by 2`/`3 by 3` base cases, general and leading-principal first-step Schur preservation, block Desnanot/Sylvester Schur determinant core, reordered block inequality, source-indexed determinant adapters and adjacent conditional bridge, trailing max-entry no-growth package, direct positive-leading-minor induction, recursive nonnegative LU construction, nonnegative-LU final-`U` and reduced-matrix growth endpoints, and full-source max-entry no-growth wrapper plus the arbitrary-p Koteljanskii/Fischer determinant comparison | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.7 count theorems | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.8 checkerboard sign-matrix support | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.8 checkerboard LU adapter support | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.8 checkerboard inverse-transport, matrix-product, and minor-determinant support; equation (9.18) tridiagonal structural bridge | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.8 cofactor-level nonsingular inverse checkerboard entry sign-pattern support plus empty-/order-one inverse-minor wrappers | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.8 adjugate inverse identity and codimension-one checkerboard inverse-minor wrapper | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.8 full determinant and full-order inverse-minor wrappers | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.8 selected Schur/Jacobi complementary-minor identity and conditional principal inverse-minor consequence | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.8 selected/complement full-matrix determinant reindex sign exposure | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.8 arbitrary selected-minor nonsingular-complement consequence and selected/complement permutation-sign support | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.8 arbitrary selected-minor nonsingular-complement consequence under explicit pure permutation-sign lemma and selected/complement sign-support adapters | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.8 canonical selected/complement split-reduction adapters | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.8 one-sided selected/complement shuffle formulas, full permutation-sign theorem, and nonsingular-complement selected-minor theorem | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.8 no-complement-nonsingularity block/selected Jacobi identity and full selected-minor checkerboard inverse theorem | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.8 total-nonnegative-checkerboard nonnegative-LU route | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.8 unpermuted exact-LU final-pivot witness and growth bridge | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.8 complete-permuted `P A Q = L U` inverse-entry bridge | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.8 recursive complete-pivoting `U` trace existence and upper-triangularity support | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.8 / Problem 9.11 complete-pivoting trace growth boundedness | `higham9_2_rowColPermutedMatrix_firstPivotRowSwap_maxEntryNorm`, `higham9_1_completePivot_rowColPermuted_partialPivotChoice_zero`, `higham9_8_completePivot_firstSchurComplement_maxEntryNorm_le_two`, `higham9_8_CompletePivotGECPUTrace_entry_abs_le_pow_two`, `higham9_8_CompletePivotGECPUTrace_growthFactorEntry_le_pow_two`, `higham9_completePivotingUTraceGrowthValues_bddAbove`, `higham9_completePivotingUTraceGrowth_le_sup`, `higham9_completePivotingUTraceGrowthValues_nonempty`, and `higham9_8_completePivotingUTraceGrowthSup_le_pow_two` report only `propext`, `Classical.choice`, and `Quot.sound` |
| Problem 9.11 trace-level complete-pivoting `g(2n)` lower bound and max-entry helper declarations | `maxEntryNorm_le_of_entry_le_bound`, `maxEntryNorm_le_of_entry_le_max`, `higham9_8_CompletePivotGECPUTrace_exists_CompletePermutedLUFactSpec_maxEntryNorm_le`, `higham9_8_CompletePivotGECPUTrace_growth_factor_ge_theta_real`, `higham9_11_exists_completePivotingUTrace_sine_block_growth_ge_succ`, `higham9_11_completePivotingUTraceGrowthValues_exists_ge_succ`, and `higham9_11_completePivotingUTraceGrowthSup_ge_succ` report only `propext`, `Classical.choice`, and `Quot.sound` |
| Problem 9.4 row- and complete-pivoted LU solve analogues | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.11 Bohte scalar tridiagonal/pentadiagonal/source-example arithmetic checks, scalar nonnegativity, and conditional solve specialization | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.11 block-doubled sine candidate theta bridge | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.11 sine-block visible-witness lower-bound bridge | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.11 flattened sine-block bounded-supremum witness bridge | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.11 flattened max-entry-norm bounded-supremum witness bridge | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.14 structural tridiagonal absorbed-bound wrappers, including direct row-dominant and exact-`LUFactSpec` column/row wrappers | `propext`, `Classical.choice`, `Quot.sound` |
| Section 9.1 pivot-choice existence, selected-pivot nonzero support, multiplier/active-entry ratio lemmas, and one-stage package lemmas | `propext`, `Classical.choice`, `Quot.sound` |
| Section 9.1 / equation (9.2b) complete-pivoting first-step nonsingularity support | `propext`, `Classical.choice`, `Quot.sound` |
| Equation (9.16) recursive rook-pivoting `U` trace existence, upper-triangularity, elementary trace-growth support, and trace supremum endpoint | `propext`, `Classical.choice`, `Quot.sound` |
| Algorithm 9.2 rectangular source identities (9.3)--(9.5) | `propext`, `Classical.choice`, `Quot.sound` |
| Algorithm 9.2 exact-LU Doolittle recurrence converse theorems | `propext`, `Classical.choice`, `Quot.sound` |
| Lemma 9.6 reduced-stage absolute-product, row-budget accumulation, and source-constant theorems | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.5 max-entry-to-infinity growth bridge and explicit partial-pivoting trace equation (9.10) wrapper | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.10 first-pivot nonsingularity support: row-swap involution/permutation, row-swap determinant preservation, nonsingular first-column nonzero witness, nonzero first partial-pivot choice, and first Schur-complement determinant inheritance | row-swap function/permutation lemmas report only `propext`; determinant/first-pivot/Schur-complement declarations report `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.10 first-step Hessenberg GEPP trace support | `propext`, `Classical.choice`, `Quot.sound`; `higham9_10_hessenberg_firstPivotRowSwap_tail` itself reports only `propext` and `Quot.sound` |
| Theorem 9.10 Hessenberg stage invariant and one-stage transition | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.10 explicit Hessenberg GEPP trace interface and trace-invariant induction | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.10 exposed upper-factor `U` trace, row-bound theorem, nonsingular trace construction, and source-facing `rho_n^p <= n` growth theorem | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.10 row-bound-to-growth scalar implication | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.10 conditional Hessenberg solve wrapper | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.11 block inverse, norm identities, theta identity, equality-/inequality-form lower-bound arithmetic, and supremum adapter | `propext`, `Classical.choice`, `Quot.sound` |
| Equation (9.12) sine-matrix definition/symmetry/scale/positivity/finite-sum orthogonality/self-inverse/theta support | `propext`, `Classical.choice`, `Quot.sound` |
| Equation (9.13) Fourier/Vandermonde definition, unit-circle, roots-of-unity cancellation, full Gram support, scaled-adjoint inverse formula, complex max-entry `theta <= n`, complex max-entry theta witness, conditional complex growth bridge, explicit complex certificate-level final-pivot bridge, complex trace/certificate construction, complex trace-to-certificate max-entry transfer, and Fourier/Vandermonde trace-level `n <= rho` theorem | `propext`, `Classical.choice`, `Quot.sound` |
| Equations (9.14)/(9.16) scalar complete-/rook-pivoting upper-bound RHS nonnegativity and positivity lemmas | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.13 threshold-update, modification-count, and growth-factor bound | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 pre-pivoted nonzero-pivot, nonsingularity, and exact-LU uniqueness bridge | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.9/9.13 transpose orientation adapters | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.9 diagonal-dominance nonsingularity side-condition lemmas | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.9 diagonal-dominance off-diagonal and first-ratio lemmas | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.9 column-dominant first-column multiplier-sum, first-Schur-complement preservation/max-entry/off-diagonal/nonsingularity, and exact no-pivot LU existence/uniqueness lemmas | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.9 final-upper entrywise-bound to growth-factor endpoint adapter | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.13 structural tridiagonal componentwise and max-entry growth wrappers, including exact-LU tridiagonal structural handoff, column-dominant multiplier bound, source-facing exact-LU wrappers without separate multiplier hypotheses, direct row-dominant growth, direct row-dominant exact-LU rescaling from the transposed certificate, and transpose max-entry normalization | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.12 SPD positive-`D L^T`, nonnegative-LU, M-matrix, sign-equivalent, and total-nonnegative source-existence max-entry growth-factor consequences | `propext`, `Classical.choice`, `Quot.sound` |
| Algorithm 9.2 printed leading flop polynomial declarations | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.7 first partial-pivoting Schur-complement entry/max-entry growth support, arbitrary nonsingular recursive partial-pivoting `U` trace and exact `rho_n^p <= 2^(n-1)` growth theorem, trace-level partial-pivoting growth-value/supremum declarations, explicit-stage recurrence, scaled active-stage no-pivot Schur-complement doubling/exact LU/growth, displayed Wilkinson growth witness exact LU/max-entry/growth theorems, no-interchange trace, and upper-bound/attainment package | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 pre-pivoted GEPP predicate, no-interchange exact LU certificate existence, trace stage reindexing, and first-Schur recursive handoff | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 row-reversal permutation, bijection, endpoint facts, nonsingularity preservation, first-column pivot support, pair-row swap primitive, natural pairwise-pivot selector/tie-breaking/pivot-to-left/multiplier support, pairwise row-operation zeroing and determinant-preservation primitives, one-step pair pivot-and-eliminate wrapper with row-shape facts, row-reversed determinant preservation, unit multiplier bound, and pre-pivoted row-reversal first-column pivot-row/target-row/target-bound/max-entry/growth-quotient specialization, matrix involution, max-entry-norm, and growth-factor denominator surface | `propext`, `Classical.choice`, `Quot.sound`; `higham_problem9_14_rowReversal` and `higham_problem9_14_adjacentRows` are axiom-free, `higham_problem9_14_rowReversal_isPermutation` reports only `propext`, `Quot.sound`, and the endpoint facts report only `propext` |
| Problem 9.14 generic right-dominant pairwise elimination step (`higham_problem9_14_pairPivotEliminateToLeft_left_eq_right_of_abs_le`, `higham_problem9_14_pairPivotEliminateToLeft_target_eq_left_sub_right`, `higham_problem9_14_pairPivotEliminateToLeft_target_active_eq_zero_of_abs_le`, `higham_problem9_14_pairPivotEliminateToLeft_target_abs_le_two_of_abs_le`) | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 pair-step row-shape invariant (`higham_problem9_14_pairPivotEliminateToLeft_of_ne_pair_of_abs_le`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_of_ne_pair`) | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 one-step next-selector invariant (`higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_pivot_active_ne_zero`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_unchanged_abs_le_pivot`) | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 two-step bubble trace support (`higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_next_pairPivotRow`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_row`) | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 two-step induction invariants (`higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_of_ne_triple`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_pivot_active_ne_zero`, `higham_problem9_14_PrePivotedGEPP_rowReversedMatrix_pairPivotEliminateToLeft_twoStep_unchanged_abs_le_pivot`) | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 recursive pairwise-bubble schedule (`higham_problem9_14_pairwiseBubbleRow_zero`, `higham_problem9_14_pairwiseBubbleRows_adjacent`, `higham_problem9_14_pairwiseBubbleRows_distinct`, `higham_problem9_14_pairwiseBubbleMatrix_zero`, `higham_problem9_14_pairwiseBubbleMatrix_succ`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_one_pivot_row`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_two_pivot_row`) | row-zero reports only `propext`; adjacent/distinct row-index facts report `propext`, `Quot.sound`; recursive matrix/scheduled bridge declarations report `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 recursive pairwise-bubble prefix invariant (`higham_problem9_14_pairwiseBubbleRow_succ_val_lt`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_invariant`) | strict row-motion arithmetic reports `propext`, `Quot.sound`; general prefix invariant reports `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 terminal scheduled-bubble corollaries (`higham_problem9_14_pairwiseBubbleRow_self`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_pivot_row`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_pivot_active_ne_zero`) | terminal row-index fact reports only `propext`; terminal pivot-row/nonzero-pivot corollaries report `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 eliminated-column scheduled-bubble invariants (`higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_eliminated_active_eq_zero`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_active_eq_zero_of_ne_zero`) | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 pairwise-bubble trace predicate/proofs (`higham_problem9_14_pairwiseBubbleMatrix_trace`, `higham_problem9_14_pairwiseBubbleMatrix_terminal_trace`) | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 scheduled pairwise-bubble determinant preservation (`higham_problem9_14_pairwiseBubbleMatrix_det_ne_zero`, `higham_problem9_14_pairwiseBubbleMatrix_terminal_det_ne_zero`) | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 terminal pairwise-bubble Schur bridge (`higham_problem9_14_pairwiseBubbleSourceRow_succ`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_prefix_eliminated_row`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_trailing_eq_rowReversed_firstSchurComplement`, `higham_problem9_14_PrePivotedGEPP_pairwiseBubbleMatrix_terminal_firstSchurComplement_eq_rowReversed_firstSchurComplement`) | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 recursive row-reversal pairwise trace package (`higham_problem9_14_RecursivePairwiseBubbleTrace`, `higham_problem9_14_RecursivePairwiseBubbleTrace_of_PrePivotedGEPP`) | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 recursive pairwise LU certificate and same-LU bridge (`higham_problem9_14_RecursivePairwiseLUFactSpec`, `higham_problem9_14_RecursivePairwiseLUFactSpec_to_LUFactSpec`, `higham_problem9_14_exists_RecursivePairwiseLUFactSpec_of_PrePivotedGEPP`, `higham_problem9_14_RecursivePairwiseLUFactSpec_same_as_PrePivotedGEPP`) | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.14 first §9.9 method trace/LU certificate and same-LU bridge (`higham_problem9_14_RecursiveFirstMethodTrace`, `higham_problem9_14_RecursiveFirstMethodTrace_of_PrePivotedGEPP`, `higham_problem9_14_RecursiveFirstMethodLUFactSpec`, `higham_problem9_14_RecursiveFirstMethodLUFactSpec_to_LUFactSpec`, `higham_problem9_14_exists_RecursiveFirstMethodLUFactSpec_of_PrePivotedGEPP`, `higham_problem9_14_RecursiveFirstMethodLUFactSpec_same_as_PrePivotedGEPP`) | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.2 finite-union, characteristic-polynomial, source leading-block danger-shift count, shifted-block determinant adapter, and final shifted-matrix finite-exception theorem | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.14 source scalar relation, aggregation, and denominator-cleared adapter theorems | `propext`, `Classical.choice`, `Quot.sound` |
| Equation (9.1) exact-LU determinant-pivot product | `propext`, `Classical.choice`, `Quot.sound` |
| Theorem 9.1 / Problems 9.1-9.2 proper-leading-principal determinant-pivot support, first Schur-complement LU construction step, proper Schur determinant inheritance, exact LU existence/uniqueness, lower-shear nonuniqueness converse, and source iff | `propext`, `Classical.choice`, `Quot.sound` |
| Equations (9.2a)--(9.2b) and Theorem 9.3 permuted LU certificate adapters | `propext`, `Classical.choice`, `Quot.sound` |
| Equations (9.2a)--(9.2b) permuted determinant-pivot consequences | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.9 exact-LU algebraic final-`U` growth bound | `propext`, `Classical.choice`, `Quot.sound` |
| Problem 9.9 exact no-pivot reduced-matrix growth bound | `propext`, `Classical.choice`, `Quot.sound` |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.13 row-dominant transpose exact-LU/growth package |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.13 row-dominant transpose exact-LU/growth package |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Theorem 9.13 row-dominant transpose exact-LU/growth declarations |
| `lake env lean --stdin` with `#print axioms` for `higham9_13_rowDiagDom_transpose_exists_LUFactSpec_growth_bound_3` and `higham9_13_rowDiagDom_transpose_exists_LUFactSpec_growthFactorEntry_le_three` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans and Chapter 13/14 code/lookup diff scan | PASS after the row-dominant transpose exact-LU/growth update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the row-dominant transpose exact-LU/growth code/lookup/report update |
| `lake build` | PASS, 3498 jobs, after the row-dominant transpose exact-LU/growth update; warnings only in pre-existing QR/Givens and FastMatMul modules |
| Theorem 9.13 row-dominant transpose exact-LU/growth existential package (`higham9_13_rowDiagDom_transpose_exists_LUFactSpec_growth_bound_3`, `higham9_13_rowDiagDom_transpose_exists_LUFactSpec_growthFactorEntry_le_three`) | `propext`, `Classical.choice`, `Quot.sound` |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the direct Theorem 9.13 row-dominant exact-LU rescaling bridge and existential growth package |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after adding the direct Theorem 9.13 row-dominant exact-LU rescaling bridge and existential growth package |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the direct Theorem 9.13 row-dominant exact-LU declarations |
| `lake env lean --stdin` with `#print axioms` for `higham9_13_LUFactSpec_of_transpose_LUFactSpec_nonzero_pivots`, `higham9_13_rowDiagDom_exists_LUFactSpec_growth_bound_3`, and `higham9_13_rowDiagDom_exists_LUFactSpec_growthFactorEntry_le_three` | PASS; all three report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the direct Theorem 9.13 row-dominant exact-LU update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the direct Theorem 9.13 row-dominant exact-LU code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.14 column- and direct row-dominant exact-LU absorbed backward-error existential wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after adding the Theorem 9.14 exact-LU absorbed backward-error existential wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean` | PASS after adding lookup checks for the Theorem 9.14 exact-LU absorbed backward-error existential wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_14_colDiagDom_exists_LUFactSpec_fu_bound` and `higham9_14_rowDiagDom_exists_LUFactSpec_fu_bound` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.14 exact-LU absorbed backward-error existential wrapper update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.14 exact-LU absorbed backward-error wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the equation-(9.22) constant-growth source-model bridge and column/direct-row diagonally-dominant exact-LU `3 f(u)|A|` source packages |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after adding the equation-(9.22) constant-growth source-model bridge and diagonal-dominance source packages |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_source_f_diagdom_models.out 2>&1` | PASS after adding lookup checks for the equation-(9.22) constant-growth and diagonal-dominance source-model packages |
| `lake env lean --stdin` with `#print axioms` for `higham9_14_source_f_bound_of_absLU_le_const_absA_and_9_20_9_21_models`, `higham9_14_colDiagDom_exists_LUFactSpec_source_f_bound_of_models`, and `higham9_14_rowDiagDom_exists_LUFactSpec_source_f_bound_of_models` | PASS; all three report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the equation-(9.22) constant-growth and diagonal-dominance source-model package update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the equation-(9.22) constant-growth and diagonal-dominance source-model code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.14 builder/recurrence `3 f(u)|A|` source-model wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after adding the Theorem 9.14 builder/recurrence source-model wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_builder_source_f_models.out 2>&1` | PASS after adding lookup checks for the Theorem 9.14 builder/recurrence source-model wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_14_tridiag_colDiagDom_source_f_bound_from_builders`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence`, and `higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.14 builder/recurrence source-model wrapper update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.14 builder/recurrence source-model code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.14 exact-`LUFactSpec` `3 f(u)|A|` source-model wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after adding the Theorem 9.14 exact-`LUFactSpec` source-model wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_lufactspec_source_f_models.out 2>&1` | PASS after adding lookup checks for the Theorem 9.14 exact-`LUFactSpec` source-model wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_14_tridiag_colDiagDom_source_f_bound_from_LUFactSpec` and `higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUFactSpec` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.14 exact-`LUFactSpec` source-model wrapper update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.14 exact-`LUFactSpec` source-model code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.14 coefficient-dominated source-model production bridges |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after adding the Theorem 9.14 coefficient-dominated source-model production bridges and refreshing the compiled module artifact |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_model_production.out 2>&1` | PASS after adding lookup checks for the Theorem 9.14 coefficient-dominated source-model production bridges |
| `lake env lean --stdin` with `#print axioms` for `higham9_20_tridiag_lu_perturbation_model_of_LUBackwardError_le`, `higham9_21_tridiag_solve_perturbation_model_of_fl_triangular_solves_gamma_le`, `higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma_le`, and `higham9_14_source_f_bound_of_LUBackwardError_fl_triangular_solves_gamma` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.14 coefficient-dominated source-model production bridge update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.14 coefficient-dominated source-model production bridge code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the exact-`LUFactSpec` column/row diagonal-dominance certificate-producing source-model wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after adding the exact-`LUFactSpec` certificate-producing source-model wrappers and refreshing the compiled module artifact |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_exact_lu_model_production.out 2>&1` | PASS after adding lookup checks for the exact-`LUFactSpec` certificate-producing source-model wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_14_tridiag_colDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves` and `higham9_14_tridiag_rowDiagDom_source_f_bound_from_LUBackwardError_fl_triangular_solves` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the exact-`LUFactSpec` certificate-producing source-model wrapper update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the exact-`LUFactSpec` certificate-producing source-model wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the builder/recurrence certificate-producing source-model wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after adding the builder/recurrence certificate-producing source-model wrappers and refreshing the compiled module artifact |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_builder_recurrence_model_production.out 2>&1` | PASS after adding lookup checks for the builder/recurrence certificate-producing source-model wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_LUBackwardError_fl_triangular_solves`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_LUBackwardError_fl_triangular_solves`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence_LUBackwardError_fl_triangular_solves`, and `higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence_LUBackwardError_fl_triangular_solves` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the builder/recurrence certificate-producing source-model wrapper update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the builder/recurrence certificate-producing source-model wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean` | PASS after adding `LUFactSpec.to_LUBackwardError_zero` |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the exact-LU actual triangular-solve source-data wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after adding the exact-LU zero-backward-error bridge and exact-factor actual-solve wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_lufactspec_actual_solves.out 2>&1` | PASS after adding lookup checks for the exact-LU actual triangular-solve wrappers |
| `lake env lean --stdin` with `#print axioms` for `LUFactSpec.to_LUBackwardError_zero`, `higham9_14_source_f_bound_of_LUFactSpec_fl_triangular_solves_gamma_le`, `higham9_14_colDiagDom_exists_LUFactSpec_source_f_bound_actual_triangular_solves`, and `higham9_14_rowDiagDom_exists_LUFactSpec_source_f_bound_actual_triangular_solves` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the exact-LU actual triangular-solve wrapper update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/LU/GaussianElimination.lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the exact-LU actual triangular-solve code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the equation-(9.19) exact-product-to-`LUFactSpec` bridge and builder/recurrence exact-factor actual triangular-solve wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after the builder/recurrence exact-factor actual triangular-solve wrapper update |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_lufactspec_builder_actual_solves.out 2>&1` | PASS after adding lookup checks for the equation-(9.19) `LUFactSpec` bridge and builder/recurrence exact-factor actual-solve wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_19_tridiag_LUFactSpec_of_exact_product`, `higham9_19_tridiag_LUFactSpec_of_recurrence`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves`, `higham9_14_tridiag_rowDiagDom_source_f_bound_from_builders_LUFactSpec_fl_triangular_solves`, `higham9_14_tridiag_colDiagDom_source_f_bound_from_recurrence_LUFactSpec_fl_triangular_solves`, and `higham9_14_tridiag_rowDiagDom_source_f_bound_from_recurrence_LUFactSpec_fl_triangular_solves` | PASS; all six report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the builder/recurrence exact-factor actual-solve wrapper update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the builder/recurrence exact-factor actual-solve code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Algorithm 9.2 literal Doolittle source-budget/component-dominance/exact-product wrapper family |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the literal Doolittle wrapper family |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_literal_doolittle_wrappers.out 2>&1` | PASS after adding lookup checks for the Algorithm 9.2 literal Doolittle wrapper family |
| `lake env lean --stdin` with `#print axioms` for `higham9_2_absBudgetCertificate_of_literal_doolittle_source_budgets`, `higham9_2_absBudgetCertificate_of_literal_doolittle_component_dominance`, `higham9_2_absBudgetCertificate_of_literal_doolittle_exact_product_margins`, and `higham9_2_absBudgetCertificate_of_literal_doolittle_exact_product_numerator_margins` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Algorithm 9.2 literal Doolittle wrapper update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Algorithm 9.2 literal Doolittle wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the exact pivot-certificate Theorem 9.3 zero/gamma adapters and complete-pivoting exact-certificate existence package |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the exact pivot-certificate package |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_exact_pivot_certificates.out 2>&1` | PASS after adding lookup checks for the exact pivot-certificate declarations |
| `lake env lean --stdin` with `#print axioms` for `higham9_2_permutedLUFactSpec_to_PermutedLUBackwardError_zero`, `higham9_2_permutedLUFactSpec_to_PermutedLUBackwardError_gamma`, `higham9_3_permuted_lu_backward_error_gamma_of_LUFactSpec`, `higham9_2_completePermutedLUFactSpec_to_CompletePermutedLUBackwardError_zero`, `higham9_2_completePermutedLUFactSpec_to_CompletePermutedLUBackwardError_gamma`, `higham9_3_complete_permuted_lu_backward_error_gamma_of_LUFactSpec`, and `higham9_3_exists_complete_permuted_lu_backward_error_gamma_of_det_ne_zero` | PASS; all seven report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the exact pivot-certificate update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the exact pivot-certificate code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the exact row-pivoted and complete-pivoted Theorem 9.5 certificate wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the exact Theorem 9.5 certificate wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_exact_wilkinson_cert_wrappers.out 2>&1` | PASS after adding lookup checks for the exact Theorem 9.5 certificate wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_LUFactSpec` and `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_LUFactSpec` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the exact Theorem 9.5 certificate wrapper update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the exact Theorem 9.5 certificate wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the total-nonnegative exact-factor/actual triangular-solve Theorem 9.14 source endpoint |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the total-nonnegative actual-solve endpoint |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_total_nonnegative_actual_solves.out 2>&1` | PASS after adding lookup checks for `higham9_14_totalNonnegative_exists_source_h_bound_of_models` and `higham9_14_totalNonnegative_exists_source_f_bound_actual_triangular_solves` |
| `lake env lean --stdin` with `#print axioms` for `higham9_14_totalNonnegative_exists_source_f_bound_actual_triangular_solves` | PASS; reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the total-nonnegative exact-factor/actual-solve endpoint update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the total-nonnegative actual-solve code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the SPD, nonnegative-LU, M-matrix LU, and sign-equivalent exact-factor/actual triangular-solve Theorem 9.14 source endpoints |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the special-class actual-solve endpoints |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_special_class_actual_solves.out 2>&1` | PASS after adding lookup checks for the four special-class actual-solve endpoints |
| `lake env lean --stdin` with `#print axioms` for `higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves`, `higham9_14_nonnegative_lu_source_f_bound_actual_triangular_solves`, `higham9_14_mmatrix_lu_source_f_bound_actual_triangular_solves`, and `higham9_14_sign_equiv_source_f_bound_actual_triangular_solves` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the special-class exact-factor/actual-solve endpoint update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the special-class actual-solve code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 source-shaped min condition-number chain wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the min condition-number chain wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_chi_min_chain.out 2>&1` | PASS after adding lookup checks for the two min condition-number chain wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_15_chi_condition_chain_min_of_inverse_product_bounds` and `higham9_15_chi_condition_chain_min_of_inverse_products` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the min condition-number chain wrapper update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the min condition-number code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 product-smallness normwise source wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the Theorem 9.15 product-smallness normwise source wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_product_smallness.out 2>&1` | PASS after adding lookup checks for the Theorem 9.15 product-smallness normwise source wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_27_GMatrix_opNorm2_lt_one_of_product_lt_one`, `higham9_15_normwise_source_bound_of_G_split_min_factor_bound_opNorm_of_inverse_identities_product_lt`, `higham9_15_normwise_source_bound_of_normalized_linear_step_opNorm_of_inverse_identities_product_lt`, `higham9_15_normwise_source_bound_of_factorization_min_factor_bound_opNorm_of_matrix_inverse_identities_product_lt`, and `higham9_15_normwise_source_bound_of_factorization_min_factor_bound_opNorm_product_lt` | PASS; all five report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.15 product-smallness normwise wrapper update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.15 product-smallness code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 `Gtilde` normwise source wrapper family |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the Theorem 9.15 `Gtilde` normwise source wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_gtilde_normwise.out 2>&1` | PASS after adding lookup checks for the Theorem 9.15 `Gtilde` normwise source wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_15_normwise_source_bound_of_Gtilde_split_min_factor_bound_opNorm_of_inverse_identities`, `higham9_15_normwise_source_bound_of_Gtilde_split_min_factor_bound_opNorm_of_inverse_identities_product_lt`, `higham9_15_normwise_source_bound_of_factorization_Gtilde_min_factor_bound_opNorm_of_matrix_inverse_identities`, `higham9_15_normwise_source_bound_of_factorization_Gtilde_min_factor_bound_opNorm_of_matrix_inverse_identities_product_lt`, `higham9_15_normwise_source_bound_of_factorization_Gtilde_min_factor_bound_opNorm`, and `higham9_15_normwise_source_bound_of_factorization_Gtilde_min_factor_bound_opNorm_product_lt` | PASS; all six report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.15 `Gtilde` normwise source wrapper update; no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.15 `Gtilde` normwise code/lookup/report update |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 2992 jobs, after adding the Theorem 9.12 total-nonnegative exact-LU/growth package |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/split2_lookup_after_ch9_total_nonnegative_912.out 2>&1` | PASS after adding lookup checks for the Theorem 9.12 total-nonnegative exact-LU/growth declarations; redirected output has 317 lines |
| `lake env lean --stdin` with `#print axioms` for `higham9_12_totalNonnegative_exists_LUFactSpec_optimal_growth` and `higham9_12_totalNonnegative_exists_LUFactSpec_growthFactorEntry_le_one` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans and Chapter 13/14 code/lookup scan | PASS after the Theorem 9.12 total-nonnegative exact-LU/growth update; no matches and no temporary axiom/probe files remain |
| `git diff --check` | PASS after the Theorem 9.12 total-nonnegative exact-LU/growth code/lookup/report/log update |
| `lake build` | PASS, 3498 jobs, after the Theorem 9.12 total-nonnegative exact-LU/growth update; warnings only in pre-existing QR/Givens and FastMatMul modules |
| Theorem 9.12 total-nonnegative exact-LU/growth existential package (`higham9_12_totalNonnegative_exists_LUFactSpec_optimal_growth`, `higham9_12_totalNonnegative_exists_LUFactSpec_growthFactorEntry_le_one`) | `propext`, `Classical.choice`, `Quot.sound` |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the one-dimensional Theorem 9.15 normalized Schur base-case declarations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the Theorem 9.15 normalized Schur base-case declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_fin_one_base.out 2>&1` | PASS after adding lookup checks for the Theorem 9.15 normalized Schur base-case declarations |
| `lake env lean --stdin` with `#print axioms` for `higham9_15_frobNormRect_eq_zero_of_entries_zero`, `higham9_15_normalized_G_min_factor_bound_fin_one`, `higham9_15_normalized_Gtilde_min_factor_bound_fin_one`, `higham9_15_normalized_G_frobNorm_ratio_bound_fin_one`, and `higham9_15_normalized_Gtilde_frobNorm_ratio_bound_fin_one` | PASS; all five report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.15 normalized Schur base-case update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.15 normalized Schur base-case code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the zero-dimensional Theorem 9.15 normalized Schur base cases and the one-dimensional source-level product wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the zero-dimensional base cases and one-dimensional source-level product wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_base_source_wrappers.out 2>&1` | PASS after adding lookup checks for the zero-dimensional base cases and one-dimensional source-level product wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_15_normalized_G_min_factor_bound_fin_zero`, `higham9_15_normalized_Gtilde_min_factor_bound_fin_zero`, `higham9_15_normalized_G_frobNorm_ratio_bound_fin_zero`, `higham9_15_normalized_Gtilde_frobNorm_ratio_bound_fin_zero`, `higham9_15_normwise_source_bound_of_G_split_opNorm_of_inverse_identities_fin_one_product_lt`, and `higham9_15_normwise_source_bound_of_Gtilde_split_opNorm_of_inverse_identities_fin_one_product_lt` | PASS; all six report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the second Theorem 9.15 base/source wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the second Theorem 9.15 base/source wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 entrywise operator-2 norm support theorem |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the entrywise operator-2 norm support theorem |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_entry_opnorm.out 2>&1` | PASS after adding the lookup check for `higham9_15_abs_entry_le_opNorm2` |
| `lake env lean --stdin` with `#print axioms` for `higham9_15_abs_entry_le_opNorm2` | PASS; reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.15 entrywise operator-norm update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.15 entrywise operator-norm code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 zero-factor min-factor and ratio support family |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the zero-factor min-factor and ratio support family |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_zero_factor.out 2>&1` | PASS after adding lookup checks for the Theorem 9.15 zero-factor support family |
| `lake env lean --stdin` with `#print axioms` for `higham9_15_normalized_G_min_factor_bound_of_left_zero`, `higham9_15_normalized_G_min_factor_bound_of_right_zero`, `higham9_15_normalized_G_frobNorm_ratio_bound_of_left_zero`, `higham9_15_normalized_G_frobNorm_ratio_bound_of_right_zero`, `higham9_15_normalized_Gtilde_frobNorm_ratio_bound_of_left_zero`, and `higham9_15_normalized_Gtilde_frobNorm_ratio_bound_of_right_zero` | PASS; all six report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.15 zero-factor support update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.15 zero-factor code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 zero-factor source product wrappers for the `G` and `Gtilde` split endpoints |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the zero-factor source product wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_zero_source_wrappers.out 2>&1` | PASS after adding lookup checks for the four zero-factor source product wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_15_normwise_source_bound_of_G_split_left_zero_opNorm_of_inverse_identities_product_lt`, `higham9_15_normwise_source_bound_of_G_split_right_zero_opNorm_of_inverse_identities_product_lt`, `higham9_15_normwise_source_bound_of_Gtilde_split_left_zero_opNorm_of_inverse_identities_product_lt`, and `higham9_15_normwise_source_bound_of_Gtilde_split_right_zero_opNorm_of_inverse_identities_product_lt` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the zero-factor source product wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the zero-factor source product wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 zero-factor source product wrappers for the original `G` and `Gtilde` factorization endpoints |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the zero-factor original-factorization source wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_factorization_zero_wrappers.out 2>&1` | PASS after adding lookup checks for the four zero-factor original-factorization source wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_15_normwise_source_bound_of_factorization_left_zero_opNorm_product_lt`, `higham9_15_normwise_source_bound_of_factorization_right_zero_opNorm_product_lt`, `higham9_15_normwise_source_bound_of_factorization_Gtilde_left_zero_opNorm_product_lt`, and `higham9_15_normwise_source_bound_of_factorization_Gtilde_right_zero_opNorm_product_lt` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the zero-factor original-factorization source wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the zero-factor original-factorization source wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.14 SPD determinant-discharge actual triangular-solve wrapper |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the Theorem 9.14 SPD determinant-discharge wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_spd_det_wrapper.out 2>&1` | PASS after adding the lookup check for `higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_spd` |
| `lake env lean --stdin` with `#print axioms` for `higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_spd` | PASS; reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.14 SPD determinant-discharge wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.14 SPD determinant-discharge wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.12 SPD growth-factor denominator-discharge wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the Theorem 9.12 SPD growth-factor denominator-discharge wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_spd_growth_wrappers.out 2>&1` | PASS after adding lookup checks for `higham9_12_spd_tridiag_growthFactorEntry_le_one_of_spd`, `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_spd`, and `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_spd_recurrence` |
| `lake env lean --stdin` with `#print axioms` for `higham9_12_spd_tridiag_growthFactorEntry_le_one_of_spd`, `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_spd`, and `higham9_12_spd_tridiag_builder_growthFactorEntry_le_one_of_spd_recurrence` | PASS; all three report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.12 SPD growth-factor denominator-discharge wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.12 SPD growth-factor denominator-discharge wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.12 special-class determinant-denominator wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the Theorem 9.12 special-class determinant-denominator wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_912_det_denominator_wrappers.out 2>&1` | PASS after adding lookup checks for the six determinant-denominator wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_12_nonneg_lu_growthFactorEntry_le_one_of_det_ne_zero`, `higham9_12_mmatrix_lu_growthFactorEntry_le_one_of_det_ne_zero`, `higham9_12_sign_equiv_growthFactorEntry_le_one_of_det_ne_zero`, `higham9_6_growthFactorEntry_le_one_of_totalNonnegative_det_ne_zero_exists_hAmax`, `higham9_6_growthFactorEntry_and_noPivotReducedGrowthFactor_le_one_of_totalNonnegative_det_ne_zero_exists_hAmax`, and `higham9_12_totalNonnegative_exists_LUFactSpec_growthFactorEntry_le_one_exists_hAmax` | PASS; all six report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.12 special-class determinant-denominator wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.12 special-class determinant-denominator wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 `Gtilde` normalized linear-step ratio and source wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the Theorem 9.15 `Gtilde` normalized linear-step wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_gtilde_linear_wrappers.out 2>&1` | PASS after adding lookup checks for the three `Gtilde` normalized linear-step declarations |
| `lake env lean --stdin` with `#print axioms` for `higham9_15_normalized_Gtilde_frobNorm_ratio_bound_of_linear_step`, `higham9_15_normwise_source_bound_of_Gtilde_normalized_linear_step_opNorm_of_inverse_identities`, and `higham9_15_normwise_source_bound_of_Gtilde_normalized_linear_step_opNorm_of_inverse_identities_product_lt` | PASS; all three report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.15 `Gtilde` normalized linear-step wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.15 `Gtilde` normalized linear-step wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 source-oriented inverse-identity normalized linear-step wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the Theorem 9.15 source-oriented inverse-identity normalized linear-step wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_source_inverse_linear_wrappers.out 2>&1` | PASS after adding lookup checks for the four source-oriented inverse-identity normalized linear-step wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_15_normwise_source_bound_of_normalized_linear_step_opNorm_of_source_inverse_identities`, `higham9_15_normwise_source_bound_of_normalized_linear_step_opNorm_of_source_inverse_identities_product_lt`, `higham9_15_normwise_source_bound_of_Gtilde_normalized_linear_step_opNorm_of_source_inverse_identities`, and `higham9_15_normwise_source_bound_of_Gtilde_normalized_linear_step_opNorm_of_source_inverse_identities_product_lt` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.15 source-oriented inverse-identity normalized linear-step wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.15 source-oriented inverse-identity normalized linear-step wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Algorithm 9.2 rectangular literal rounded fold and absolute-budget certificate surfaces |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the rectangular literal fold and certificate surfaces |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_rect_doolittle_square_bridge.out 2>&1` | PASS after adding lookup checks for the rectangular literal fold definitions, certificate surfaces, constructor, square specialization bridge, and residual theorems |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_2_rectAbsBudgetCertificate_to_rectDenseLoopCertificate`, `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_source_budgets`, `higham9_2_rectAbsBudgetCertificate_to_squareAbsBudgetCertificate`, `higham9_2_rectFlDoolittleUEntry_residual_abs_le`, and `higham9_2_rectFlDoolittleLEntry_residual_abs_le` | PASS; all five report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Algorithm 9.2 rectangular literal fold and certificate update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain. Broader report-inclusive scans match only historical command strings in this report. |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Algorithm 9.2 rectangular literal fold/certificate code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the square-specialized rectangular dense-loop and Theorem 9.3 backward-error adapters |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the square-specialized rectangular Theorem 9.3 adapters |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_rect_square_backward_error_after_build.out 2>&1` | PASS after adding lookup checks for the square-specialized rectangular dense-loop, absolute-budget, and literal-source-budget backward-error adapters |
| `lake env lean --stdin` with `#print axioms` for `higham9_2_rectDenseLoopCertificate_to_squareDenseLoopCertificate`, `higham9_3_rectDenseLoopCertificate_square_backward_error`, `higham9_3_rectAbsBudgetCertificate_square_backward_error`, and `higham9_3_rectLiteralDoolittle_source_budgets_square_backward_error` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the square-specialized rectangular Theorem 9.3 adapter update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the square-specialized rectangular Theorem 9.3 adapter code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the SPD positive-`D L^T` tridiagonal recurrence wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the SPD tridiagonal recurrence wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_spd_tridiag_recurrence_wrappers.out 2>&1` | PASS after adding lookup checks for the SPD tridiagonal `h(u)` recurrence wrapper and `f(u)` actual triangular-solve recurrence wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_14_spd_tridiag_positive_DLT_source_h_bound_of_recurrence`, `higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_recurrence`, and `higham9_14_spd_tridiag_positive_DLT_source_f_bound_actual_triangular_solves_of_spd_recurrence` | PASS; all three report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the SPD tridiagonal recurrence wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the SPD tridiagonal recurrence wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the row-pivoted and complete-pivoted literal-source-budget Wilkinson wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the pivoted literal-source-budget Wilkinson wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_pivoted_literal_source_budgets.out 2>&1` | PASS after adding lookup checks for the dense-loop, absolute-budget, literal-source-budget, and exact-certificate pivoted Wilkinson wrappers |
| `lake env lean --stdin` with `#print axioms` for `higham9_5_wilkinson_source_bound_of_PermutedPartialPivotGEPPUTrace_literalSourceBudgets` and `higham9_5_wilkinson_source_bound_of_CompletePivotGECPUTrace_literalSourceBudgets` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the pivoted literal-source-budget Wilkinson wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the pivoted literal-source-budget Wilkinson wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the row-pivoted and complete-pivoted component-dominance, exact-product-margin, exact-product-numerator-margin, and exact-target-gap Wilkinson wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the pivoted dominance/margin Wilkinson wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_pivoted_dominance_margin_wrappers.out 2>&1` | PASS after adding lookup checks for the eight pivoted dominance/margin Wilkinson wrappers; redirected output has 56224 lines |
| `lake env lean --stdin` with `#print axioms` for the eight row-pivoted and complete-pivoted component-dominance, exact-product-margin, exact-product-numerator-margin, and exact-target-gap Wilkinson wrappers | PASS; all eight report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the pivoted dominance/margin Wilkinson wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the pivoted dominance/margin Wilkinson wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding `higham9_2_rowColPermutedMatrix_det_ne_zero`, the strengthened complete-pivoting trace-to-certificate theorem with `|L_ij| <= 1`, the complete-permuted exact-certificate growth bridge, and the trace-derived Theorem 9.5 solve wrapper |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the complete-pivot trace-to-exact-solve wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_complete_pivot_trace_solve.out 2>&1` | PASS after adding lookup checks for the complete-pivot trace-to-exact-solve declarations; redirected output has 56257 lines |
| `lake env lean --stdin` with `#print axioms` for `higham9_2_rowColPermutedMatrix_det_ne_zero`, `higham9_8_CompletePivotGECPUTrace_exists_CompletePermutedLUFactSpec_L_bound_maxEntryNorm_le`, `higham9_5_wilkinson_source_bound_of_CompletePermutedLUFactSpec_growth`, and `higham9_5_wilkinson_source_bound_exists_of_CompletePivotGECPUTrace` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the complete-pivot trace-to-exact-solve wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the complete-pivot trace-to-exact-solve code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the equation (9.16) rook-pivoting trace-to-exact-solve certificate theorem and Wilkinson perturbation wrapper |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the rook-pivot trace-to-exact-solve wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_rook_trace_solve.out 2>&1` | PASS after adding lookup checks for the rook-pivot trace-to-exact-solve declarations; redirected output has 56276 lines |
| `lake env lean --stdin` with `#print axioms` for `higham9_16_RookPivotGEUTrace_exists_CompletePermutedLUFactSpec_L_bound_maxEntryNorm_le` and `higham9_16_wilkinson_source_bound_exists_of_RookPivotGEUTrace` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the rook-pivot trace-to-exact-solve wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain. Broader report-inclusive scans match only historical command strings in this report. |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the rook-pivot trace-to-exact-solve code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the partial-pivot trailing-row Schur lemma, generic exact `PA = LU` growth bridge, trace-to-exact-certificate theorem, and trace-derived Theorem 9.5 solve wrapper |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the partial-pivot trace-to-exact-solve wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_partial_trace_solve.out 2>&1` | PASS after adding lookup checks for the partial-pivot trace-to-exact-solve declarations; redirected output has 56308 lines |
| `lake env lean --stdin` with `#print axioms` for `higham9_7_luFirstSchurComplement_trailingRowPerm`, `higham9_5_wilkinson_source_bound_of_PermutedLUFactSpec_growth`, `higham9_7_PartialPivotGEPPUTrace_exists_PermutedLUFactSpec_L_bound_maxEntryNorm_le`, and `higham9_5_wilkinson_source_bound_exists_of_PartialPivotGEPPUTrace` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the partial-pivot trace-to-exact-solve wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the partial-pivot trace-to-exact-solve code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding det-only exact solve wrappers for the partial-, complete-, and rook-pivoting trace-to-solve endpoints |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the pivoted det-only exact solve wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_pivoted_det_wrappers.out 2>&1` | PASS after adding lookup checks for the pivoted det-only exact solve wrappers; redirected output has 56346 lines |
| `lake env lean --stdin` with `#print axioms` for `higham9_5_wilkinson_source_bound_exists_of_PartialPivotGEPPUTrace_of_det_ne_zero`, `higham9_5_wilkinson_source_bound_exists_of_CompletePivotGECPUTrace_of_det_ne_zero`, and `higham9_16_wilkinson_source_bound_exists_of_RookPivotGEUTrace_of_det_ne_zero` | PASS; all three report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the pivoted det-only exact solve wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the pivoted det-only exact solve wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the upper-Hessenberg trace-to-partial-trace conversion and exact normwise solve wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the upper-Hessenberg exact trace-to-solve wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_hessenberg_exact_solve.out 2>&1` | PASS after adding lookup checks for the upper-Hessenberg exact trace-to-solve declarations; redirected output has 56371 lines |
| `lake env lean --stdin` with `#print axioms` for `higham9_10_HessenbergGEPPUTrace_to_PartialPivotGEPPUTrace`, `higham9_10_wilkinson_source_bound_exists_of_HessenbergGEPPUTrace`, and `higham9_10_wilkinson_source_bound_exists_of_det_ne_zero` | PASS; all three report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the upper-Hessenberg exact trace-to-solve wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the upper-Hessenberg exact trace-to-solve code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the sign-equivalence source-predicate bridge and Theorem 9.14 `IsSignEquiv` wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the sign-equivalence source-predicate bridge |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_sign_equiv_source_predicate.out 2>&1` | PASS after adding lookup checks for the `IsSignEquiv` bridge declarations; redirected output has 56412 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_12_sign_equiv_signDiag_witnesses`, `higham9_12_sign_equiv_optimal_growth_of_IsSignEquiv`, `higham9_12_sign_equiv_growthFactorEntry_le_one_of_IsSignEquiv`, `higham9_12_sign_equiv_growthFactorEntry_le_one_of_IsSignEquiv_det_ne_zero`, `higham9_14_sign_equiv_source_h_bound_of_IsSignEquiv_models`, and `higham9_14_sign_equiv_source_f_bound_actual_triangular_solves_of_IsSignEquiv` | PASS; all six report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the sign-equivalence source-predicate bridge update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the sign-equivalence source-predicate bridge code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Problem 9.9 det-only denominator wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the Problem 9.9 det-only denominator wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_problem99_det_wrappers.out 2>&1` | PASS after adding lookup checks for the Problem 9.9 det-only denominator wrappers; redirected output has 56438 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_infNorm_pos_of_det_ne_zero`, `higham_problem9_9_noPivotReducedGrowthFactor_le_one_of_nonnegative_LU_exists_hAmax`, `higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_absLU_infNorm_div_exists_hAmax`, and `higham_problem9_9_growthFactorEntry_le_one_add_card_mul_absLU_infNorm_div_exists_hAmax` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Problem 9.9 / equation (9.17) Skeel-condition composition wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the Problem 9.9 / equation (9.17) Skeel-condition composition wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_problem99_skeel_wrappers.out 2>&1` | PASS after adding lookup checks for the Problem 9.9 / equation (9.17) Skeel-condition composition wrappers; redirected output has 56447 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham_problem9_9_noPivotReducedGrowthFactor_le_one_add_card_mul_condSkeel_exists_hAmax` and `higham_problem9_9_growthFactorEntry_le_one_add_card_mul_condSkeel_exists_hAmax` | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Problem 9.6 principal-block denominator-discharge wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the Problem 9.6 principal-block denominator-discharge wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_problem96_principal_hamax_wrappers.out 2>&1` | PASS after adding lookup checks for the five Problem 9.6 principal-block/proper-leading positive-denominator wrappers |
| `lake env lean --stdin` with fully qualified `#print axioms` for the five Problem 9.6 principal-block/proper-leading positive-denominator wrappers | PASS; all five report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Problem 9.6 principal-block denominator-discharge wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Problem 9.6 principal-block denominator-discharge code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Lemma 9.6 source-constant denominator-discharge wrapper |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the Lemma 9.6 source-constant denominator-discharge wrapper |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_lemma96_source_constant_hamax_wrapper.out 2>&1` | PASS after adding the lookup check for `higham9_6_absLU_infNorm_le_source_constant_of_noPivotReducedGrowthFactor_exists_hAmax` |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_6_absLU_infNorm_le_source_constant_of_noPivotReducedGrowthFactor_exists_hAmax` | PASS; reports only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Lemma 9.6 source-constant denominator-discharge wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Lemma 9.6 source-constant denominator-discharge code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 source-inverse normalized Frobenius, split/min-factor, and componentwise-majorant wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the Theorem 9.15 source-inverse split wrapper family |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_source_inverse_split_wrappers.out 2>&1` | PASS after adding lookup checks for the ten Theorem 9.15 source-inverse split/majorant declarations |
| `lake env lean --stdin` with fully qualified `#print axioms` for the ten Theorem 9.15 source-inverse split/majorant declarations | PASS; all ten report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.15 source-inverse split wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.15 source-inverse split wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 source-inverse zero-factor and one-dimensional product wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the source-inverse zero/one wrapper family |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_source_inverse_zero_one_wrappers.out 2>&1` | PASS after adding lookup checks for the six source-inverse zero-factor and one-dimensional declarations; redirected output has 56846 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the six Theorem 9.15 source-inverse zero-factor and one-dimensional declarations | PASS; all six report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Theorem 9.15 source-inverse zero/one wrapper update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the Theorem 9.15 source-inverse zero/one wrapper code/lookup/report update |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the no-pivot and indexed pivoting growth-family source layer |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the growth-family source layer |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_growth_family_index.out 2>&1` | PASS after adding lookup checks for the no-pivot and indexed pivoting growth-family declarations; redirected output has 56875 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the ten theorem-level growth-family declarations | PASS; all ten report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the growth-family source-layer update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |
| `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter9_formalization_report.md` | PASS after the growth-family source-layer code/lookup/report update |

## 2026-06-28 Theorem 9.15 Principal-Block Schur Support

Added the top-left principal-block support layer for the normalized Barrlund-Sun
Schur-induction route. The new declarations are:

- `higham9_15_initBlock`
- `higham9_15_strictLower_init`
- `higham9_15_upper_init`
- `higham9_15_opNorm2_init_le`
- `higham9_15_opNorm2_init_lt_one_of_lt_one`
- `higham9_15_normalized_G_init_factorization_matrix`
- `higham9_15_normalized_Gtilde_init_factorization_matrix`
- `higham9_15_normalized_G_init_frobNorm_ratio_bound_of_min_factor_bound`
- `higham9_15_normalized_Gtilde_init_frobNorm_ratio_bound_of_min_factor_bound`

This proves that the top-left principal block inherits triangular support, the
strict-contraction hypothesis, and the `I + G` / `I - Gtilde` normalized
factorizations. It also packages the principal-block ratio handoff from a
block-level min-factor induction hypothesis. This advances the formal
Schur-induction scaffold but does not yet close the full Barrlund-Sun
min-factor theorem or the spectral-radius majorant theorem.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 principal-block Schur support layer |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the principal-block Schur support layer |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_init_schur_support.out 2>&1` | PASS after adding lookup checks for the nine principal-block Schur support declarations; redirected output has 56910 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the eight theorem-level principal-block Schur support declarations | PASS; all eight report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the principal-block Schur support update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |

## 2026-06-28 Theorem 9.15 Principal-Block Frobenius Border Support

Extended the same Schur-induction scaffold with Frobenius and triangular-border
support for the top-left principal block. The new declarations are:

- `higham9_15_frobNormRect_initBlock_le`
- `higham9_15_strictLower_lastColumn_zero`
- `higham9_15_upper_lastRow_init_zero`
- `higham9_15_upper_firstColumn_tail_zero`
- `higham9_15_frobNormSqRect_block_lastColumn_zero`
- `higham9_15_frobNormRect_block_lastColumn_zero_le`
- `higham9_15_strictLower_frobNormRect_le_init_lastRow`
- `higham9_15_upper_frobNormRect_le_init_lastColumn_diag`

This supplies the local Frobenius bookkeeping needed by an eventual
dimension-step proof: strict-lower normalized factors split into their
top-left principal block plus final-row initial vector, while upper normalized
factors split into their top-left principal block plus final-column/diagonal
border terms. The full min-factor induction and spectral-radius majorant
theorems remain open.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 principal-block Frobenius border support layer |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the principal-block Frobenius border support layer |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_init_frob_border_support.out 2>&1` | PASS after adding lookup checks for the eight Frobenius/border support declarations; redirected output has 56932 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the eight Frobenius/border support declarations | PASS; all eight report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the Frobenius/border support update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |

## 2026-06-28 Theorem 9.15 Normalized Border Entry Equations

Added entrywise equations extracting the final-row, final-column, and final
diagonal border terms from the normalized split identities:

- `higham9_15_normalized_G_lastRow_init_eq`
- `higham9_15_normalized_G_lastColumn_init_eq`
- `higham9_15_normalized_G_lastDiag_eq`
- `higham9_15_normalized_Gtilde_lastRow_init_eq`
- `higham9_15_normalized_Gtilde_lastColumn_init_eq`
- `higham9_15_normalized_Gtilde_lastDiag_eq`

These equations connect the new Frobenius border estimates to the residual
matrices `G - X*Y` and `Gtilde + X*Y`. They are local support for the missing
dimension-step proof; they do not by themselves prove the Barrlund-Sun
min-factor theorem.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the normalized border-entry equations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the normalized border-entry equations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_border_entry_equations.out 2>&1` | PASS after adding lookup checks for the six normalized border-entry declarations; redirected output has 56956 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the six normalized border-entry declarations | PASS; all six report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the normalized border-entry update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |

## 2026-06-28 Theorem 9.15 Residual Border Norm Bounds

Converted the normalized border-entry equations into vector/entry norm bounds
against the corresponding residual Frobenius norm:

- `higham9_15_normalized_G_lastRow_init_vecNorm2_le_residual`
- `higham9_15_normalized_G_lastColumn_init_vecNorm2_le_residual`
- `higham9_15_normalized_G_lastDiag_abs_le_residual`
- `higham9_15_normalized_Gtilde_lastRow_init_vecNorm2_le_residual`
- `higham9_15_normalized_Gtilde_lastColumn_init_vecNorm2_le_residual`
- `higham9_15_normalized_Gtilde_lastDiag_abs_le_residual`

These are the norm-level border estimates needed to combine the principal-block
induction hypothesis with the full residual estimate. The missing global
min-factor theorem remains open.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the residual border norm bounds |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the residual border norm bounds |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_residual_border_norms.out 2>&1` | PASS after adding lookup checks for the six residual border-norm declarations; redirected output has 56980 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the six residual border-norm declarations | PASS; all six report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the residual border norm update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |

## 2026-06-28 Theorem 9.15 Combined Frobenius Induction Bounds

Added combined full-factor Frobenius inequalities that use the principal block
plus the residual border estimates:

- `higham9_15_normalized_G_frobNormRect_X_le_init_add_residual`
- `higham9_15_normalized_G_frobNormRect_Y_le_init_add_two_residual`
- `higham9_15_normalized_Gtilde_frobNormRect_X_le_init_add_residual`
- `higham9_15_normalized_Gtilde_frobNormRect_Y_le_init_add_two_residual`

These are proof-engineering support for the remaining Schur-induction step:
they reduce full-size Frobenius control to principal-block control plus the
already formalized residual bounds. They still stop short of the full
Barrlund-Sun min-factor theorem.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the combined Frobenius induction bounds |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the combined Frobenius induction bounds |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_combined_frob_induction_bounds.out 2>&1` | PASS after adding lookup checks for the four combined Frobenius induction declarations; redirected output has 56996 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the four combined Frobenius induction declarations | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the combined Frobenius induction update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |

## 2026-06-28 Theorem 9.15 Max-Frobenius Induction Handoff

Added max-form handoff inequalities for the normalized induction route:

- `higham9_15_normalized_G_max_frobNormRect_le_init_max_add_two_residual`
- `higham9_15_normalized_Gtilde_max_frobNormRect_le_init_max_add_two_residual`

They state that the full-size `max(||X||_F, ||Y||_F)` is bounded by the
top-left principal-block max plus twice the residual Frobenius norm. This is
another local scaffold for the missing dimension-step argument; it is not the
full Barrlund-Sun theorem.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the max-Frobenius induction handoff declarations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the max-Frobenius induction handoff declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_max_frob_induction_handoff.out 2>&1` | PASS after adding lookup checks for the two max-Frobenius induction handoff declarations; redirected output has 57007 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the two max-Frobenius induction handoff declarations | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans | PASS after the max-Frobenius induction handoff update; implementation, docs, and lookup scans had no matches and no temporary axiom/probe files remain |

## 2026-06-28 Theorem 9.15 Max-Frobenius Ratio Handoff

Added full max-Frobenius handoff inequalities that combine the
principal-block ratio hypothesis with the residual border estimates:

- `higham9_15_normalized_G_max_frobNormRect_le_init_ratio_add_two_residual_of_min_factor_bound`
- `higham9_15_normalized_Gtilde_max_frobNormRect_le_init_ratio_add_two_residual_of_min_factor_bound`

These package the current induction interface for the normalized `I + G` and
`I - Gtilde` splits. They reduce the full factor max to the principal-block
ratio plus twice the residual Frobenius norm, but still require the missing
global Barrlund-Sun residual/min-factor argument to close Theorem 9.15.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the max-Frobenius ratio handoff declarations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the max-Frobenius ratio handoff declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_max_frob_ratio_handoff.out 2>&1` | PASS after adding lookup checks for the two max-Frobenius ratio handoff declarations; redirected output has 57026 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the two max-Frobenius ratio handoff declarations | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the max-Frobenius ratio handoff update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Theorem 9.15 Full-Ratio Principal-Block Handoff

Added a scalar/norm bridge from the top-left principal-block ratio to the
full-matrix ratio and two normalized consequences:

- `higham9_15_initBlock_frobNorm_ratio_le`
- `higham9_15_normalized_G_max_frobNormRect_le_ratio_add_two_residual_of_init_min_factor_bound`
- `higham9_15_normalized_Gtilde_max_frobNormRect_le_ratio_add_two_residual_of_init_min_factor_bound`

The generic bridge reuses the existing denominator monotonicity lemma with the
principal-block Frobenius and operator-norm contraction theorems. The two
normalized consequences replace the principal-block ratio in the previous
handoff with the full `G`/`Gtilde` ratio, leaving only the residual term and
the still-open global Barrlund-Sun residual/min-factor argument.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the full-ratio principal-block handoff declarations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the full-ratio principal-block handoff declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_full_ratio_principal_block_handoff.out 2>&1` | PASS after adding lookup checks for the three full-ratio principal-block handoff declarations; redirected output has 57045 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the three full-ratio principal-block handoff declarations | PASS; all three report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the full-ratio principal-block handoff update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Theorem 9.15 Source Residual Handoffs

Added source-facing residual handoff wrappers for the normalized `G` and
`Gtilde` split routes:

- `higham9_15_normwise_source_bound_of_G_split_init_min_factor_bound_opNorm_of_inverse_identities`
- `higham9_15_normwise_source_bound_of_G_split_init_min_factor_bound_opNorm_of_inverse_identities_product_lt`
- `higham9_15_normwise_source_bound_of_Gtilde_split_init_min_factor_bound_opNorm_of_inverse_identities`
- `higham9_15_normwise_source_bound_of_Gtilde_split_init_min_factor_bound_opNorm_of_inverse_identities_product_lt`

These wrappers consume a principal-block min-factor hypothesis and produce the
printed operator-denominator relative perturbation bound with one explicit
normalized residual term. The product-smallness forms also convert the exact
`G` ratio to Higham's product denominator. The residual term remains the
visible obstruction to the full Barrlund-Sun source theorem.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the Theorem 9.15 source residual handoff wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the source residual handoff wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_source_residual_handoffs.out 2>&1` | PASS after adding lookup checks for the four source residual handoff declarations; redirected output has 57167 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the four source residual handoff declarations | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the source residual handoff update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Theorem 9.15 Source-Inverse Residual Handoffs

Added source-oriented inverse-identity variants of the residual handoff
wrappers:

- `higham9_15_normwise_source_bound_of_G_split_init_min_factor_bound_opNorm_of_source_inverse_identities`
- `higham9_15_normwise_source_bound_of_G_split_init_min_factor_bound_opNorm_of_source_inverse_identities_product_lt`
- `higham9_15_normwise_source_bound_of_Gtilde_split_init_min_factor_bound_opNorm_of_source_inverse_identities`
- `higham9_15_normwise_source_bound_of_Gtilde_split_init_min_factor_bound_opNorm_of_source_inverse_identities_product_lt`

These remove the need for callers to provide the opposite rectangular inverse
identities directly; the existing finite-square inverse adapters derive them
from the source identities `L⁻¹L = I` and `UU⁻¹ = I`.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the source-inverse residual handoff wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the source-inverse residual handoff wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_source_inverse_residual_handoffs.out 2>&1` | PASS after adding lookup checks for the four source-inverse residual handoff declarations; redirected output has 57289 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the four source-inverse residual handoff declarations | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the source-inverse residual handoff update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Theorem 9.15 Zero-Residual Source Handoffs

Added exact-residual specializations for the principal-block residual handoff
wrappers:

- `higham9_15_normwise_source_bound_of_G_split_init_min_factor_bound_opNorm_of_inverse_identities_of_residual_zero`
- `higham9_15_normwise_source_bound_of_G_split_init_min_factor_bound_opNorm_of_inverse_identities_product_lt_of_residual_zero`
- `higham9_15_normwise_source_bound_of_G_split_init_min_factor_bound_opNorm_of_source_inverse_identities_of_residual_zero`
- `higham9_15_normwise_source_bound_of_G_split_init_min_factor_bound_opNorm_of_source_inverse_identities_product_lt_of_residual_zero`
- `higham9_15_normwise_source_bound_of_Gtilde_split_init_min_factor_bound_opNorm_of_inverse_identities_of_residual_zero`
- `higham9_15_normwise_source_bound_of_Gtilde_split_init_min_factor_bound_opNorm_of_inverse_identities_product_lt_of_residual_zero`
- `higham9_15_normwise_source_bound_of_Gtilde_split_init_min_factor_bound_opNorm_of_source_inverse_identities_of_residual_zero`
- `higham9_15_normwise_source_bound_of_Gtilde_split_init_min_factor_bound_opNorm_of_source_inverse_identities_product_lt_of_residual_zero`

These close the exact normalized-factorization boundary case of the residual
scaffold: when `frobNormRect (G - X*Y) = 0` or
`frobNormRect (Gtilde + X*Y) = 0`, the source wrappers collapse to the exact
`G` ratio or the printed product denominator without the explicit residual
term. The full Barrlund-Sun Schur-induction/spectral-radius theorem remains
open for the nonzero residual case.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the zero-residual source handoff declarations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the zero-residual handoff declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_zero_residual_handoffs.out 2>&1` | PASS after adding lookup checks for the eight zero-residual handoff declarations; redirected output has 58221 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the eight zero-residual handoff declarations | PASS; all eight report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the zero-residual handoff update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Theorem 9.15 Zero-Residual No-`hmin` Handoffs

Strengthened the exact-residual branch by proving that a zero normalized
residual supplies the principal-block min-factor hypothesis:

- `higham9_15_normalized_G_init_min_factor_bound_of_residual_zero`
- `higham9_15_normalized_Gtilde_init_min_factor_bound_of_residual_zero`

The source wrappers below therefore no longer require callers to provide
`hmin` in the exact-residual case:

- `higham9_15_normwise_source_bound_of_G_split_init_residual_zero_opNorm_of_inverse_identities`
- `higham9_15_normwise_source_bound_of_G_split_init_residual_zero_opNorm_of_inverse_identities_product_lt`
- `higham9_15_normwise_source_bound_of_G_split_init_residual_zero_opNorm_of_source_inverse_identities`
- `higham9_15_normwise_source_bound_of_G_split_init_residual_zero_opNorm_of_source_inverse_identities_product_lt`
- `higham9_15_normwise_source_bound_of_Gtilde_split_init_residual_zero_opNorm_of_inverse_identities`
- `higham9_15_normwise_source_bound_of_Gtilde_split_init_residual_zero_opNorm_of_inverse_identities_product_lt`
- `higham9_15_normwise_source_bound_of_Gtilde_split_init_residual_zero_opNorm_of_source_inverse_identities`
- `higham9_15_normwise_source_bound_of_Gtilde_split_init_residual_zero_opNorm_of_source_inverse_identities_product_lt`

This closes the exact normalized-residual boundary more cleanly. The nonzero
residual branch still needs the full Barrlund-Sun Schur-induction theorem.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the zero-residual no-`hmin` handoff declarations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the zero-residual no-`hmin` declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_residual_zero_no_hmin.out 2>&1` | PASS after adding lookup checks for the ten zero-residual no-`hmin` declarations; redirected output has 58618 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the ten zero-residual no-`hmin` declarations | PASS; all ten report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the zero-residual no-`hmin` update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Theorem 9.15 Factorization Zero-Residual No-`hmin` Handoffs

Lifted the no-`hmin` exact-residual branch to the original factorization
equations:

- `higham9_15_normwise_source_bound_of_factorization_init_residual_zero_opNorm_of_matrix_inverse_identities`
- `higham9_15_normwise_source_bound_of_factorization_init_residual_zero_opNorm_of_matrix_inverse_identities_product_lt`
- `higham9_15_normwise_source_bound_of_factorization_init_residual_zero_opNorm`
- `higham9_15_normwise_source_bound_of_factorization_init_residual_zero_opNorm_product_lt`
- `higham9_15_normwise_source_bound_of_factorization_Gtilde_init_residual_zero_opNorm_of_matrix_inverse_identities`
- `higham9_15_normwise_source_bound_of_factorization_Gtilde_init_residual_zero_opNorm_of_matrix_inverse_identities_product_lt`
- `higham9_15_normwise_source_bound_of_factorization_Gtilde_init_residual_zero_opNorm`
- `higham9_15_normwise_source_bound_of_factorization_Gtilde_init_residual_zero_opNorm_product_lt`

These wrappers derive the normalized split identity from the source
factorization equations, then apply the exact-residual no-`hmin` source
handoff. The nonzero residual branch remains the open Barrlund-Sun
Schur-induction target.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the factorization zero-residual no-`hmin` declarations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the factorization zero-residual no-`hmin` declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_factorization_residual_zero_no_hmin.out 2>&1` | PASS after adding lookup checks for the eight factorization zero-residual no-`hmin` declarations; redirected output has 58760 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the eight factorization zero-residual no-`hmin` declarations | PASS; all eight report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the factorization zero-residual no-`hmin` update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Theorem 9.15 Factorization Residual Handoffs

Added factorization-level principal-block residual handoff wrappers for both
the normwise `G` and signed `Gtilde` routes:

- `higham9_15_normwise_source_bound_of_factorization_init_min_factor_bound_opNorm_of_matrix_inverse_identities`
- `higham9_15_normwise_source_bound_of_factorization_init_min_factor_bound_opNorm_of_matrix_inverse_identities_product_lt`
- `higham9_15_normwise_source_bound_of_factorization_init_min_factor_bound_opNorm`
- `higham9_15_normwise_source_bound_of_factorization_init_min_factor_bound_opNorm_product_lt`
- `higham9_15_normwise_source_bound_of_factorization_Gtilde_init_min_factor_bound_opNorm_of_matrix_inverse_identities`
- `higham9_15_normwise_source_bound_of_factorization_Gtilde_init_min_factor_bound_opNorm_of_matrix_inverse_identities_product_lt`
- `higham9_15_normwise_source_bound_of_factorization_Gtilde_init_min_factor_bound_opNorm`
- `higham9_15_normwise_source_bound_of_factorization_Gtilde_init_min_factor_bound_opNorm_product_lt`

These wrappers start from the original exact factorization equations and derive
the normalized split identities internally before applying the principal-block
residual handoff. They keep the principal-block min-factor hypothesis and the
explicit residual term visible; the full Barrlund-Sun Schur-induction theorem
for eliminating those conditions remains open.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the factorization-level residual handoff declarations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the factorization residual handoff declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_factorization_residual_handoffs.out 2>&1` | PASS after adding lookup checks for the eight factorization residual handoff declarations; redirected output has 58387 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the eight factorization residual handoff declarations | PASS; all eight report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the factorization residual handoff update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Theorem 9.15 Normalized Residual Identities

Added named residual identities for the normalized `G` and `Gtilde` split
equations:

- `higham9_15_normalized_G_residual_eq_add`
- `higham9_15_normalized_G_residual_frobNormRect_eq_add`
- `higham9_15_normalized_Gtilde_residual_eq_add`
- `higham9_15_normalized_Gtilde_residual_frobNormRect_eq_add`

These expose the algebraic consequences `G - X * Y = X + Y` and
`Gtilde + X * Y = X + Y` from the normalized factorizations, plus direct
Frobenius-norm rewrites. The existing split lemmas now use these named
identities internally, which leaves a cleaner interface for the remaining
Schur-induction proof surface.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the normalized residual identity declarations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the normalized residual identity declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_residual_identities.out 2>&1` | PASS after adding lookup checks for the four normalized residual identity declarations; redirected output has 57298 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the four normalized residual identity declarations | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the normalized residual identity update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Rectangular Doolittle Component-Dominance Verification

Verified the rectangular component-dominance budget handoff increment.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the rectangular work terms and component-dominance compression lemmas |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the rectangular component-dominance handoff |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_rect_component_dominance.out 2>&1` | PASS after adding lookup checks for the rectangular work terms, compression lemmas, and component-dominance certificate constructor; redirected output has 57377 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_2_rectDoolittleUWorkAbs`, `higham9_2_rectDoolittleLWorkAbs`, `higham9_2_rectDoolittleUAbsBudget_le_compression_of_component_dominance`, `higham9_2_rectDoolittleLAbsBudget_le_compression_of_component_dominance`, and `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_component_dominance` | PASS; all five report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the rectangular component-dominance handoff update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Rectangular Doolittle Exact-Product Margin Verification

Verified the rectangular exact-product and numerator-margin budget handoff
increment.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the rectangular exact-product margin wrappers and certificate constructors |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the rectangular exact-product margin handoff |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_rect_exact_product_margins.out 2>&1` | PASS after adding lookup checks for the rectangular exact-product margin wrappers and constructors; redirected output has 57448 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_2_rectDoolittleUWorkAbs_le_of_exact_product_margin`, `higham9_2_rectDoolittleUProductAbs_le_of_exact_product_margin`, `higham9_2_rectDoolittleLWorkAbs_le_of_exact_product_margin`, `higham9_2_rectDoolittleLProductAbs_le_of_exact_product_margin`, `higham9_2_rectDoolittleLNumeratorAbs_le_of_exact_product_numerator_margin`, `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_margins`, and `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_product_numerator_margins` | PASS; all seven report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the rectangular exact-product margin update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Rectangular Doolittle Exact-Target Gap Verification

Verified the rectangular exact-target gap handoff increment.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the rectangular exact-target vocabulary and gap-to-margin handoff |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the rectangular exact-target gap handoff |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_rect_exact_target_gaps.out 2>&1` | PASS after adding lookup checks for the rectangular exact-target definitions, gap-to-margin wrappers, and certificate constructor; redirected output has 57515 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_2_rectDoolittleUExactTarget`, `higham9_2_rectDoolittleLExactTarget`, `higham9_2_rectDoolittleUExactTargetResidualBudget`, `higham9_2_rectDoolittleLExactTargetNumeratorResidualBudget`, `higham9_2_rectDoolittleLExactTargetEntryResidualBudget`, `higham9_2_rectDoolittleUExactProductMargin_of_exactTarget_gap`, `higham9_2_rectDoolittleLExactProductMargin_of_exactTarget_gap`, `higham9_2_rectDoolittleLExactProductNumeratorMargin_of_exactTarget_gap`, and `higham9_2_rectAbsBudgetCertificate_of_literal_doolittle_exact_target_gaps` | PASS; all nine report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the rectangular exact-target gap update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Rectangular Doolittle Backward-Error Variant Verification

Verified the direct Theorem 9.3 endpoint variants for the rectangular literal
budget routes.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the rectangular literal backward-error endpoint variants |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the endpoint variants |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_rect_backward_variants.out 2>&1` | PASS after adding lookup checks for the four endpoint variants; redirected output has 57620 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_3_rectLiteralDoolittle_componentDominance_backward_error`, `higham9_3_rectLiteralDoolittle_exactProductMargins_backward_error`, `higham9_3_rectLiteralDoolittle_exactProductNumeratorMargins_backward_error`, and `higham9_3_rectLiteralDoolittle_exactTargetGaps_backward_error` | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the rectangular endpoint variant update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Square Doolittle Backward-Error Endpoint Verification

Verified the direct Theorem 9.3 endpoint wrappers for the square literal
Doolittle budget routes.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the square literal backward-error endpoint wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the square endpoint wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_square_backward_endpoints.out 2>&1` | PASS after adding lookup checks for the five square endpoint wrappers; redirected output has 57710 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for `higham9_3_literalDoolittle_source_budgets_backward_error`, `higham9_3_literalDoolittle_componentDominance_backward_error`, `higham9_3_literalDoolittle_exactProductMargins_backward_error`, `higham9_3_literalDoolittle_exactProductNumeratorMargins_backward_error`, and `higham9_3_literalDoolittle_exactTargetGaps_backward_error` | PASS; all five report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the square endpoint wrapper update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Theorem 9.15 G Componentwise Source Wrappers

Added source-facing componentwise wrappers for the normalized `G` split route,
matching the existing `Gtilde` source surface:

- `higham9_15_componentwise_source_bound_of_G_split_majorant_of_inverse_identities`
- `higham9_15_componentwise_source_bound_of_G_split_majorant_of_source_inverse_identities`
- `higham9_15_componentwise_source_bound_of_factorization_G_majorant_of_matrix_inverse_identities`
- `higham9_15_componentwise_source_bound_of_factorization_G_majorant`

These wrappers expose the already-formalized `I + G = (I + X)(I + Y)`
componentwise majorant at the original-variable level. They keep the
spectral-radius/Schur majorant as an explicit hypothesis and do not claim the
remaining Barrlund--Sun induction theorem.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the `G` componentwise source wrapper block |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the `G` componentwise wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_g_componentwise_wrappers.out 2>&1` | PASS after adding lookup checks for the four `G` componentwise wrapper declarations; redirected output has 57776 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the four `G` componentwise wrapper declarations | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the `G` componentwise wrapper update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Theorem 9.14 `f(u)` Model Wrappers

Added direct model-consuming `f(u)|A|` wrappers for the optimal-growth
Theorem 9.14 classes:

- `higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_models`
- `higham9_14_spd_tridiag_positive_DLT_source_f_bound_of_recurrence`
- `higham9_14_nonnegative_lu_source_f_bound_of_models`
- `higham9_14_mmatrix_lu_source_f_bound_of_models`
- `higham9_14_sign_equiv_source_f_bound_of_models`
- `higham9_14_sign_equiv_source_f_bound_of_IsSignEquiv_models`
- `higham9_14_totalNonnegative_exists_source_f_bound_of_models`

These are the equation-(9.22) counterparts to the existing `h(u)` model
wrappers and actual-triangular-solve `f(u)` packages. They reuse the exact
`|L||U| = |A|` optimal-growth comparisons and leave the equation (9.20)/(9.21)
perturbation models explicit.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the seven Theorem 9.14 `f(u)` model wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the `f(u)` model wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_914_fu_model_wrappers.out 2>&1` | PASS after adding lookup checks for the seven `f(u)` model wrapper declarations; redirected output has 57852 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the seven `f(u)` model wrapper declarations | PASS; all seven report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the `f(u)` model wrapper update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Theorem 9.14 `h(u)` Actual-Solve Wrappers

Added actual-triangular-solve wrappers for the final Theorem 9.14 `h(u)|A|`
bound:

- `higham9_14_source_h_bound_of_LUBackwardError_fl_triangular_solves_gamma_le`
- `higham9_14_source_h_bound_of_LUFactSpec_fl_triangular_solves_gamma_le`
- `higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves`
- `higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves_of_spd`
- `higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves_of_recurrence`
- `higham9_14_spd_tridiag_positive_DLT_source_h_bound_actual_triangular_solves_of_spd_recurrence`
- `higham9_14_nonnegative_lu_source_h_bound_actual_triangular_solves`
- `higham9_14_mmatrix_lu_source_h_bound_actual_triangular_solves`
- `higham9_14_sign_equiv_source_h_bound_actual_triangular_solves`
- `higham9_14_sign_equiv_source_h_bound_actual_triangular_solves_of_IsSignEquiv`
- `higham9_14_totalNonnegative_exists_source_h_bound_actual_triangular_solves`

The generic bridges instantiate equation (9.20) from an LU backward-error
certificate or exact `LUFactSpec` and equation (9.21) from the actual
`fl_forwardSub`/`fl_backSub` routines.  The class endpoints reuse the existing
exact-growth comparisons `|L||U| <= |A|`, so they expose the printed final
`h(u)|A|` source bound while leaving the rounded LU factorization trace as a
separate upstream certificate.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the eleven Theorem 9.14 `h(u)` actual-solve wrappers |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the `h(u)` actual-solve wrappers |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_914_hu_actual_solve_wrappers.out 2>&1` | PASS after adding lookup checks for the eleven `h(u)` actual-solve wrapper declarations; redirected output has 57969 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the eleven `h(u)` actual-solve wrapper declarations | PASS; all eleven report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus `git diff --check` | PASS after the `h(u)` actual-solve wrapper update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Theorem 9.15 Zero-Residual Factor/Smallness Discharge

Added reusable exact zero-residual support lemmas for factor vanishing:

- `higham9_15_entries_zero_of_frobNormRect_eq_zero`
- `higham9_15_normalized_G_split_entries_zero_of_residual_zero`
- `higham9_15_normalized_Gtilde_split_entries_zero_of_residual_zero`

Then extended the same exact branch through the normalized perturbation and
ratio surfaces:

- `higham9_15_opNorm2_eq_zero_of_entries_zero`
- `higham9_15_normalized_G_entries_zero_of_residual_zero`
- `higham9_15_normalized_Gtilde_entries_zero_of_residual_zero`
- `higham9_15_normalized_G_opNorm2_lt_one_of_residual_zero`
- `higham9_15_normalized_Gtilde_opNorm2_lt_one_of_residual_zero`
- `higham9_15_normalized_G_frobNorm_ratio_bound_of_residual_zero`
- `higham9_15_normalized_Gtilde_frobNorm_ratio_bound_of_residual_zero`

The first group closes the reverse direction of the rectangular Frobenius zero
criterion and proves that an exact zero residual forces both normalized
triangular factors to be entrywise zero. The second group derives `G = 0` or
`Gtilde = 0`, discharges the strict `opNorm2 < 1` side condition, and exposes
the normalized ratio handoff without separate smallness or min-factor
hypotheses. This strengthens the exact-residual support layer only; the
nonzero Barrlund-Sun Schur-induction/spectral-radius branch remains open.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the zero-residual factor/smallness discharge lemmas |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the zero-residual factor/smallness discharge lemmas |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_residual_zero_factor_smallness.out 2>&1` | PASS after adding lookup checks for the ten zero-residual factor/smallness declarations; redirected output has 58795 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the ten zero-residual factor/smallness declarations | PASS; all ten report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus repo-local `git diff --check` and dev-log whitespace/conflict-marker scans | PASS after the zero-residual factor/smallness update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, repo-local whitespace diff check passed, and the non-repo dev log has no trailing whitespace or conflict markers |

## 2026-06-28 Theorem 9.15 Zero-Residual No-Smallness Handoffs

Lifted the exact zero-residual smallness discharge through the source handoff
surfaces:

- `higham9_15_normwise_source_bound_of_G_split_init_residual_zero_opNorm_of_inverse_identities_no_smallness`
- `higham9_15_normwise_source_bound_of_G_split_init_residual_zero_opNorm_of_source_inverse_identities_no_smallness`
- `higham9_15_normwise_source_bound_of_factorization_init_residual_zero_opNorm_of_matrix_inverse_identities_no_smallness`
- `higham9_15_normwise_source_bound_of_factorization_init_residual_zero_opNorm_no_smallness`
- `higham9_15_normwise_source_bound_of_Gtilde_split_init_residual_zero_opNorm_of_inverse_identities_no_smallness`
- `higham9_15_normwise_source_bound_of_Gtilde_split_init_residual_zero_opNorm_of_source_inverse_identities_no_smallness`
- `higham9_15_normwise_source_bound_of_factorization_Gtilde_init_residual_zero_opNorm_of_matrix_inverse_identities_no_smallness`
- `higham9_15_normwise_source_bound_of_factorization_Gtilde_init_residual_zero_opNorm_no_smallness`

These wrappers remove the explicit `opNorm2 G < 1`/`opNorm2 Gtilde < 1`
hypothesis from the exact residual-zero branch. The split-level wrappers derive
operator smallness from the zero-residual factor-vanishing lemmas; the
factorization-level wrappers derive the normalized split identities from the
original exact factorization equations and then delegate to those split
wrappers. The nonzero-residual Barrlund-Sun Schur-induction/spectral-radius
branch remains open.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the eight zero-residual no-smallness handoffs |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the no-smallness handoffs |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_residual_zero_no_smallness.out 2>&1` | PASS after adding lookup checks for the eight no-smallness declarations; redirected output has 58964 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the eight no-smallness declarations | PASS; all eight report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus repo-local `git diff --check` and dev-log whitespace/conflict-marker scans | PASS after the no-smallness update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, repo-local whitespace diff check passed, and the non-repo dev log has no trailing whitespace or conflict markers |

## 2026-06-28 Theorem 9.15 Exact Source-Perturbation Vanishing

Added the source-level exact-zero consequence of the zero-residual branch:

- `higham9_15_source_perturbations_zero_of_inverse_normalized_zero`
- `higham9_15_source_perturbations_zero_of_G_split_residual_zero_of_inverse_identities`
- `higham9_15_source_perturbations_zero_of_G_split_residual_zero_of_source_inverse_identities`
- `higham9_15_source_perturbations_zero_of_Gtilde_split_residual_zero_of_inverse_identities`
- `higham9_15_source_perturbations_zero_of_Gtilde_split_residual_zero_of_source_inverse_identities`
- `higham9_15_source_perturbations_zero_of_factorization_G_residual_zero_of_matrix_inverse_identities`
- `higham9_15_source_perturbations_zero_of_factorization_G_residual_zero`
- `higham9_15_source_perturbations_zero_of_factorization_Gtilde_residual_zero_of_matrix_inverse_identities`
- `higham9_15_source_perturbations_zero_of_factorization_Gtilde_residual_zero`

The generic helper proves that if the inverse-normalized lower and upper
perturbations are both entrywise zero, then the source perturbations `Delta L`
and `Delta U` vanish entrywise under the inverse identities. The `G` and
`Gtilde` split/factorization wrappers obtain those normalized zeros from the
exact full residual-zero hypotheses proved earlier. This closes the source
vanishing surface of the exact branch; it does not address the nonzero-residual
Schur-induction/spectral-radius theorem.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the nine exact source-perturbation vanishing declarations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the exact source-zero declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_source_perturbations_zero.out 2>&1` | PASS after adding lookup checks for the nine exact source-zero declarations; redirected output has 59127 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the nine exact source-zero declarations | PASS; all nine report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus repo-local `git diff --check` and dev-log whitespace/conflict-marker scans | PASS after the exact source-zero update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, repo-local whitespace diff check passed, and the non-repo dev log has no trailing whitespace or conflict markers |

## 2026-06-28 Theorem 9.15 Exact Zero Normwise Source Bound

Added the zero-residual branch as a direct printed-left-hand-side bound:

- `higham9_15_normwise_source_zero_bound_of_source_perturbations_zero`
- `higham9_15_normwise_source_zero_bound_of_G_split_residual_zero_of_inverse_identities`
- `higham9_15_normwise_source_zero_bound_of_G_split_residual_zero_of_source_inverse_identities`
- `higham9_15_normwise_source_zero_bound_of_Gtilde_split_residual_zero_of_inverse_identities`
- `higham9_15_normwise_source_zero_bound_of_Gtilde_split_residual_zero_of_source_inverse_identities`
- `higham9_15_normwise_source_zero_bound_of_factorization_G_residual_zero_of_matrix_inverse_identities`
- `higham9_15_normwise_source_zero_bound_of_factorization_G_residual_zero`
- `higham9_15_normwise_source_zero_bound_of_factorization_Gtilde_residual_zero_of_matrix_inverse_identities`
- `higham9_15_normwise_source_zero_bound_of_factorization_Gtilde_residual_zero`

These results turn the exact source-perturbation vanishing consequences into
`max (||Delta L||_F / ||L||_2) (||Delta U||_F / ||U||_2) <= 0`, with no
separate positivity or smallness assumptions on the denominators. This is only
the exact residual-zero branch; the nonzero-residual Barrlund-Sun theorem
remains open.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the nine exact zero normwise source-bound declarations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the exact zero-bound declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_normwise_source_zero_bound.out 2>&1` | PASS after adding lookup checks for the nine exact zero-bound declarations; redirected output has 59289 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the nine exact zero-bound declarations | PASS; all nine report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus repo-local `git diff --check` and dev-log whitespace/conflict-marker scans | PASS after the exact zero-bound update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, repo-local whitespace diff check passed, and the non-repo dev log has no trailing whitespace or conflict markers |

## 2026-06-28 Theorem 9.15 Linear-Step Min-Factor Exposure

Added named normalized linear-step bridges for the remaining Barrlund--Sun
Schur-induction route:

- `higham9_15_normalized_G_linear_step_of_min_factor_bound`
- `higham9_15_normalized_Gtilde_linear_step_of_min_factor_bound`

These theorems expose the transition from the already-formalized quadratic
Frobenius split step to the linearized step consumed by the ratio theorem,
assuming the min-factor control. The existing ratio theorems now reuse these
lemmas directly. This is proof-engineering support for the nonzero-residual
branch; it does not prove the missing Schur-induction/spectral-radius theorem.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the two linear-step min-factor declarations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the linear-step min-factor declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_linear_step_min_factor.out 2>&1` | PASS after adding lookup checks for the two declarations; redirected output has 59298 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the two linear-step declarations | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder scans | PASS after the linear-step update; implementation, docs, and lookup scans had no matches |

## 2026-06-28 Theorem 9.15 Principal-Block Linear-Step Exposure

Added the top-left principal-block companions for the normalized linear-step
bridges:

- `higham9_15_normalized_G_init_linear_step_of_min_factor_bound`
- `higham9_15_normalized_Gtilde_init_linear_step_of_min_factor_bound`

These expose the exact recursive form used by the Schur-induction scaffold:
the principal block inherits the normalized split and triangular support, and a
principal-block min-factor hypothesis gives the linearized step on that block.
The full nonzero-residual Barrlund--Sun Schur-induction/spectral-radius theorem
remains open.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the two principal-block linear-step declarations |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the principal-block linear-step declarations |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_init_linear_step_min_factor.out 2>&1` | PASS after adding lookup checks for the two declarations; redirected output has 59318 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the two principal-block linear-step declarations | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder scans | PASS after the principal-block linear-step update; implementation, docs, and lookup scans had no matches |

## 2026-06-28 Theorem 9.15 Principal-Block Linear Residual Handoff

Added full-matrix residual handoffs that take the principal-block linear step
directly:

- `higham9_15_normalized_G_max_frobNormRect_le_ratio_add_two_residual_of_init_linear_step`
- `higham9_15_normalized_Gtilde_max_frobNormRect_le_ratio_add_two_residual_of_init_linear_step`

The older principal-block min-factor residual handoffs now delegate through
these linear-step versions. This makes the remaining Schur-induction target
explicit at the recursive handoff boundary: prove the principal-block
linearized step, then the already-formalized residual machinery gives the full
`G` or `Gtilde` ratio plus the nonlinear residual term. The full
nonzero-residual Barrlund--Sun theorem remains open.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the two principal-block linear residual handoffs |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the residual handoffs |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_init_linear_step_residual_handoff.out 2>&1` | PASS after adding lookup checks for the two declarations; redirected output has 59338 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the two residual handoff declarations | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder scans | PASS after the residual-handoff update; implementation, docs, and lookup scans had no matches |

## 2026-06-28 Theorem 9.15 Source Linear-Step Residual Handoffs

Added source-facing split wrappers that consume the principal-block linearized
step directly:

- `higham9_15_normwise_source_bound_of_G_split_init_linear_step_opNorm_of_inverse_identities`
- `higham9_15_normwise_source_bound_of_Gtilde_split_init_linear_step_opNorm_of_inverse_identities`

These wrappers lift the normalized residual handoffs to the printed
operator-denominator source surface under explicit inverse identities.  They
expose the exact recursive Schur-induction boundary as a linearized-step
hypothesis and avoid routing source callers through the older min-factor
interface.  They do not prove the remaining nonzero-residual Barrlund--Sun
Schur-induction/spectral-radius theorem.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the two source linear-step residual handoffs |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the source linear-step residual handoffs |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_init_linear_step_source.out 2>&1` | PASS after adding lookup checks for the two declarations; redirected output has 79310 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the two source linear-step declarations | PASS; both report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus repo-local `git diff --check` | PASS after the source linear-step update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

## 2026-06-28 Theorem 9.15 Factorization Linear-Step Handoffs

Lifted the source split linear-step residual handoffs through the original
factorization equations:

- `higham9_15_normwise_source_bound_of_factorization_init_linear_step_opNorm_of_matrix_inverse_identities`
- `higham9_15_normwise_source_bound_of_factorization_init_linear_step_opNorm`
- `higham9_15_normwise_source_bound_of_factorization_Gtilde_init_linear_step_opNorm_of_matrix_inverse_identities`
- `higham9_15_normwise_source_bound_of_factorization_Gtilde_init_linear_step_opNorm`

The matrix-inverse versions derive the normalized `I + G` and `I - Gtilde`
split identities from the original exact perturbed factorization equations.
The source-oriented versions assume only the displayed source inverse
identities and recover the opposite inverse identities internally.  The
remaining nonzero-residual Barrlund--Sun Schur-induction/spectral-radius
theorem is still explicit as the principal-block linearized-step hypothesis.

| Command | Result |
| --- | --- |
| `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter9.lean` | PASS after adding the four factorization linear-step handoffs |
| `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter9` | PASS, 3045 jobs, after refreshing the Chapter 9 module for the factorization linear-step handoffs |
| `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch9_lookup_915_factorization_linear_step.out 2>&1` | PASS after adding lookup checks for the four declarations; redirected output has 79403 lines |
| `lake env lean --stdin` with fully qualified `#print axioms` for the four factorization linear-step declarations | PASS; all four report only `propext`, `Classical.choice`, and `Quot.sound` |
| focused implementation/lookup placeholder/local-placeholder/temp-file scans plus repo-local `git diff --check` | PASS after the factorization linear-step update; implementation, docs, and lookup scans had no matches, no temporary axiom/probe files remain, and whitespace diff check passed |

No new `sorry`, `admit`, `axiom`, `unsafe`, or `opaque` appears in the touched Lean
files. Earlier default-stack lookup runs hit the unrelated pre-Chapter-9 IEEE
stack limit; the unifying pass verified the full lookup file with
`--tstack=65536` and also verified the new names directly in a focused lookup
file.

## GitHub Synchronization

- Local branch: `main`.
- Latest remote base integrated before the latest local push attempt:
  `origin/main` at `70936be`.  Earlier sync points in this recovery were
  `5d681d2` for the initial conflict recovery and `74351c1` for the first
  post-milestone pull-before-push merge.
- Merge/conflict resolution: local `main` merged `origin/main` in merge commit
  `be66eb4`; later clean pull-before-push merges integrated `origin/main` at
  `74351c1` into local merge commit `cf03c8c` and `origin/main` at `70936be`
  into local merge commit `ddfb358`.  The pre-merge dirty state was reapplied
  from `stash@{0}` and resolved conservatively, preserving both Split 2 work
  and newer upstream lookup/report rows while removing duplicate conflict
  artifacts.
- Milestone subject committed for the resolved sync state:
  `Split 2: recover ch09 proof-completion milestone after sync`.
- Latest local Split 2 proof-completion milestone:
  `Split 2: add ch09 source linear-step handoffs`.
- Post-`70936be` merge verification: `lake build
  LeanFpAnalysis.FP.Algorithms.HighamChapter9` passed; `lake env lean
  --tstack=65536 examples/LibraryLookup.lean >
  /tmp/ch9_lookup_915_init_linear_step_source_postmerge.out 2>&1` passed with
  79310 output lines; focused placeholder/conflict/temp-file scans and
  `git diff --check` passed.
- Push status: blocked by GitHub HTTPS credentials in this environment.  The
  command `git push origin main` failed, including after the `70936be` merge,
  with
  `fatal: could not read Username for 'https://github.com': No such device or address`;
  no `credential.helper` is configured and `gh` is not installed.

## Documentation

- Chapter report and full ledger: `chapter_splitting/reports/chapter9_formalization_report.md`.
- Public lookup docs updated: `docs/LIBRARY_LOOKUP.md`.
- Lookup example updated: `examples/LibraryLookup.lean`.
- Relevant dev logs updated in
  `/home/mymel/flare-bundle/dev-logs/2026-06-20-chapter9-proof-completion.md`
  `/home/mymel/flare-bundle/dev-logs/2026-06-21-split2-unifying-pass.md`, and
  `/home/mymel/flare-bundle/dev-logs/2026-06-22-chapter9-wilkinson-witness.md`.
