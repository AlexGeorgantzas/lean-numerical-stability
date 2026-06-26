# Chapter 8 Formalization Report

Date: 2026-06-26.
Source: `References/1.9780898718027.ch8.pdf`.
Appendix source read: `References/1.9780898718027.appa.pdf`.
Split contract: Split 2, Chapter 8.
Mode: proof-completion pass for Split 2.

`PREVIOUS_SPLITS = 1` in this pass.  The 2026-06-24 re-audit treats Split 1
as integrated and reusable.  Former Split 1-gate rows below are now current
Split 2 proof/API targets or concrete integration/API follow-ups.

## Summary

This pass kept the existing Chapter 8 module organization:

- source-facing wrappers in `LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`;
- triangular solve proofs in `TriangularSolve.lean` and `ForwardSub.lean`;
- comparison-matrix, inverse-bound, and M-matrix proofs in
  `TriangularForwardComparison.lean`, `InverseBounds.lean`, and `MMatrix.lean`.

Newly closed proof-facing work in this pass:

- `compMatrix_inv_upper_row_eq_ones`: exact algebraic recurrence behind
  Algorithm 8.13, `|u_ii| y_i = 1 + sum_{j>i} |u_ij| y_j`.
- `higham8_13_y` and `higham8_13_comparison_inverse_row_recurrence`: source
  Chapter 8 wrappers for that recurrence.
- `higham8_7_rowDiagMargin`,
  `higham8_7_scaledRowDiagMargin`,
  `higham8_7_scaledStrictRowDiagDominant_invInfNorm_le`,
  `higham8_7_strictRowDiagDominant_invInfNorm_le`, and
  `higham8_7_comparisonInverseOnes_infNorm_ge_inverseInfNorm`: source-facing
  Problem 8.7 inverse `∞`-norm wrappers, including the positive-diagonal
  scaling variant and the `M(U)⁻¹ e` corollary that rederives Algorithm 8.13's
  upper bound.
- `higham8_14_infNorm_lowerBound`: source-facing lower-bound part of (8.9) for
  the infinity norm, using the existing row-sum lower-bound theorem.
- `higham8_8_rankOne_singular_update`,
  `higham8_8_rankOne_singular_update_den_eq_zero`,
  `higham8_8_rankOne_singular_update_iff`,
  `higham8_8_rankOne_singular_update_abs_eq_inv_abs_inverse_entry`,
  `higham8_8_bestRankOneSingularUpdate_of_maxInverseEntry`, and
  `higham8_8_bestRankOneSingularUpdate_exists`: Problem 8.8(a) is now closed,
  including the exact iff criterion for singularity, the source magnitude
  formula `|α_ij| = |(A⁻¹)_{ji}|⁻¹`, and the Appendix A "best place" theorem
  from a maximal-entry position of `A⁻¹`.
- `higham8_9_comparisonMatrix_condAtSolution_eq`,
  `higham8_9_condAtSolution_le_comparisonMatrix`,
  `higham8_9_upperTriangular_condAtSolution_le_comparison_eq`, and
  `higham8_9_lowerTriangular_condAtSolution_le_comparison_eq`: source-facing
  Lemma 8.9 infinity-norm comparison-matrix condition-number wrappers reusing
  the integrated Chapter 7 `ch7SkeelCondAtSolutionInf` API.
- `higham8_4_stressUpperInvFormula_isInverse`: the displayed inverse formula
  for the stress family (8.4) is now certified as a genuine two-sided inverse.
- `higham8_12_ZMatrix`, `higham8_12_ZInvFormula`, and
  `higham8_12_ZInvFormula_isInverse`: source-facing `Z(U)` surface from
  Theorem 8.12 together with its exact inverse.
- `higham8_5_ZInvFormula_infNorm_eq` and `higham8_5_ZInvFormula_oneNorm_eq`:
  exact `∞`- and `1`-norm formulas for `Z(U)⁻¹`, closing Problem 8.5 in the
  source norm conventions.
- `higham8_5_ZInvFormula_opNorm2_le` and
  `higham8_14_ZInvFormula_oneNorm_upperBound`,
  `higham8_14_ZInvFormula_infNorm_upperBound`,
  `higham8_14_ZInvFormula_opNorm2_upperBound`: the source-style `Z(U)⁻¹`
  endpoint now covers `1`, `2`, and `∞`, including the `β ≤ 1` specialization
  used in the proof sketch of Theorem 8.14.
- `higham8_12_comparisonInv_le_WInv`,
  `higham8_12_WInv_le_ZInvFormula`,
  `higham8_12_infNorm_chain`, `higham8_12_oneNorm_chain`, and
  `higham8_12_opNorm2_chain`: the missing middle
  `M(U)⁻¹ ≤ W(U)⁻¹ ≤ Z(U)⁻¹` componentwise chain is now formalized, and it
  lifts to concrete real `∞`-, `1`-, and `2`-norm chains for `U⁻¹`,
  `M(U)⁻¹`, `W(U)⁻¹`, and `Z(U)⁻¹`.
- `higham8_nonneg_real_matrix_absVec_mul_norm`,
  `higham8_absolute_norm_vec_le_of_nonneg_le`, and
  `higham8_12_absolute_norm_vector_chain`: Theorem 8.12 now also has the
  fully packaged absolute-norm vector inequality
  `‖ |U⁻¹| |z| ‖ ≤ ‖M(U)⁻¹ |z|‖ ≤ ‖W(U)⁻¹ |z|‖ ≤ ‖Z(U)⁻¹ |z|‖`
  for arbitrary absolute complex vector norms.
- `higham8_14_oneNorm_lowerBound`, `higham8_14_oneNorm_upperBound`,
  `higham8_14_opNorm2_lowerBound`, `higham8_14_opNorm2_upperBound`, and
  `higham8_14_full_norm_chain`: Theorem 8.14 now has source-facing endpoint
  bounds for the `1`- and `2`-norms in addition to the existing `∞`-norm
  route and the exact `Z(U)⁻¹` endpoint formulas, and it now packages the
  full source `∞/1/2` norm chain using the minimum diagonal magnitude.
- `higham8_2_backSub_relative_infNorm_bound` and
  `higham8_2_forwardSub_relative_infNorm_bound`: fixed-order upper/lower
  substitution wrappers for equation (8.2), proving the source
  `cond(T,x) γ_n / (1 - cond(T) γ_n)` relative `∞`-norm bound for the
  repository's `fl_backSub` and `fl_forwardSub` routines.
- `higham8_2_comparisonInverseInfNormRatio_ge_lambda`,
  `higham8_2_comparisonInverseOneNormRatio_ge_lambda`, and
  `higham8_2_comparisonInverseRatios_arbitrarily_large`: Problem 8.2 is now
  closed from the Appendix A `3 × 3` witness, with exact inverse formulas for
  `T(λ)` and `M(T(λ))` proving both source norm ratios can be made
  arbitrarily large.
- `higham8_4_upperTriangularMMatrix_condAtSolution_le`: Problem 8.4 is now
  closed in the source upper-triangular M-matrix setting, proving
  `cond(T,x) ≤ 2n - 1` when `b = Tx ≥ 0`.
- `higham8_8b_stressUpper_lastFirst_singular_update`: Problem 8.8(b)'s
  displayed `T_n + α e_n e_1^T` singular example is now closed with
  `α = -((2^(n-2))⁻¹)`.

No source theorem is claimed complete unless its row is classified `CLOSED`.
Rows with a closed specialization keep the full source-general row visible when
the full theorem still needs current Split 2 source wrappers, integration/API
follow-up, or a valid split-plan deferral.

## 2026-06-24 Kimon Main Re-Audit

The integrated branch now imports Kimon/Split 1 norm and condition-number
machinery through `LeanFpAnalysis.FP.Analysis.Norms`,
`LeanFpAnalysis.FP.Analysis.Stability`, and the lookup smoke declarations
`complexVecLpNorm`, `complexMatrixLpNormOfReal`,
`IsMixedConditionNumberProductValue`,
`complexMatrixLpNormOfReal_conditionNumberRadiusLimitValue_eq_conditionNumberProduct_of_positive_radii_of_inverse`,
`normwiseBackwardErrorBoundedVec`, and `normwiseConditionNumberBoundedVec`.

These declarations remove the old "no imported norm layer" reading of several
Chapter 8 blockers. The current Chapter 8 source wrappers now cover the
componentwise `M/W/Z` inverse chain, the concrete real `1/∞/2` norm chains,
the packaged absolute-norm vector chain for Theorem 8.12, and the full
source-facing Theorem 8.14 norm chain. The remaining current Split 2 work is
no longer the Theorem 8.12 / Theorem 8.14 norm-chain surface itself; it is
the separate condition-number/problem packaging, the arbitrary evaluation-order
and product-rounding API, and the Kahan/SVD/fan-in rows.

Theorem-design entries for current implementation:

| Source row | Former status | Re-audit result | Existing declaration/import | Intended Lean target | Dependencies | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| Lemma 8.8 and Chapter 9 equation (9.17) dependency | Former Split 1-gate label | Closed as a corrected theorem surface after source audit; the printed hypothesis is kept separately as a source-only row, and Chapter 9 equation (9.17) now consumes the corrected wrapper | `higham8_rowDominantUpperSource`; `higham8_8_rowDiagDominantUpper`; `higham8_8_rowDiagDominantUpper_condSkeel_bound`; `higham9_17_absLU_infNorm_le_condSkeel_of_LUFactSpec`; `higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec` | The corrected row-sum-dominance wrapper now closes the downstream Chapter 9 row-dominance norm bound; the printed source condition remains visible only as an audited typo row | Triangular inverse recurrence, scaled unit-upper inverse-entry bound, Chapter 7 `condSkeel`, exact LU algebra for `L = A U⁻¹` | Keep the printed source condition visible as an audited typo and route downstream uses through the corrected theorem |
| Lemma 8.9, Theorem 8.12, and Theorem 8.14 full norm chains | Former Split 1-gate label | Closed as source-facing infinity-/absolute-/`1/2/∞` Chapter 8 wrappers: Lemma 8.9 is closed, Theorem 8.12 now has the packaged absolute-norm vector chain, and Theorem 8.14 now packages the full source `∞/1/2` norm chain under `β ≤ 1` | `comparisonMatrix`; `higham8_9_comparisonMatrix_condAtSolution_eq`; `higham8_9_upperTriangular_condAtSolution_le_comparison_eq`; `higham8_9_lowerTriangular_condAtSolution_le_comparison_eq`; `higham8_12_abs_inv_le_comparison_inv`; `higham8_12_comparisonInv_le_WInv`; `higham8_12_WInv_le_ZInvFormula`; `higham8_12_infNorm_chain`; `higham8_12_oneNorm_chain`; `higham8_12_opNorm2_chain`; `higham8_12_absolute_norm_vector_chain`; `higham8_12_rowMaxStrictUpper`; `higham8_12_WMatrix`; `higham8_12_WMatrix_isDiagDominantUpper`; `higham8_14_WInv_infNorm_upperBound`; `higham8_12_ZMatrix`; `higham8_12_ZInvFormula_isInverse`; `higham8_5_ZInvFormula_infNorm_eq`; `higham8_5_ZInvFormula_oneNorm_eq`; `higham8_5_ZInvFormula_opNorm2_le`; `higham8_14_ZInvFormula_oneNorm_upperBound`; `higham8_14_ZInvFormula_infNorm_upperBound`; `higham8_14_ZInvFormula_opNorm2_upperBound`; `higham8_14_oneNorm_lowerBound`; `higham8_14_oneNorm_upperBound`; `higham8_14_opNorm2_lowerBound`; `higham8_14_opNorm2_upperBound`; `higham8_14_infNorm_lowerBound`; `higham8_14_infNorm_upperBound`; `higham8_14_full_norm_chain`; `complexMatrixLpNormOfReal` | Closed row family; remaining Chapter 8 open work is downstream condition-number/problem packaging, not the Theorem 8.12 / Theorem 8.14 norm-chain surface | Integrated `Norms`, real-to-complex norm preservation, exact `Z(U)` endpoint formulas, and the new local componentwise/absolute/`1/∞/2` chain surfaces | Reuse the closed wrappers in the remaining equation (8.2), Problem 8.6, and condition-number rows |
| Equation (8.2), Problems 8.2-8.7 | Former Split 1-gate label | Current Split 2 target; fixed-order upper/lower substitution wrappers for `(8.2)`, the Appendix A Problem 8.2 asymptotic witness, and the general/source-scaled Problem 8.7 inverse `∞`-norm wrappers are now closed, but the remaining source-facing packaging for Problem 8.3 and Problem 8.6 still needs local follow-through | `normwiseBackwardErrorBoundedVec`; `normwiseConditionNumberBoundedVec`; `higham8_2_backSub_relative_infNorm_bound`; `higham8_2_forwardSub_relative_infNorm_bound`; `higham8_2_comparisonInverseRatios_arbitrarily_large`; `higham8_7_rowDiagMargin`; `higham8_7_scaledRowDiagMargin`; `higham8_7_scaledStrictRowDiagDominant_invInfNorm_le`; `higham8_7_strictRowDiagDominant_invInfNorm_le`; `higham8_7_comparisonInverseOnes_infNorm_ge_inverseInfNorm`; existing Chapter 8 exact/infinity-norm wrappers | Matrix-specialized condition-number wrappers compatible with the source comparison-matrix rows and the new strict-row-dominance inverse-norm layer | Shared norm/condition layer plus Chapter 8 comparison-matrix adapters | Build the remaining `(8.2)` arbitrary-order packaging and Problem 8.3 / Problem 8.6 surfaces after the current middle-chain and arbitrary-order surfaces, not as an external Split 1 blocker |
| Lemma 8.4, full Theorem 8.5, and fan-in equations (8.12)-(8.20) | Former Split 1-gate label | Current Split 2 target or integration/API follow-up; available gamma infrastructure exists, but no arbitrary evaluation-order or fan-in product rounding theorem was found in the current branch | fixed-order `higham8_5_backSub_backward_error`, `higham8_5_forwardSub_backward_error`; available `gammaValid` infrastructure | Shared expression-order scalar theorem and matrix fan-in product theorem, then Chapter 8 wrappers | Integrated rounding/gamma APIs plus the still-missing expression-order/fan-in surfaces | Prove or expose the expression-order and fan-in theorem surfaces without duplicating incompatible rounding algebra |

Progress snapshot after this re-audit:

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- | --- |
| 8 | integrated-Split-1 proof/API re-audit | 100 | 98 | 93 | 95 | 100 | 95 | ~17 | Arbitrary-order/fan-in rounding surfaces plus remaining `(8.2)` / Problems 8.3, 8.6 and Kahan/SVD wrappers | Medium |

## Primary Label Inventory

| Source item | Classification | Previous-split dependency status | Lean declarations | Notes |
| --- | --- | --- | --- | --- |
| Algorithm 8.1, back substitution | `CLOSED` | Uses available Split 1 rounding model through `FPModel`; no unresolved previous-split dependency | `fl_backSub`, `higham8_1_backSub` | Concrete repository algorithm. |
| Lemma 8.2, ordered scalar row error | `CLOSED` | Uses available Split 1 `H03.gamma_theta`; no unresolved previous-split dependency | `BackSubRowSpec`, `backSub_row_tight`, `higham8_2_backSub_row_spec`, `higham8_2_backSub_row_tight` | Row-tight proof chain for the repository evaluation order. |
| Theorem 8.3, Algorithm 8.1 backward error | `CLOSED` | Uses available Split 1 `H02.rounding_model` and `H03.gamma_theta`; no unresolved previous-split dependency | `backSub_backward_error_algorithm_8_1`, `higham8_3_backSub_backward_error` | Row-specific constants match the zero-based Lean translation of the source constants. |
| Lemma 8.4, arbitrary evaluation-order scalar error | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | The needed expression-tree/product rounding surface was not found in the current branch. Next target is a shared arbitrary-evaluation-order scalar theorem compatible with existing `gammaValid`/theta algebra. |
| Theorem 8.5, substitution in any ordering | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | Closed fixed-order specializations: `backSub_backward_error`, `forwardSub_backward_error`, `higham8_5_backSub_backward_error`, `higham8_5_forwardSub_backward_error` | The full source theorem quantifies over arbitrary evaluation ordering. The fixed forward/back substitution orders are proved; the remaining target is the arbitrary-order wrapper over the shared expression-order theorem. |
| Lemma 8.6, condition (8.5) implies the triangular inverse product bound | `CLOSED` | No integrated previous-split blocker | `IsDiagDominantUpper`, `inv_abs_mul_bound_diagDom`, `higham8_6_inv_abs_mul_bound_diagDom` | Genuine triangular inverse recurrence/geometric proof. |
| Theorem 8.7, componentwise forward error under (8.5) | `CLOSED` | Uses available Split 1 `H03.gamma_theta`; no unresolved previous-split dependency | `backSub_forward_error_diagDom`, `higham8_7_backSub_forward_error_diagDom` | Proof reuses the backward-error theorem and Lemma 8.6. |
| Lemma 8.8, row-dominant upper-triangular bound and `cond(U) <= 2n-1` | `CLOSED` as a corrected theorem surface | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_8_rowDiagDominantUpper`; `higham8_8_rowDiagDominantUpper_condSkeel_bound` | PDF audit shows the printed hypothesis `|u_ii| <= sum_{j>i} |u_ij|` is not a viable theorem hypothesis in the current model. The closed Lean theorem uses the corrected strict-upper row-sum dominance condition and proves the Skeel condition-number bound `condSkeel(U) <= 2n-1`. |
| Lemma 8.9, comparison-matrix condition-number identity | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_9_comparisonImage`, `higham8_9_comparisonMatrix_condAtSolution_eq`, `higham8_9_condAtSolution_le_comparisonMatrix`, `higham8_9_upperTriangular_condAtSolution_le_comparison_eq`, `higham8_9_lowerTriangular_condAtSolution_le_comparison_eq` | Closed as source-facing infinity-norm comparison-matrix wrappers over the integrated Chapter 7 condition-number API. The remaining `W/Z` work belongs to Theorems 8.12 and 8.14, not to a duplicate Lemma 8.9 condition-number surface. |
| Theorem 8.10, comparison-matrix forward error | `CLOSED` | Uses available Split 1 `H03.gamma_theta`; no unresolved previous-split dependency | `mu`, `mu_closed_form`, `forwardSub_forward_error_mu_bound`, `higham8_10_forwardSub_forward_error_mu_bound` | Formalized in exact `mu`-recurrence form instead of an informal `O(u^2)` abbreviation. |
| Corollary 8.11, M-matrix high relative accuracy | `CLOSED` | Uses available Split 1 `H03.gamma_theta`; no unresolved previous-split dependency | `mmatrix_forwardSub_relative_error`, `higham8_11_mmatrix_forwardSub_relative_error` | Closed for lower triangular M-matrices and `b >= 0` in exact `mu` form. |
| Theorem 8.12, inverse comparison chain | `CLOSED` | Yes, direct and indirect integrated Split 1 dependency, now discharged locally | Closed first inequality, the `W(U)` and `Z(U)` source surfaces, the full componentwise middle chain, the concrete real `∞/1/2` norm chains, and the fully packaged absolute-norm vector statement: `abs_inv_le_compMatrix_inv`, `abs_inv_le_compMatrix_inv_lowerTri`, `higham8_12_abs_inv_le_comparison_inv`, `higham8_12_comparisonInv_le_WInv`, `higham8_12_WInv_le_ZInvFormula`, `higham8_12_infNorm_chain`, `higham8_12_oneNorm_chain`, `higham8_12_opNorm2_chain`, `higham8_12_absolute_norm_vector_chain`, `higham8_12_rowMaxStrictUpper`, `higham8_12_WMatrix`, `higham8_12_WMatrix_isDiagDominantUpper`, `higham8_12_ZMatrix`, `higham8_12_ZInvFormula`, `higham8_12_ZInvFormula_isInverse` | Closed by the source-general absolute-norm statement `‖ |U⁻¹| |z| ‖ ≤ ‖M(U)⁻¹ |z|‖ ≤ ‖W(U)⁻¹ |z|‖ ≤ ‖Z(U)⁻¹ |z|‖`. |
| Algorithm 8.13, compute `mu = ||M(U)^-1||_inf >= ||U^-1||_inf` | `CLOSED` | No integrated previous-split blocker | `higham8_13_y`, `compMatrix_inv_upper_row_eq_ones`, `higham8_13_comparison_inverse_row_recurrence`, `higham8_13_mu`, `higham8_13_inverse_bound_from_comparison` | Closed as an exact semantic computation and certified upper-bound theorem. The `O(n^2)` flop count is treated as an expository cost statement, not a Lean theorem. |
| Theorem 8.14, norm bounds under (8.5) | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | Closed `∞`-norm pieces, the `W(U)` diagonal-dominant upper-bound bridge, exact `Z(U)⁻¹` endpoint formulas in `1/2/∞`, the explicit middle `2`-norm chain, source-facing `1`- and `2`-norm endpoint bounds for `U⁻¹`, and the final packaged source theorem: `triInv_row_sum_lowerBound`, `triInv_row_sum_upperBound`, `triInv_infNorm_upperBound`, `higham8_12_infNorm_chain`, `higham8_12_oneNorm_chain`, `higham8_12_opNorm2_chain`, `higham8_12_WMatrix_isDiagDominantUpper`, `higham8_14_WInv_infNorm_upperBound`, `higham8_14_infNorm_lowerBound`, `higham8_14_infNorm_upperBound`, `higham8_14_oneNorm_lowerBound`, `higham8_14_oneNorm_upperBound`, `higham8_14_opNorm2_lowerBound`, `higham8_14_opNorm2_upperBound`, `higham8_5_ZInvFormula_infNorm_eq`, `higham8_5_ZInvFormula_oneNorm_eq`, `higham8_5_ZInvFormula_opNorm2_le`, `higham8_14_ZInvFormula_oneNorm_upperBound`, `higham8_14_ZInvFormula_infNorm_upperBound`, `higham8_14_ZInvFormula_opNorm2_upperBound`, `higham8_14_full_norm_chain` | Closed by packaging the already proved middle and endpoint `∞/1/2` consequences in the source theorem's notation using `α = min_i |u_ii|`. |

## Numbered Equation Inventory

| Source item | Classification | Previous-split dependency status | Lean declarations or decision | Notes |
| --- | --- | --- | --- | --- |
| (8.1), rowwise backward-error identity | `CLOSED` | Uses available Split 1 gamma infrastructure | `backSub_row_tight`, `higham8_2_backSub_row_tight` | Source equation appears as the row-tight theorem. |
| (8.2), forward-error condition-number bound | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | fixed-order upper/lower substitution wrappers: `higham8_2_backSub_relative_infNorm_bound`, `higham8_2_forwardSub_relative_infNorm_bound` | The repository's back/forward substitution routines now satisfy the source `cond(T,x) γ_n / (1 - cond(T) γ_n)` relative `∞`-norm bound. The full source row still depends on the arbitrary-order Lemma 8.4 / Theorem 8.5 route and downstream matrix-specific comparison/asymptotic wrappers. |
| (8.3), stress matrix `U(alpha)` | `CLOSED` | No integrated previous-split blocker | `higham8_3_stressUpper` | Displayed definition. |
| (8.4), displayed inverse-entry formula | `CLOSED` | No integrated previous-split blocker | `higham8_4_stressUpperInvFormula`, `higham8_4_stressUpperInvFormula_isInverse` | Displayed formula is encoded and certified as the exact inverse of the stress family. |
| (8.5), diagonal-dominant upper triangular condition | `CLOSED` | No integrated previous-split blocker | `IsDiagDominantUpper` | Existing predicate. |
| (8.6), lower-triangular analogue | `CLOSED` | No integrated previous-split blocker | `higham8_6_diagDominantLower` | Source-facing predicate. |
| (8.7), comparison matrix | `CLOSED` | No integrated previous-split blocker | `comparisonMatrix`, `higham8_7_comparisonMatrix` | Existing definition plus source wrapper. |
| (8.8), `mu` recurrence | `CLOSED` | Uses available Split 1 gamma infrastructure | `mu`, `mu_closed_form`, `forwardSub_forward_error_mu_bound`, `higham8_10_forwardSub_forward_error_mu_bound` | Encoded as the exact recurrence driving Theorem 8.10. |
| (8.9), Theorem 8.14 norm chain | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_9_comparisonMatrix_condAtSolution_eq`, `higham8_9_upperTriangular_condAtSolution_le_comparison_eq`, `higham8_9_lowerTriangular_condAtSolution_le_comparison_eq`, `higham8_12_infNorm_chain`, `higham8_12_oneNorm_chain`, `higham8_12_opNorm2_chain`, `higham8_12_WMatrix_isDiagDominantUpper`, `higham8_14_WInv_infNorm_upperBound`, `higham8_14_infNorm_lowerBound`, `higham8_14_infNorm_upperBound`, `higham8_14_oneNorm_lowerBound`, `higham8_14_oneNorm_upperBound`, `higham8_14_opNorm2_lowerBound`, `higham8_14_opNorm2_upperBound`, `higham8_5_ZInvFormula_infNorm_eq`, `higham8_5_ZInvFormula_oneNorm_eq`, `higham8_5_ZInvFormula_opNorm2_le`, `higham8_14_ZInvFormula_oneNorm_upperBound`, `higham8_14_ZInvFormula_infNorm_upperBound`, `higham8_14_ZInvFormula_opNorm2_upperBound`, `higham8_14_full_norm_chain` now close the componentwise chain, the concrete `∞/1/2` chains, the `1/2/∞` endpoint bounds, and the packaged source norm chain | Closed by the source-facing wrapper `higham8_14_full_norm_chain`. |
| (8.10), QR column-pivoting inequality | `DEFER-LATER-SPLIT` | No direct integrated Split 1 dependency; later deferred block also uses norm infrastructure | none | Belongs with the later QR/factorization split/chapter material referenced by Problem 19.5. |
| (8.11), Kahan matrix family | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | related unscaled base: `higham8_3_stressUpper` | Exact singular-value claims need a source-facing wrapper over the integrated SVD/singular-value layer. |
| (8.12), fan-in factorization `L=L_1...L_n` | `PROVE-NOW-SPLIT2` | Yes, indirect integrated Split 1 dependency; not an unresolved wait | none | The fan-in proof needs a current fan-in algorithm surface and matrix-product/fan-in rounding theorem. |
| (8.13), fan-in product formula | `PROVE-NOW-SPLIT2` | Yes, indirect integrated Split 1 dependency; not an unresolved wait | none | Same fan-in matrix-product target as (8.12). |
| (8.14), rounded fan-in product expansion | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | Needs a matrix/product rounding theorem surface over the available gamma/theta API. |
| (8.15), fan-in componentwise residual bound | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | Needs gamma/product bounds plus the current-split fan-in algorithm. |
| (8.16), fan-in norm residual bound | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | Needs current fan-in rounding plus norm wrappers over the integrated norm API. |
| (8.17), Sameh-Brent backward bound | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | Needs current product-rounding and norm source wrappers. |
| (8.18), fan-in forward comparison bound | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | Needs product-rounding and comparison/norm interfaces. |
| (8.19), weakened fan-in forward bound | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | Same current fan-in/comparison target family as (8.18). |
| (8.20), condition-cubing fan-in bound | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | Needs condition-number/norm wrappers plus current fan-in infrastructure. |

## Problems And Appendix A Inventory

Appendix A contains printed solutions for Problems 8.1, 8.2, 8.3, 8.4, 8.5,
8.7, 8.8, 8.9, and 8.10. No printed Appendix A solution for 8.6 was present in
the extracted text.

| Source item | Classification | Previous-split dependency status | Lean declarations or decision | Notes |
| --- | --- | --- | --- | --- |
| Problem 8.1, no guard-digit backward error | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | Needs a no-guard-digit rounding variant connected to the triangular row proofs. |
| Problem 8.2, arbitrarily large `||M(T)^-1||/||T^-1||` example | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_2_ratioWitness`, `higham8_2_ratioWitnessInv`, `higham8_2_ratioWitnessComparison`, `higham8_2_ratioWitnessComparisonInv`, `higham8_2_comparisonInverseInfNormRatio_ge_lambda`, `higham8_2_comparisonInverseOneNormRatio_ge_lambda`, `higham8_2_comparisonInverseRatios_arbitrarily_large` | Closed by encoding the Appendix A `3 × 3` witness and proving the `∞`- and `1`-norm comparison-inverse ratios both exceed any prescribed `R` for a suitable `λ ≥ 1`. |
| Problem 8.3, explicit bound from Theorem 8.10 | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | Depends on Theorem 8.10 plus norm/asymptotic simplification wrappers. |
| Problem 8.4, M-matrix `cond(T,x) <= 2n-1` for `x >= 0` | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_4_upperTriangularMMatrix_condAtSolution_le` | Closed in the source upper-triangular M-matrix setting by combining the integrated Chapter 7 condition-at-solution API with a local Appendix A comparison-image bound. |
| Problem 8.5, closed form for `||Z(T)^-1||` | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_12_ZMatrix`, `higham8_12_ZInvFormula`, `higham8_5_ZInvFormula_infNorm_eq`, `higham8_5_ZInvFormula_oneNorm_eq` | Closed exactly in the source norm conventions: `‖Z(T)⁻¹‖₁ = ‖Z(T)⁻¹‖∞ = (β + 1)^(n - 1) / α`. |
| Problem 8.6, efficient computation of `||M(U)^-1 |z|||_inf` and `||W(U)^-1 |z|||_inf` | `PROVE-NOW-SPLIT2` | Yes, indirect integrated Split 1 dependency; not an unresolved wait | stronger support for the `M/W` side: `higham8_12_comparisonInv_le_WInv`, `higham8_12_infNorm_chain`, `higham8_12_absolute_norm_vector_chain`, `higham8_14_WInv_infNorm_upperBound` | The cost/algorithm statement still depends on source algorithm/cost packaging rather than on any remaining absolute-norm theorem gap. |
| Problem 8.7, strictly row diagonally dominant inverse norm theorem | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_7_rowDiagMargin`; `higham8_7_scaledRowDiagMargin`; `higham8_7_scaledStrictRowDiagDominant_invInfNorm_le`; `higham8_7_strictRowDiagDominant_invInfNorm_le`; `higham8_7_comparisonInverseOnes_infNorm_ge_inverseInfNorm` | Closed by the general real square-matrix `∞`-norm inverse bound `‖A⁻¹‖∞ ≤ 1 / min_i α_i`, its positive-diagonal scaled variant `‖A⁻¹‖∞ ≤ ‖D‖∞ / min_i β_i`, and the Chapter 8 comparison-matrix corollary rederiving `‖M(U)⁻¹ e‖∞ ≥ ‖U⁻¹‖∞`. |
| Problem 8.8(a), constructive singular rank-one perturbation when `(A^-1)_{ji} != 0` | `CLOSED` | No integrated previous-split blocker | `higham8_8_rankOne_singular_update` | This is the positive branch of the source iff statement. |
| Problem 8.8(a), converse/no-update branch and best perturbation location | `CLOSED` | No integrated previous-split blocker | `higham8_8_rankOne_singular_update_den_eq_zero`, `higham8_8_rankOne_singular_update_iff`, `higham8_8_rankOne_singular_update_abs_eq_inv_abs_inverse_entry`, `higham8_8_bestRankOneSingularUpdate_of_maxInverseEntry`, `higham8_8_bestRankOneSingularUpdate_exists` | Closed by the exact iff criterion `det(A + α e_i e_j^T) = 0 ↔ (A⁻¹)_{ji} ≠ 0 ∧ α = -((A⁻¹)_{ji})⁻¹`, the source magnitude identity `|α| = |(A⁻¹)_{ji}|⁻¹`, and the Appendix A best-place theorem obtained from a maximal-entry position of `A⁻¹`. |
| Problem 8.8(b), `T_n + alpha e_n e_1^T` singular example | `CLOSED` | Yes, indirect integrated Split 1 dependency, now discharged locally | `higham8_8b_stressUpper_lastFirst_singular_update` | Closed by instantiating the general rank-one singular-update theorem with the stress-family inverse entry `(T_n⁻¹)₁ₙ = 2^(n-2)`. |
| Problem 8.9, Kahan singular-value formula | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | Exact source statement needs a singular-value/interlacing wrapper over the integrated SVD layer. |
| Problem 8.10, rational-function triangular solver theorem/counterexample | `SKIP` | No integrated previous-split blocker | none | The problem describes a broad algorithm family plus a counterexample without a fixed executable solver model in the Split 2 contract. It is recorded as underspecified for this pass. |

## Source-Level Side Conditions And Prose Claims

| Source item | Classification | Previous-split dependency status | Lean declarations or decision | Notes |
| --- | --- | --- | --- | --- |
| Nonsingular upper/lower triangular diagonal hypotheses | `CLOSED` | No integrated previous-split blocker | `hU : forall i, U i i != 0`, `hUT`, `hLT`, `IsInverse`, `IsRightInverse` across wrappers | Represented explicitly as theorem hypotheses. |
| Gamma-valid small-unit-roundoff side conditions | `CLOSED` | Uses available Split 1 `H03.gamma_theta`; no unresolved dependency | `gammaValid fp n`, `gammaValid fp (n+1)`, `gammaValid fp (2*n)` | No orphan typeclass hypotheses are used to hide these assumptions. |
| Condition (8.5) and lower analogue (8.6) | `CLOSED` | No integrated previous-split blocker | `IsDiagDominantUpper`, `higham8_6_diagDominantLower` | The upper condition uses `|u_ij| <= |u_ii|` for `j>i`. |
| Printed row-dominant condition before Lemma 8.8 | `CLOSED` as a source condition | No integrated previous-split blocker | `higham8_rowDominantUpperSource` | PDF audit confirms the source prints `|u_ii| <= sum_{j>i} |u_ij|`; no theorem is claimed from this condition. |
| Corrected row-dominant condition used to close Lemma 8.8 | `CLOSED` | No integrated previous-split blocker | `higham8_8_rowDiagDominantUpper`; `higham8_8_rowDiagDominantUpper_condSkeel_bound` | The proved theorem uses the mathematically consistent strict-upper row-sum bound `sum_{j>i} |u_ij| <= |u_ii|` and records the resulting `condSkeel(U) <= 2n-1` certificate. |
| `b >= 0` and M-matrix sign hypotheses in Corollary 8.11 | `CLOSED` | No integrated previous-split blocker beyond available gamma results | `higham8_11_mmatrix_forwardSub_relative_error` hypotheses | Nonnegativity conclusions are proved, not assumed as theorem-equivalent fields. |
| Cost claims such as `O(n^2)`, `O(n)`, and `O(1)` flops | `SKIP` | No integrated previous-split blocker | none | Pure complexity prose is outside the current Lean cost model. |
| Informal `O(u^2)` abbreviations | `SKIP` | Later exact asymptotic APIs may use Split 1, but no theorem is claimed here | exact `mu` forms instead | The formal statements use exact recurrence bounds rather than informal Big-O text. |

## Current Split 2 Proof/API Targets After Previous-Split Re-Audit

| Row family | Previous split | Contract family or missing result | Direct or indirect | Why not local |
| --- | --- | --- | --- | --- |
| Arbitrary evaluation order: Lemma 8.4 and full Theorem 8.5 | Split 1 | `H03.gamma_theta` plus expression-tree/product rounding interfaces | Direct | Reproving would duplicate the shared rounding algebra owned by Split 1. |
| No-guard variant: Problem 8.1 | Split 1 | `H02.rounding_model` / no-guard subtraction variant | Direct | The rounding model variant must be global, not a Chapter 8-only assumption. |
| Condition numbers and remaining norm-general statements: (8.2), Problems 8.3, 8.6 | Split 1 | `H06.norms`, `H06.condition_distance`, and condition-number APIs | Direct | Theorem 8.12 / Theorem 8.14 wrapper layers are now closed, Chapter 9 equation (9.17) already consumes Lemma 8.8 through the corrected `condSkeel` wrapper, and Problem 8.7 is now closed by the local strict-row-dominance inverse-norm theorems; the remaining work is the problem-specific condition-number packaging that should reuse the shared API rather than fork it. |
| Singular-value/Kahan rows: (8.11), Problem 8.9 | Split 1 | `H06.svd` and singular-value interlacing/factorization lemmas | Direct | These are shared spectral foundations, not Chapter 8-specific facts. |
| Fan-in equations (8.12)-(8.20) | Split 1 | `H03.gamma_theta` matrix-product/fan-in rounding; `H06.norms` for norm forms | Direct for rounding/norm bounds; indirect through the current fan-in algorithm interface | The fan-in algorithm should consume the Split 1 product and norm contracts rather than reintroducing product-error models. |

## Verification Ledger

Focused commands run after this pass:

- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter8`
- `lake env lean examples/LibraryLookup.lean`

Repository health commands run after this pass:

- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean examples/LibraryLookup.lean`
- `rg -n "TODO|FIXME" LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean examples/LibraryLookup.lean`
- `git diff --check`

Results:

- Focused `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
  passed.
- Focused `HighamChapter8` build passed:
  `Build completed successfully (3031 jobs).`
- `examples/LibraryLookup.lean` passed and now exposes
  `higham8_12_absolute_norm_vector_chain` and
  `higham8_14_full_norm_chain`.
- Code scan over the touched Chapter 8 Lean file and lookup example found no
  `sorry`, `admit`, `axiom`, `unsafe`, `TODO`, or `FIXME`.
- `git diff --check` passed.

The Lean file and lookup example contain no new `sorry`, `admit`, `axiom`, or
`unsafe`, and the refreshed Chapter 8 surfaces compile cleanly on the current
branch.
