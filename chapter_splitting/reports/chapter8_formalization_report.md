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
- `higham8_14_infNorm_lowerBound`: source-facing lower-bound part of (8.9) for
  the infinity norm, using the existing row-sum lower-bound theorem.
- `higham8_8_rankOne_singular_update`: constructive "possible" branch of
  Problem 8.8(a), proving that the displayed rank-one perturbation is singular
  when the corresponding inverse entry is nonzero.
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
Chapter 8 blockers, but they do not yet close the Chapter 8 rows. The current
Chapter 8 source wrappers are real function-shaped triangular matrices, while
the imported norm/condition-number layer is primarily complex-vector and
mixed-subordinate matrix-norm machinery. The remaining work is an adapter
layer for `M(U)`, the middle `M/W/Z` inverse-chain inequalities, row-dominant
triangular inverse algebra, and
the source's specific condition-number notation, plus the separate expression
tree/product rounding API for arbitrary evaluation order and fan-in products.

Theorem-design entries for current implementation:

| Source row | Former status | Re-audit result | Existing declaration/import | Intended Lean target | Dependencies | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| Lemma 8.8 and Chapter 9 equation (9.17) dependency | Former Split 1-gate label | Closed as a corrected theorem surface after source audit; the printed hypothesis is kept separately as a source-only row | `higham8_rowDominantUpperSource`; `higham8_8_rowDiagDominantUpper`; `higham8_8_rowDiagDominantUpper_condSkeel_bound` | Use the corrected row-sum-dominance wrapper together with the Chapter 7 `condSkeel` API; downstream Ch9 rows should consume this corrected theorem, not the printed misstatement | Triangular inverse recurrence, scaled unit-upper inverse-entry bound, Chapter 7 `condSkeel` | Keep the printed source condition visible as an audited typo and route downstream uses through the corrected theorem |
| Lemma 8.9, Theorem 8.12, and Theorem 8.14 full norm chains | Former Split 1-gate label | Lemma 8.9 is now closed in its source infinity-norm comparison-matrix form; the first comparison-inverse inequality, the `W(U)` source surface and its diagonal-dominant `∞`-norm upper bound, the infinity-norm endpoints, and the exact `Z(U)⁻¹` `1/2/∞` endpoint formulas are closed, but the full `M/W/Z` condition-number and middle-chain inequalities are not represented by the imported API | `comparisonMatrix`; `higham8_9_comparisonMatrix_condAtSolution_eq`; `higham8_9_upperTriangular_condAtSolution_le_comparison_eq`; `higham8_9_lowerTriangular_condAtSolution_le_comparison_eq`; `higham8_12_abs_inv_le_comparison_inv`; `higham8_12_rowMaxStrictUpper`; `higham8_12_WMatrix`; `higham8_12_WMatrix_isDiagDominantUpper`; `higham8_14_WInv_infNorm_upperBound`; `higham8_12_ZMatrix`; `higham8_12_ZInvFormula_isInverse`; `higham8_5_ZInvFormula_infNorm_eq`; `higham8_5_ZInvFormula_oneNorm_eq`; `higham8_5_ZInvFormula_opNorm2_le`; `higham8_14_ZInvFormula_oneNorm_upperBound`; `higham8_14_ZInvFormula_infNorm_upperBound`; `higham8_14_ZInvFormula_opNorm2_upperBound`; `higham8_14_infNorm_lowerBound`; `higham8_14_infNorm_upperBound`; `complexMatrixLpNormOfReal` | `higham8_12_norm_chain`, `higham8_14_full_norm_chain`, with the middle `M(U)⁻¹/W(U)⁻¹/Z(U)⁻¹` inequalities as the remaining source-facing gap | Integrated `Norms`, real-to-complex norm preservation, exact `Z(U)` endpoint formulas, the new `W(U)` source surface, and a reusable inverse-monotonicity surface for the missing middle chain | Prove the middle norm-chain inequalities; the current-branch audit still did not find a reusable upper-triangular M-matrix inverse-monotonicity theorem for the `W(U)⁻¹ ≤ Z(U)⁻¹` step |
| Equation (8.2), Problems 8.2-8.7 | Former Split 1-gate label | Current Split 2 target; `normwiseConditionNumberBoundedVec` exists but does not by itself express the Chapter 8 matrix-specific comparison bounds or asymptotic examples | `normwiseBackwardErrorBoundedVec`; `normwiseConditionNumberBoundedVec`; existing Chapter 8 exact/infinity-norm wrappers | Matrix-specialized condition-number wrappers compatible with the source comparison-matrix rows | Shared norm/condition layer plus Chapter 8 comparison-matrix adapters | Build these after Lemmas 8.8/8.9 and `W/Z` surfaces, not as an external Split 1 blocker |
| Lemma 8.4, full Theorem 8.5, and fan-in equations (8.12)-(8.20) | Former Split 1-gate label | Current Split 2 target or integration/API follow-up; available gamma infrastructure exists, but no arbitrary evaluation-order or fan-in product rounding theorem was found in the current branch | fixed-order `higham8_5_backSub_backward_error`, `higham8_5_forwardSub_backward_error`; available `gammaValid` infrastructure | Shared expression-order scalar theorem and matrix fan-in product theorem, then Chapter 8 wrappers | Integrated rounding/gamma APIs plus the still-missing expression-order/fan-in surfaces | Prove or expose the expression-order and fan-in theorem surfaces without duplicating incompatible rounding algebra |

Progress snapshot after this re-audit:

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- | --- |
| 8 | integrated-Split-1 proof/API re-audit | 100 | 90 | 80 | 81 | 89 | 87 | Theorems 8.12/8.14 full chains, equation (8.2), fan-in rows, Problems 8.2-8.7 except 8.5 | Middle `M/W/Z` inverse-monotonicity and expression/fan-in rounding theorem surfaces | Medium |

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
| Theorem 8.12, inverse comparison chain | `PROVE-NOW-SPLIT2` | Yes, direct and indirect integrated Split 1 dependency; not an unresolved wait | Closed first inequality, the `W(U)` source surface, and the exact `Z(U)` endpoint surface: `abs_inv_le_compMatrix_inv`, `abs_inv_le_compMatrix_inv_lowerTri`, `higham8_12_abs_inv_le_comparison_inv`, `higham8_12_rowMaxStrictUpper`, `higham8_12_WMatrix`, `higham8_12_WMatrix_isDiagDominantUpper`, `higham8_12_ZMatrix`, `higham8_12_ZInvFormula`, `higham8_12_ZInvFormula_isInverse` | The remaining source chain is now the middle inequalities linking `M(U)⁻¹`, `W(U)⁻¹`, and `Z(U)⁻¹` through the shared norm API. |
| Algorithm 8.13, compute `mu = ||M(U)^-1||_inf >= ||U^-1||_inf` | `CLOSED` | No integrated previous-split blocker | `higham8_13_y`, `compMatrix_inv_upper_row_eq_ones`, `higham8_13_comparison_inverse_row_recurrence`, `higham8_13_mu`, `higham8_13_inverse_bound_from_comparison` | Closed as an exact semantic computation and certified upper-bound theorem. The `O(n^2)` flop count is treated as an expository cost statement, not a Lean theorem. |
| Theorem 8.14, norm bounds under (8.5) | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | Closed infinity-norm pieces, the `W(U)` diagonal-dominant upper-bound bridge, and exact `Z(U)⁻¹` endpoint formulas in `1/2/∞`: `triInv_row_sum_lowerBound`, `triInv_row_sum_upperBound`, `triInv_infNorm_upperBound`, `higham8_12_WMatrix_isDiagDominantUpper`, `higham8_14_WInv_infNorm_upperBound`, `higham8_14_infNorm_lowerBound`, `higham8_14_infNorm_upperBound`, `higham8_5_ZInvFormula_infNorm_eq`, `higham8_5_ZInvFormula_oneNorm_eq`, `higham8_5_ZInvFormula_opNorm2_le`, `higham8_14_ZInvFormula_oneNorm_upperBound`, `higham8_14_ZInvFormula_infNorm_upperBound`, `higham8_14_ZInvFormula_opNorm2_upperBound` | The full source theorem still needs the middle `M/W/Z` inequalities; the current branch did not expose a ready-made inverse-monotonicity theorem for the `W(U)` step. |

## Numbered Equation Inventory

| Source item | Classification | Previous-split dependency status | Lean declarations or decision | Notes |
| --- | --- | --- | --- | --- |
| (8.1), rowwise backward-error identity | `CLOSED` | Uses available Split 1 gamma infrastructure | `backSub_row_tight`, `higham8_2_backSub_row_tight` | Source equation appears as the row-tight theorem. |
| (8.2), forward-error condition-number bound | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | Needs a source-shaped wrapper over the integrated norm/condition-number API. |
| (8.3), stress matrix `U(alpha)` | `CLOSED` | No integrated previous-split blocker | `higham8_3_stressUpper` | Displayed definition. |
| (8.4), displayed inverse-entry formula | `CLOSED` | No integrated previous-split blocker | `higham8_4_stressUpperInvFormula`, `higham8_4_stressUpperInvFormula_isInverse` | Displayed formula is encoded and certified as the exact inverse of the stress family. |
| (8.5), diagonal-dominant upper triangular condition | `CLOSED` | No integrated previous-split blocker | `IsDiagDominantUpper` | Existing predicate. |
| (8.6), lower-triangular analogue | `CLOSED` | No integrated previous-split blocker | `higham8_6_diagDominantLower` | Source-facing predicate. |
| (8.7), comparison matrix | `CLOSED` | No integrated previous-split blocker | `comparisonMatrix`, `higham8_7_comparisonMatrix` | Existing definition plus source wrapper. |
| (8.8), `mu` recurrence | `CLOSED` | Uses available Split 1 gamma infrastructure | `mu`, `mu_closed_form`, `forwardSub_forward_error_mu_bound`, `higham8_10_forwardSub_forward_error_mu_bound` | Encoded as the exact recurrence driving Theorem 8.10. |
| (8.9), Theorem 8.14 norm chain | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | `higham8_9_comparisonMatrix_condAtSolution_eq`, `higham8_9_upperTriangular_condAtSolution_le_comparison_eq`, `higham8_9_lowerTriangular_condAtSolution_le_comparison_eq`, `higham8_12_WMatrix_isDiagDominantUpper`, `higham8_14_WInv_infNorm_upperBound`, `higham8_14_infNorm_lowerBound`, `higham8_14_infNorm_upperBound`, `higham8_5_ZInvFormula_infNorm_eq`, `higham8_5_ZInvFormula_oneNorm_eq`, `higham8_5_ZInvFormula_opNorm2_le`, `higham8_14_ZInvFormula_oneNorm_upperBound`, `higham8_14_ZInvFormula_infNorm_upperBound`, `higham8_14_ZInvFormula_opNorm2_upperBound` close the infinity-norm comparison wrapper, the `W(U)` `∞`-norm upper-bound bridge, and the exact `Z(U)⁻¹` endpoint formulas in `1/2/∞` | Full `1/2/∞` chain still needs the middle `M/W/Z` inequalities over the available norm infrastructure. |
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
| Problem 8.2, arbitrarily large `||M(T)^-1||/||T^-1||` example | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | The symbolic 3-by-3 matrices are local; the source ratio/asymptotic claim needs norm/asymptotic wrappers. |
| Problem 8.3, explicit bound from Theorem 8.10 | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | Depends on Theorem 8.10 plus norm/asymptotic simplification wrappers. |
| Problem 8.4, M-matrix `cond(T,x) <= 2n-1` for `x >= 0` | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | Needs the shared condition-number API; local nilpotent/M-matrix monotonicity should target that API, not a duplicate. |
| Problem 8.5, closed form for `||Z(T)^-1||` | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_12_ZMatrix`, `higham8_12_ZInvFormula`, `higham8_5_ZInvFormula_infNorm_eq`, `higham8_5_ZInvFormula_oneNorm_eq` | Closed exactly in the source norm conventions: `‖Z(T)⁻¹‖₁ = ‖Z(T)⁻¹‖∞ = (β + 1)^(n - 1) / α`. |
| Problem 8.6, efficient computation of `||M(U)^-1 |z|||_inf` and `||W(U)^-1 |z|||_inf` | `PROVE-NOW-SPLIT2` | Yes, indirect integrated Split 1 dependency; not an unresolved wait | partial support for the `W(U)` side: `higham8_12_WMatrix`, `higham8_14_WInv_infNorm_upperBound` | The cost/algorithm statement still depends on the same middle `M/W` norm interfaces as Theorem 8.12. |
| Problem 8.7, strictly row diagonally dominant inverse norm theorem | `PROVE-NOW-SPLIT2` | Yes, direct integrated Split 1 dependency; not an unresolved wait | none | Needs a general matrix infinity-norm/inverse wrapper over the integrated norm foundations. |
| Problem 8.8(a), constructive singular rank-one perturbation when `(A^-1)_{ji} != 0` | `CLOSED` | No integrated previous-split blocker | `higham8_8_rankOne_singular_update` | This is the positive branch of the source iff statement. |
| Problem 8.8(a), converse/no-update branch and best perturbation location | `PROVE-NOW-SPLIT2` | Yes, indirect integrated Split 1 dependency; not an unresolved wait | none | Needs a reusable determinant/rank-one update API and finite max-entry/norm conventions. The positive branch above is closed. |
| Problem 8.8(b), `T_n + alpha e_n e_1^T` singular example | `PROVE-NOW-SPLIT2` | Yes, indirect integrated Split 1 dependency; not an unresolved wait | none | Depends on the full Problem 8.8(a) rank-one API and the stress-matrix inverse identity around (8.4). |
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
| Condition numbers and norm-general statements: (8.2), Lemmas 8.8/8.9, Theorems 8.12/8.14, Problems 8.2-8.7 | Split 1 | `H06.norms`, `H06.condition_distance`, and condition-number APIs | Direct | Local definitions would produce incompatible condition-number statements for later chapters. |
| Singular-value/Kahan rows: (8.11), Problem 8.9 | Split 1 | `H06.svd` and singular-value interlacing/factorization lemmas | Direct | These are shared spectral foundations, not Chapter 8-specific facts. |
| Fan-in equations (8.12)-(8.20) | Split 1 | `H03.gamma_theta` matrix-product/fan-in rounding; `H06.norms` for norm forms | Direct for rounding/norm bounds; indirect through the current fan-in algorithm interface | The fan-in algorithm should consume the Split 1 product and norm contracts rather than reintroducing product-error models. |

## Verification Ledger

Focused commands run after this pass:

- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
- `lake build LeanFpAnalysis.FP.Algorithms.TriangularForwardBound`
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter8`
- `lake env lean examples/LibraryLookup.lean`
- `lake env lean /tmp/higham8_axioms.lean`

Repository health commands run after this pass:

- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean LeanFpAnalysis/FP/Algorithms/TriangularForwardBound.lean examples/LibraryLookup.lean`
- `rg -n "TODO|FIXME" LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean LeanFpAnalysis/FP/Algorithms/TriangularForwardBound.lean examples/LibraryLookup.lean`
- `rg -n "placeholder|vacuous|theorem-equivalent" LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean LeanFpAnalysis/FP/Algorithms/TriangularForwardBound.lean examples/LibraryLookup.lean`
- `git diff --check`
- `#print axioms` for:
  - `LeanFpAnalysis.FP.higham8_8_rowDiagDominantUpper_condSkeel_bound`
  - `LeanFpAnalysis.FP.unitUpperTri_inv_entry_le_one_of_row_sum_le_one`
  - plus `#check` expansion from `examples/LibraryLookup.lean`
- `lake build`

Results:

- Focused `TriangularForwardBound` build passed:
  `Build completed successfully (2421 jobs).`
- Focused `HighamChapter8` build passed:
  `Build completed successfully (2426 jobs).`
- `examples/LibraryLookup.lean` passed.
- Code scan over the touched Chapter 8 Lean files and lookup example found no
  `sorry`, `admit`, `axiom`, or `unsafe`.
- Chapter 8 TODO/FIXME scan found no matches.
- A broader local placeholder scan found no Chapter 8 `placeholder`, `vacuous`,
  or `theorem-equivalent` markers.  Existing `certificate` lookup entries were
  pre-existing outside this Chapter 8 pass and are not theorem-equivalent
  assumptions introduced here.
- `git diff --check` passed.
- `#print axioms` for the new corrected Lemma 8.8 theorem and its reusable
  unit-upper helper reported only
  standard Lean/mathlib foundations: `propext`, `Classical.choice`, and
  `Quot.sound`.
- Full `lake build` passed: `Build completed successfully (3507 jobs).`
  Remaining warnings are pre-existing QR/FastMatMul linter warnings outside
  Chapter 8.

The Lean files contain no new `sorry`, `admit`, `axiom`, or `unsafe`; no orphan
classes are used as theorem hypotheses; and the new definitions are not vacuous
theorem-equivalent assumptions.
