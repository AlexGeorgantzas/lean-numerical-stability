# Chapter 8 Formalization Report

Date: 2026-06-27.
Edition: Higham, Accuracy and Stability of Numerical Algorithms, 2nd ed.
Source: `/home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.ch8.pdf`.
Appendix source read: `/home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.appa.pdf`.
Split contract: Split 2, Chapter 8.
Mode: proof-completion pass for Split 2.
Selected-scope gate: PASS.

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
- `higham8_6_comparisonInverseAbsVec`,
  `higham8_6_comparisonInverseAbsVecInfNorm`,
  `higham8_6_WInverseAbsVec`,
  `higham8_6_WInverseAbsVecInfNorm`,
  `higham8_6_comparisonInverseAbsVec_recurrence`,
  `higham8_6_WInverseAbsVec_recurrence`,
  `higham8_6_comparisonInverseAbsVec_le_WInverseAbsVec`, and
  `higham8_6_comparisonInverseAbsVecInfNorm_le_WInverseAbsVecInfNorm`:
  Problem 8.6 is now closed at the mathematical algorithm-spec level.  The two
  exact vectors `M(U)⁻¹ |z|` and `W(U)⁻¹ |z|` are exposed, their backward-sweep
  row recurrences are proved, and the `∞`-norm `M/W` comparison is certified.
  The source flop-count prose remains a skipped cost-model claim.
- `higham8_8b_stressUpper_lastFirst_singular_update`: Problem 8.8(b)'s
  displayed `T_n + α e_n e_1^T` singular example is now closed with
  `α = -((2^(n-2))⁻¹)`.
- `higham8_problem8_1_noGuard_mulSub_div_row_tight`,
  `higham8_problem8_1_noGuard_backSub_backward_error`, and
  `higham8_problem8_1_noGuard_forwardSub_backward_error`: Problem 8.1 is now
  closed under the no-guard-digit model (2.6).  The scalar modified Lemma 8.2
  row keeps `c` unperturbed with the source `θ_(i+2)` indexing, and the
  upper/lower modified Theorem 8.5 wrappers prove
  `(T + ΔT)xhat = b`, `|ΔT| ≤ γ_(n+1)|T|`.
- `higham8_12_lowerColumnFactor`,
  `higham8_12_lowerColumnProductPrefix_apply`, and
  `higham8_12_lowerColumnProduct_eq`: equation (8.12)'s exact
  lower-triangular column-factor factorization `L = L_1 ... L_n` is now
  closed.
- `higham8_14_fanIn7RoundedMatrix`,
  `higham8_18_fanIn_forward_componentwise_bound`,
  `higham8_19_fanIn_forward_relative_infNorm_bound`,
  `higham8_15_fanIn_residual_componentwise_bound`,
  `higham8_16_fanIn_residual_infNorm_bound`,
  `higham8_17_backward_error_from_residual_infNorm_bound`, and
  `higham8_20_condition_cubing_relative_infNorm_bound`: the fan-in
  finite-product perturbation, residual, backward-error, and condition-cubing
  wrappers for `(8.14)`--`(8.20)` are now closed with explicit local
  perturbation hypotheses.
- `higham8_problem8_9_kahanRightWitness`,
  `higham8_problem8_9_kahanLeftWitness`,
  `higham8_problem8_9_kahan_witness_forward`,
  `higham8_problem8_9_kahan_witness_transpose`, and
  `higham8_problem8_9_kahan_gram_witness`: Appendix A's explicit Kahan
  singular-vector equations and the resulting Gram-eigenpair certificate are
  now formalized and feed the final ordered second-smallest singular-value
  theorem.
- `higham8_11_kahanMatrix_leadingBlock_succ`,
  `higham8_11_kahanGram_leadingBlock_succ`,
  `higham8_problem8_9_kahanRightWitness_euclidean_ne_zero`,
  `higham8_problem8_9_kahan_candidate_hasGramEigenvalue`,
  `higham8_problem8_9_kahan_candidate_mem_gramEigenvalues`,
  `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_le_candidate`,
  `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_lower_bound`,
  and `higham8_problem8_9_kahan_secondSmallestSingularValue_of_lower_bound`:
  the leading matrix/Gram block identities, nonzero witness, sorted-list
  membership, easy ordered upper half, and final lower-bound bridge are now
  formalized.
- `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_two`
  and `higham8_problem8_9_kahan_secondSmallestSingularValue_two`: the
  `2 × 2`, `0 < s < 1` base case is closed without interlacing by sorted
  antitonicity and candidate membership.
- `higham8_problem8_9_thirdSmallestIndex`,
  `higham8_problem8_9_kahan_smallestGramEigenvalue_lt_candidate`,
  `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_interlacing`,
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_interlacing`, and
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_kahanGram_interlacing`:
  the Appendix A induction is packaged as a reusable bridge from the Kahan Gram
  interlacing step to the source singular-value formula.
- `higham8_problem8_9_kahanGram_interlacing` and
  `higham8_problem8_9_kahan_secondSmallestSingularValue`: the Kahan-specific
  singular-vector span/intersection proof now supplies the missing ordered
  Gram interlacing step, closing Problem 8.9's source singular-value formula.
- `higham8_11_kahanMatrix_zero_one_eq_finiteId`,
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_one`,
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_zero`, and
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_interior_lower_bound`:
  the source edge cases `s = 1` and `s = 0` are closed, and the all-cases
  wrapper now composes with the closed Kahan Gram interlacing theorem.
- `higham8_problem8_9_kahan_stressInvLastColumn_action`,
  `higham8_problem8_9_kahan_smallestSingularValue_le_pow`, and
  `higham8_problem8_9_kahan_smallestSingularValue_lt_candidate`: Appendix A's
  side condition that the displayed candidate is not the smallest singular
  value is now formalized in the `0 < s < 1` branch.

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
source-facing Theorem 8.14 norm chain. Problem 8.6 now also has exact
`M(U)⁻¹ |z|` and `W(U)⁻¹ |z|` bound-vector recurrences. The remaining current
Split 2 work is no longer the Theorem 8.12 / Theorem 8.14 norm-chain surface,
Problem 8.6, Problem 8.1, the fan-in finite-product wrappers, or Problem 8.9's
ordered Kahan singular-value formula; the selected Chapter 8 Split 2 rows are
now closed.

Theorem-design entries for current implementation:

| Source row | Former status | Re-audit result | Existing declaration/import | Intended Lean target | Dependencies | Next action |
| --- | --- | --- | --- | --- | --- | --- |
| Lemma 8.8 and Chapter 9 equation (9.17) dependency | Former Split 1-gate label | Closed as a corrected theorem surface after source audit; the printed hypothesis is kept separately as a source-only row, and Chapter 9 equation (9.17) now consumes the corrected wrapper | `higham8_rowDominantUpperSource`; `higham8_8_rowDiagDominantUpper`; `higham8_8_rowDiagDominantUpper_condSkeel_bound`; `higham9_17_absLU_infNorm_le_condSkeel_of_LUFactSpec`; `higham9_17_rowDiagDom_absLU_bound_of_LUFactSpec` | The corrected row-sum-dominance wrapper now closes the downstream Chapter 9 row-dominance norm bound; the printed source condition remains visible only as an audited typo row | Triangular inverse recurrence, scaled unit-upper inverse-entry bound, Chapter 7 `condSkeel`, exact LU algebra for `L = A U⁻¹` | Keep the printed source condition visible as an audited typo and route downstream uses through the corrected theorem |
| Lemma 8.9, Theorem 8.12, and Theorem 8.14 full norm chains | Former Split 1-gate label | Closed as source-facing infinity-/absolute-/`1/2/∞` Chapter 8 wrappers: Lemma 8.9 is closed, Theorem 8.12 now has the packaged absolute-norm vector chain, and Theorem 8.14 now packages the full source `∞/1/2` norm chain under `β ≤ 1` | `comparisonMatrix`; `higham8_9_comparisonMatrix_condAtSolution_eq`; `higham8_9_upperTriangular_condAtSolution_le_comparison_eq`; `higham8_9_lowerTriangular_condAtSolution_le_comparison_eq`; `higham8_12_abs_inv_le_comparison_inv`; `higham8_12_comparisonInv_le_WInv`; `higham8_12_WInv_le_ZInvFormula`; `higham8_12_infNorm_chain`; `higham8_12_oneNorm_chain`; `higham8_12_opNorm2_chain`; `higham8_12_absolute_norm_vector_chain`; `higham8_12_rowMaxStrictUpper`; `higham8_12_WMatrix`; `higham8_12_WMatrix_isDiagDominantUpper`; `higham8_14_WInv_infNorm_upperBound`; `higham8_12_ZMatrix`; `higham8_12_ZInvFormula_isInverse`; `higham8_5_ZInvFormula_infNorm_eq`; `higham8_5_ZInvFormula_oneNorm_eq`; `higham8_5_ZInvFormula_opNorm2_le`; `higham8_14_ZInvFormula_oneNorm_upperBound`; `higham8_14_ZInvFormula_infNorm_upperBound`; `higham8_14_ZInvFormula_opNorm2_upperBound`; `higham8_14_oneNorm_lowerBound`; `higham8_14_oneNorm_upperBound`; `higham8_14_opNorm2_lowerBound`; `higham8_14_opNorm2_upperBound`; `higham8_14_infNorm_lowerBound`; `higham8_14_infNorm_upperBound`; `higham8_14_full_norm_chain`; `complexMatrixLpNormOfReal` | Closed row family; remaining Chapter 8 open work is downstream arbitrary-order `(8.2)` packaging, not the Theorem 8.12 / Theorem 8.14 norm-chain surface | Integrated `Norms`, real-to-complex norm preservation, exact `Z(U)` endpoint formulas, and the new local componentwise/absolute/`1/∞/2` chain surfaces | Reuse the closed wrappers in the remaining equation (8.2) arbitrary-order condition-number row |
| Equation (8.2), Problems 8.2-8.7 | Former Split 1-gate label | Closed as Split 2 wrappers; fixed-order and arbitrary-order upper/lower substitution routes for `(8.2)`, the Appendix A Problem 8.2 asymptotic witness, the exact-`μ`/sharper-geometric-sum Problem 8.3 wrapper, Problem 8.6 exact `M/W` bound-vector recurrences and `∞`-norm comparison, and the general/source-scaled Problem 8.7 inverse `∞`-norm wrappers are now closed | `normwiseBackwardErrorBoundedVec`; `normwiseConditionNumberBoundedVec`; `higham8_2_backSub_relative_infNorm_bound`; `higham8_2_forwardSub_relative_infNorm_bound`; `higham8_2_backSub_anyOrder_relative_infNorm_bound`; `higham8_2_forwardSub_anyOrder_relative_infNorm_bound`; `higham8_2_comparisonInverseRatios_arbitrarily_large`; `higham8_problem8_3_unitUpper_backSub_forward_error_mu_infNorm_bound`; `higham8_6_comparisonInverseAbsVec`; `higham8_6_comparisonInverseAbsVecInfNorm`; `higham8_6_WInverseAbsVec`; `higham8_6_WInverseAbsVecInfNorm`; `higham8_6_comparisonInverseAbsVec_recurrence`; `higham8_6_WInverseAbsVec_recurrence`; `higham8_6_comparisonInverseAbsVec_le_WInverseAbsVec`; `higham8_6_comparisonInverseAbsVecInfNorm_le_WInverseAbsVecInfNorm`; `higham8_7_rowDiagMargin`; `higham8_7_scaledRowDiagMargin`; `higham8_7_scaledStrictRowDiagDominant_invInfNorm_le`; `higham8_7_strictRowDiagDominant_invInfNorm_le`; `higham8_7_comparisonInverseOnes_infNorm_ge_inverseInfNorm`; existing Chapter 8 exact/infinity-norm wrappers | Closed source-general arbitrary-order equation `(8.2)` wrappers compatible with Lemma 8.4/Theorem 8.5 | Shared norm/condition layer plus Chapter 8 comparison-matrix adapters | Reuse these closed wrappers; no remaining `(8.2)` blocker |
| Lemma 8.4, full Theorem 8.5, and fan-in equations (8.12)-(8.20) | Former Split 1-gate label | Closed locally: Lemma 8.4, full upper/lower arbitrary-order Theorem 8.5, exact fan-in factorization (8.12), exact n=7 fan-in product (8.13), rounded finite-product expression (8.14), residual/backward-error surfaces (8.15)--(8.17), forward-error surfaces (8.18)--(8.19), and condition-cubing surface (8.20) now all have compiling theorem surfaces | fixed-order `higham8_5_backSub_backward_error`, `higham8_5_forwardSub_backward_error`; arbitrary-order declarations `SumTree.backward_error_pivot`, `higham8_4_anyOrder`, `higham8_4_anyOrder_mulSub_div`, `BackSubAnyOrderSpec`, `ForwardSubAnyOrderSpec`, `backSub_backward_error_anyOrder`, `forwardSub_backward_error_anyOrder`, `higham8_5_backSub_anyOrder_backward_error`, `higham8_5_forwardSub_anyOrder_backward_error`; fan-in declarations `higham8_12_lowerColumnFactor`, `higham8_12_lowerColumnProductPrefix_apply`, `higham8_12_lowerColumnProduct_eq`, `higham8_13_fanIn7Matrix_eq_sequential7Matrix`, `higham8_14_fanIn7RoundedMatrix`, `higham8_14_fanIn7RoundedApply`, `higham8_18_fanIn_forward_componentwise_bound`, `higham8_19_fanIn_forward_relative_infNorm_bound`, `higham8_15_fanIn_residual_componentwise_bound`, `higham8_16_fanIn_residual_infNorm_bound`, `higham8_17_backward_error_from_residual_infNorm_bound`, `higham8_20_condition_cubing_relative_infNorm_bound` | Closed fan-in wrapper family | Integrated rounding/gamma and norm APIs plus local finite-product perturbation wrappers | Reuse the closed fan-in wrappers; no remaining fan-in selected row |
| Problem 8.1 no-guard substitution variant | Former Split 1-gate label | Closed as a no-guard model theorem surface: the global `NoGuardFPModel` model exists, the modified scalar row identity is proved, and upper/lower modified Theorem 8.5 wrappers are assembled at `γ_(n+1)` | `NoGuardFPModel`; `NoGuardFPModel.gammaProxy`; `noGuardGamma`; `noGuard_sub_fold_unroll`; `noGuard_mulSub_div_row_tight`; `NoGuardBackSubSpec`; `NoGuardForwardSubSpec`; `noGuard_backSub_backward_error`; `noGuard_forwardSub_backward_error`; `higham8_problem8_1_noGuard_mulSub_div_row_tight`; `higham8_problem8_1_noGuard_backSub_backward_error`; `higham8_problem8_1_noGuard_forwardSub_backward_error` | Closed source Problem 8.1 row | Existing no-guard model plus local row/matrix assembly | Reuse these wrappers; no remaining Problem 8.1 blocker |

Progress snapshot after this re-audit:

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- | --- |
| 8 | proof-completion | 100 | 100 | 100 | 100 | 100 | 100 | 0 | None. Problem 8.9 is closed by the Kahan-specific Gram interlacing theorem `higham8_problem8_9_kahanGram_interlacing`, which composes with the existing all-cases wrapper to give `higham8_problem8_9_kahan_secondSmallestSingularValue`. Fan-in `(8.14)`--`(8.20)`, Lemma 8.4, arbitrary-order Theorem 8.5, arbitrary-order `(8.2)`, no-guard Problem 8.1, and exact fan-in factorization `(8.12)` are CLOSED. | High |

## Problem 8.9 Closure Ledger

Closed spectral step:

```lean
∀ (m : ℕ) (hm : 3 ≤ m),
  complexMatrixGramEigenvalues
      (realRectToCMatrix (higham8_11_kahanMatrix (m - 1) c s))
      (higham8_problem8_9_secondSmallestIndex (m - 1) (by omega)) ≤
    complexMatrixGramEigenvalues
      (realRectToCMatrix (higham8_11_kahanMatrix m c s))
      (higham8_problem8_9_thirdSmallestIndex m hm)
```

This is now theorem `higham8_problem8_9_kahanGram_interlacing`.  It is proved
locally, without a new global Courant--Fischer API, by embedding the right
singular-vector top span of the leading `(m-1) × (m-1)` Kahan block into the
current `m × m` space with a final zero coordinate, intersecting it with the
current Gram tail span by a dimension count, and squeezing the image norm
between the corresponding ordered singular values.  Squaring the singular-value
inequality gives the Gram inequality.

The compiled wrapper
`higham8_problem8_9_kahan_secondSmallestSingularValue_of_kahanGram_interlacing`
proves that this interlacing step is sufficient for the full source
second-smallest singular-value formula.  Equivalently, it supplies the earlier
raw lower inequality
`(s^(n-2))^2 * (1+c) <= complexMatrixGramEigenvalues ... (n-2)` in the
inductive range `3 ≤ n`.  The `n = 2` branch and both source edge cases
`s = 0` and `s = 1` are closed.  The final source-facing theorem is
`higham8_problem8_9_kahan_secondSmallestSingularValue`.

Closed source inputs:

- `higham8_11_kahanMatrix_leadingBlock_succ` and
  `higham8_11_kahanGram_leadingBlock_succ` prove the leading principal Kahan
  matrix and Gram block identities needed by the Appendix A induction.
- `higham8_problem8_9_kahan_witness_forward`,
  `higham8_problem8_9_kahan_witness_transpose`, and
  `higham8_problem8_9_kahan_gram_witness` prove the candidate is a genuine
  Gram eigenvalue.
- `higham8_problem8_9_kahanRightWitness_euclidean_ne_zero`,
  `higham8_problem8_9_kahan_candidate_hasGramEigenvalue`, and
  `higham8_problem8_9_kahan_candidate_mem_gramEigenvalues` turn the explicit
  witness into membership in the sorted Gram-eigenvalue list.
- `higham8_problem8_9_kahan_smallestSingularValue_le_pow` and
  `higham8_problem8_9_kahan_smallestSingularValue_lt_candidate`, plus
  `higham8_problem8_9_kahan_smallestGramEigenvalue_lt_candidate`, prove the
  candidate is not the smallest singular/Gram value in Appendix A's
  `0 < s < 1` branch.
- `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_le_candidate` closes
  the easy ordered half
  `complexMatrixGramEigenvalues ... (n-2) <= (s^(n-2))^2*(1+c)`.
- `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_lower_bound`
  and `higham8_problem8_9_kahan_secondSmallestSingularValue_of_lower_bound`
  prove that the exact lower inequality above is sufficient to finish the
  ordered Gram equality and singular-value formula.
- `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_two` and
  `higham8_problem8_9_kahan_secondSmallestSingularValue_two` close the
  `n = 2`, `0 < s < 1` base case.
- `higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_zero`,
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_one`, and
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_interior_lower_bound`
  close both source edge cases and package the full source formula behind only
  the exact interior lower-bound hypothesis above.
- `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_interlacing`,
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_interlacing`, and
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_kahanGram_interlacing`
  package the Appendix A induction: the exact interlacing step above implies
  the interior ordered Gram equality and then the full all-cases
  singular-value formula.
- `higham8_problem8_9_kahanGram_interlacing` supplies the exact spectral step
  above, and `higham8_problem8_9_kahan_secondSmallestSingularValue` is the
  unconditional Problem 8.9 theorem under `c, s >= 0` and
  `c^2 + s^2 = 1`.

> 2026-06-26 proof-completion update: **Lemma 8.4 closed** at the sharp source
> constant `γ_n` by adding the pivot-normalised summation-tree backward error
> `SumTree.backward_error_pivot` and the scalar wrappers `higham8_4_anyOrder` /
> `higham8_4_anyOrder_backwardError`.  This corrects the prior audit's
> classification of the arbitrary-order rows as a missing-foundation /
> cross-split blocker: per the parallel-formalization blueprint, Lemma 8.4 and
> Theorem 8.5 are Split 2's *own* primary labels, and the required Split 1
> foundations (`SumTree` = Algorithm 4.1, `relErrorCounter` = Lemma 3.1) are
> already present on the branch.  At that point, the remaining gap to Theorem
> 8.5 was an arbitrary-order substitution algorithm model that discharges each
> row via `higham8_4_anyOrder`; the later update below closes the upper/back
> instance and leaves the lower/forward instance.

> 2026-06-27 proof-completion update: **upper/back arbitrary-order Theorem 8.5
> lift closed**.  Added the product-aware row identity
> `higham8_4_anyOrder_mulSub_div`, concrete row-tree model
> `BackSubAnyOrderSpec`, row theorem `backSub_anyOrder_row_error`, matrix theorem
> `backSub_backward_error_anyOrder`, and source wrapper
> `higham8_5_backSub_anyOrder_backward_error`.  This assembles
> `(U + ΔU)xhat = b` with `|ΔU_ij| <= γ_n |U_ij|` for arbitrary summation trees
> in each upper-triangular back-substitution row.  At this point, full source
> Theorem 8.5 still needed the analogous lower/forward arbitrary-order lift;
> the following update closes it.

> 2026-06-27 proof-completion update: **full arbitrary-order Theorem 8.5
> closed**.  Mirrored the row-tree construction for lower-triangular forward
> substitution with `ForwardSubAnyOrderSpec`, `forwardSub_anyOrder_row_error`,
> `forwardSub_backward_error_anyOrder`, and
> `higham8_5_forwardSub_anyOrder_backward_error`.  The source theorem now has
> both arbitrary-order upper/back and lower/forward componentwise backward-error
> wrappers at `γ_n`.  The remaining `(8.2)` row is downstream condition-number
> packaging, not a missing substitution backward-error theorem.

> 2026-06-27 proof-completion update: **arbitrary-order equation (8.2) closed**.
> The existing transfer theorem
> `higham8_relative_infNorm_bound_of_componentwise_backward_error` consumes the
> new arbitrary-order Theorem 8.5 certificates directly.  Added
> `higham8_2_backSub_anyOrder_relative_infNorm_bound` and
> `higham8_2_forwardSub_anyOrder_relative_infNorm_bound`, giving the source
> `∞`-norm relative forward-error bound for arbitrary row evaluation orders.

> 2026-06-27 proof-completion update: **Problem 8.1 closed**.  Added
> `TriangularNoGuard.lean`, the no-guard gamma proxy
> `NoGuardFPModel.gammaProxy`, the scalar modified Lemma 8.2 theorem
> `noGuard_mulSub_div_row_tight`, and the upper/lower matrix wrappers
> `noGuard_backSub_backward_error` / `noGuard_forwardSub_backward_error`
> with source-facing Chapter 8 names
> `higham8_problem8_1_noGuard_backSub_backward_error` and
> `higham8_problem8_1_noGuard_forwardSub_backward_error`.  The proved matrix
> envelope is exactly the source Problem 8.1 modification
> `|ΔT| ≤ γ_(n+1)|T|`.

> 2026-06-27 proof-completion update: **exact fan-in factorization (8.12)
> closed**.  Added `higham8_12_lowerColumnFactor`,
> `higham8_12_lowerColumnProductPrefix`, the prefix invariant
> `higham8_12_lowerColumnProductPrefix_apply`, and
> `higham8_12_lowerColumnProduct_eq`, proving every lower-triangular matrix
> satisfies the source product `L = L_1 ... L_n`.

> 2026-06-27 proof-completion update: **fan-in equations (8.14)--(8.20)
> closed as finite-product perturbation wrappers**.  Added the rounded `n=7`
> fan-in expression, finite-product forward bound, residual transfer, normwise
> residual bound, rank-one backward-error transfer, and condition-cubing
> componentwise/relative wrappers.  The theorem surfaces keep the local
> perturbation matrices explicit rather than hiding an unproved rounded-product
> computation theorem.

> 2026-06-27 proof-completion update: **Problem 8.9 reduced to the exact
> spectral foundation**.  Added the Appendix A scaled witness vectors and proved
> `U_n(θ) v = s^(n-2) sqrt(1+c) u` and
> `U_n(θ)^T u = s^(n-2) sqrt(1+c) v` under `c^2+s^2=1`.  Added
> `higham8_problem8_9_kahan_gram_witness`, proving the candidate is a genuine
> Gram eigenpair with eigenvalue `(s^(n-2))^2(1+c)`.  The remaining source row
> is the ordered second-smallest singular-value step: interlacing/ordering must
> show this eigenvalue occupies index `n-2`, or equivalently prove the
> ordered Gram-eigenvalue equality used by
> `higham8_problem8_9_kahan_secondSmallestSingularValue_of_gramEigenvalue`.
> Added the source-side smallest-slot inequality
> `higham8_problem8_9_kahan_smallestSingularValue_le_pow` and strict
> `0 < s < 1` branch
> `higham8_problem8_9_kahan_smallestSingularValue_lt_candidate`, so the
> then-remaining spectral foundation was the singular-value interlacing
> induction, not the Appendix A witness algebra or smallest-slot exclusion.
> Follow-up in the same proof-completion pass added the leading-block identity
> `higham8_11_kahanMatrix_leadingBlock_succ`, nonzero-witness and sorted-list
> membership theorems, the easy ordered upper half
> `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_le_candidate`, bridge
> theorems reducing the final singular-value statement to the single missing
> lower inequality, and the closed `2 × 2` base case
> `higham8_problem8_9_kahan_secondSmallestSingularValue_two`.
> This interlacing induction is now closed by
> `higham8_problem8_9_kahanGram_interlacing` and the final source theorem
> `higham8_problem8_9_kahan_secondSmallestSingularValue`.

## Primary Label Inventory

| Source item | Classification | Previous-split dependency status | Lean declarations | Notes |
| --- | --- | --- | --- | --- |
| Algorithm 8.1, back substitution | `CLOSED` | Uses available Split 1 rounding model through `FPModel`; no unresolved previous-split dependency | `fl_backSub`, `higham8_1_backSub` | Concrete repository algorithm. |
| Lemma 8.2, ordered scalar row error | `CLOSED` | Uses available Split 1 `H03.gamma_theta`; no unresolved previous-split dependency | `BackSubRowSpec`, `backSub_row_tight`, `higham8_2_backSub_row_spec`, `higham8_2_backSub_row_tight` | Row-tight proof chain for the repository evaluation order. |
| Theorem 8.3, Algorithm 8.1 backward error | `CLOSED` | Uses available Split 1 `H02.rounding_model` and `H03.gamma_theta`; no unresolved previous-split dependency | `backSub_backward_error_algorithm_8_1`, `higham8_3_backSub_backward_error` | Row-specific constants match the zero-based Lean translation of the source constants. |
| Lemma 8.4, arbitrary evaluation-order scalar error | `CLOSED` | Built on integrated Split 1 foundations (`SumTree` Algorithm 4.1 + `relErrorCounter` Lemma 3.1); no unresolved wait | `SumTree.backward_error_pivot`, `higham8_4_anyOrder`, `higham8_4_anyOrder_backwardError` | Closed at the sharp source constant `γ_n` (= `γ_k` for `k` summands). The Split-1 summation foundation **does** exist on the current branch (`SumTree.backward_error`); the prior "not found" note was incorrect. The missing piece was the *pivot-normalised* sharpening `SumTree.backward_error_pivot`, which exposes per-leaf factors relative to a distinguished pivot so the shared root-prefix `(1+δ)` factors cancel (Higham's "divide through" step), keeping the constant at `γ_n` rather than `γ_{2n}`. Lemma 8.4's `bₖ ŷ (1+θ₀) = ∑ wᵢ(1+θᵢ)` then follows by one `model_div` factor. `#print axioms`: only `propext`, `Classical.choice`, `Quot.sound`. |
| Theorem 8.5, substitution in any ordering | `CLOSED` | Built on Split 1 + the new Lemma 8.4; no unresolved wait | Fixed-order specializations: `backSub_backward_error`, `forwardSub_backward_error`, `higham8_5_backSub_backward_error`, `higham8_5_forwardSub_backward_error`; arbitrary-order declarations `SumTree.backward_error_pivot`, `higham8_4_anyOrder`, `higham8_4_anyOrder_mulSub_div`, `BackSubAnyOrderSpec`, `ForwardSubAnyOrderSpec`, `backSub_backward_error_anyOrder`, `forwardSub_backward_error_anyOrder`, `higham8_5_backSub_anyOrder_backward_error`, `higham8_5_forwardSub_anyOrder_backward_error` | Fixed forward/back orders are proved, Lemma 8.4 is closed at `γ_n`, and both upper/back and lower/forward arbitrary-order row-tree algorithm models are assembled into `|ΔT| ≤ γ_n|T|`. |
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
| (8.2), forward-error condition-number bound | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | fixed-order upper/lower substitution wrappers `higham8_2_backSub_relative_infNorm_bound`, `higham8_2_forwardSub_relative_infNorm_bound`; arbitrary-order wrappers `higham8_2_backSub_anyOrder_relative_infNorm_bound`, `higham8_2_forwardSub_anyOrder_relative_infNorm_bound` | The repository's fixed-order routines and the arbitrary row-evaluation-order models now satisfy the source `cond(T,x) γ_n / (1 - cond(T) γ_n)` relative `∞`-norm bound. |
| (8.3), stress matrix `U(alpha)` | `CLOSED` | No integrated previous-split blocker | `higham8_3_stressUpper` | Displayed definition. |
| (8.4), displayed inverse-entry formula | `CLOSED` | No integrated previous-split blocker | `higham8_4_stressUpperInvFormula`, `higham8_4_stressUpperInvFormula_isInverse` | Displayed formula is encoded and certified as the exact inverse of the stress family. |
| (8.5), diagonal-dominant upper triangular condition | `CLOSED` | No integrated previous-split blocker | `IsDiagDominantUpper` | Existing predicate. |
| (8.6), lower-triangular analogue | `CLOSED` | No integrated previous-split blocker | `higham8_6_diagDominantLower` | Source-facing predicate. |
| (8.7), comparison matrix | `CLOSED` | No integrated previous-split blocker | `comparisonMatrix`, `higham8_7_comparisonMatrix` | Existing definition plus source wrapper. |
| (8.8), `mu` recurrence | `CLOSED` | Uses available Split 1 gamma infrastructure | `mu`, `mu_closed_form`, `forwardSub_forward_error_mu_bound`, `higham8_10_forwardSub_forward_error_mu_bound` | Encoded as the exact recurrence driving Theorem 8.10. |
| (8.9), Theorem 8.14 norm chain | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_9_comparisonMatrix_condAtSolution_eq`, `higham8_9_upperTriangular_condAtSolution_le_comparison_eq`, `higham8_9_lowerTriangular_condAtSolution_le_comparison_eq`, `higham8_12_infNorm_chain`, `higham8_12_oneNorm_chain`, `higham8_12_opNorm2_chain`, `higham8_12_WMatrix_isDiagDominantUpper`, `higham8_14_WInv_infNorm_upperBound`, `higham8_14_infNorm_lowerBound`, `higham8_14_infNorm_upperBound`, `higham8_14_oneNorm_lowerBound`, `higham8_14_oneNorm_upperBound`, `higham8_14_opNorm2_lowerBound`, `higham8_14_opNorm2_upperBound`, `higham8_5_ZInvFormula_infNorm_eq`, `higham8_5_ZInvFormula_oneNorm_eq`, `higham8_5_ZInvFormula_opNorm2_le`, `higham8_14_ZInvFormula_oneNorm_upperBound`, `higham8_14_ZInvFormula_infNorm_upperBound`, `higham8_14_ZInvFormula_opNorm2_upperBound`, `higham8_14_full_norm_chain` now close the componentwise chain, the concrete `∞/1/2` chains, the `1/2/∞` endpoint bounds, and the packaged source norm chain | Closed by the source-facing wrapper `higham8_14_full_norm_chain`. |
| (8.10), QR column-pivoting inequality | `DEFER-LATER-SPLIT` | No direct integrated Split 1 dependency; later deferred block also uses norm infrastructure | none | Belongs with the later QR/factorization split/chapter material referenced by Problem 19.5. |
| (8.11), Kahan matrix family | `CLOSED` | No unresolved previous-split dependency | `higham8_11_kahanMatrix`, `higham8_11_kahanInvFormula`, `higham8_11_kahanInvFormula_isRightInverse`, `higham8_11_kahanInvFormula_isInverse` | Closed as the source row-scaled stress matrix `diag(1,s,...,s^(n-1)) U(c)` and the displayed inverse formula for `s ≠ 0`; the associated singular-value statement is closed in the Problem 8.9 row. |
| (8.12), fan-in factorization `L=L_1...L_n` | `CLOSED` | No unresolved previous-split dependency | `higham8_12_lowerColumnFactor`; `higham8_12_lowerColumnProductPrefix`; `higham8_12_lowerColumnProductPrefix_apply`; `higham8_12_lowerColumnProduct_eq` | Closed as the exact algebraic lower-column factorization. The subsequent displayed fan-in product, residual, backward-error, forward-error, and condition-cubing rows are closed as the wrapper family `(8.13)`--`(8.20)`. |
| (8.13), fan-in product formula | `CLOSED` | Yes, indirect integrated Split 1 dependency, now discharged locally | `higham8_13_fanIn7Matrix`, `higham8_13_fanIn7Apply`, `higham8_13_sequential7Matrix`, `higham8_13_fanIn7Matrix_eq_sequential7Matrix` | The displayed `n = 7` binary-tree parenthesization is formalized and proved equal to the same exact product. |
| (8.14), rounded fan-in product expansion | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_14_fanIn7RoundedMatrix`; `higham8_14_fanIn7RoundedApply` | Closed as a rounded `n = 7` fan-in matrix expression with explicit local perturbation factors. |
| (8.15), fan-in componentwise residual bound | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_15_residual_componentwise_of_forward_error`; `higham8_15_fanIn_residual_componentwise_bound`; `higham8_15_residualCubeBase` | Closed by residual transfer from the finite-product forward-error bound. |
| (8.16), fan-in norm residual bound | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_16_fanIn_residual_infNorm_bound` | Closed as the infinity-norm lift of the componentwise residual bound. |
| (8.17), Sameh-Brent backward bound | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_17_rankOneBackwardDelta`; `higham8_17_rankOneBackwardDelta_mulVec`; `higham8_17_rankOneBackwardDelta_infNorm_le`; `higham8_17_backward_error_from_residual_infNorm_bound` | Closed by the rank-one backward perturbation construction from the residual norm bound. |
| (8.18), fan-in forward comparison bound | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_18_fanIn_forward_componentwise_bound` | Closed as the componentwise forward-error wrapper over the finite product perturbation API. |
| (8.19), weakened fan-in forward bound | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_19_fanIn_forward_relative_infNorm_bound` | Closed as the relative infinity-norm lift of the fan-in forward-error comparison. |
| (8.20), condition-cubing fan-in bound | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_20_absCondCube`; `higham8_20_forward_componentwise_of_residual_bound`; `higham8_20_forward_relative_infNorm_of_residual_bound`; `higham8_20_condition_cube_envelope_eq`; `higham8_20_condition_cubing_componentwise_bound`; `higham8_20_condition_cubing_relative_infNorm_bound` | Closed as the condition-cubing componentwise and relative infinity-norm envelope. |

## Problems And Appendix A Inventory

Appendix A contains printed solutions for Problems 8.1, 8.2, 8.3, 8.4, 8.5,
8.7, 8.8, 8.9, and 8.10. No printed Appendix A solution for 8.6 was present in
the extracted text.

| Source item | Classification | Previous-split dependency status | Lean declarations or decision | Notes |
| --- | --- | --- | --- | --- |
| Problem 8.1, no guard-digit backward error | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `NoGuardFPModel`; `noGuard_sub_fold_unroll`; `noGuard_mulSub_div_row_tight`; `NoGuardBackSubSpec`; `NoGuardForwardSubSpec`; `noGuard_backSub_backward_error`; `noGuard_forwardSub_backward_error`; `higham8_problem8_1_noGuard_sub_fold_unroll`; `higham8_problem8_1_noGuard_mulSub_div_row_tight`; `higham8_problem8_1_noGuard_backSub_backward_error`; `higham8_problem8_1_noGuard_forwardSub_backward_error` | Closed under Higham's no-guard model (2.6): the scalar modified Lemma 8.2 row keeps `c` unperturbed with source-sharp zero-based bounds `γ_(m+1)` / `γ_(t+3)`, and the upper/lower modified Theorem 8.5 wrappers prove `(T + ΔT)xhat = b`, `|ΔT| ≤ γ_(n+1)|T|`. |
| Problem 8.2, arbitrarily large `||M(T)^-1||/||T^-1||` example | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_2_ratioWitness`, `higham8_2_ratioWitnessInv`, `higham8_2_ratioWitnessComparison`, `higham8_2_ratioWitnessComparisonInv`, `higham8_2_comparisonInverseInfNormRatio_ge_lambda`, `higham8_2_comparisonInverseOneNormRatio_ge_lambda`, `higham8_2_comparisonInverseRatios_arbitrarily_large` | Closed by encoding the Appendix A `3 × 3` witness and proving the `∞`- and `1`-norm comparison-inverse ratios both exceed any prescribed `R` for a suitable `λ ≥ 1`. |
| Problem 8.3, explicit bound from Theorem 8.10 | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_problem8_3_unitUpper_backSub_forward_error_mu_infNorm_bound` | Closed by a source-hypothesis upper-triangular wrapper around the repository's back-substitution routine. The theorem keeps Higham's exact `μ` recurrence instead of introducing a separate `O(u^2)` artifact and uses the exact geometric row-sum bound `2^(n-1-i)`, which is slightly sharper than the printed `2^(n-i)` factor. |
| Problem 8.4, M-matrix `cond(T,x) <= 2n-1` for `x >= 0` | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_4_upperTriangularMMatrix_condAtSolution_le` | Closed in the source upper-triangular M-matrix setting by combining the integrated Chapter 7 condition-at-solution API with a local Appendix A comparison-image bound. |
| Problem 8.5, closed form for `||Z(T)^-1||` | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_12_ZMatrix`, `higham8_12_ZInvFormula`, `higham8_5_ZInvFormula_infNorm_eq`, `higham8_5_ZInvFormula_oneNorm_eq` | Closed exactly in the source norm conventions: `‖Z(T)⁻¹‖₁ = ‖Z(T)⁻¹‖∞ = (β + 1)^(n - 1) / α`. |
| Problem 8.6, efficient computation of `||M(U)^-1 |z|||_inf` and `||W(U)^-1 |z|||_inf` | `CLOSED` | Yes, indirect integrated Split 1 dependency, now discharged locally for the mathematical algorithm spec | `higham8_6_comparisonInverseAbsVec`, `higham8_6_comparisonInverseAbsVecInfNorm`, `higham8_6_WInverseAbsVec`, `higham8_6_WInverseAbsVecInfNorm`, `higham8_6_comparisonInverseAbsVec_recurrence`, `higham8_6_WInverseAbsVec_recurrence`, `higham8_6_comparisonInverseAbsVec_le_WInverseAbsVec`, `higham8_6_comparisonInverseAbsVecInfNorm_le_WInverseAbsVecInfNorm` | Closed by exposing the exact `M(U)⁻¹ |z|` and `W(U)⁻¹ |z|` vectors, proving their backward-sweep row recurrences, and proving the `∞`-norm `M/W` comparison. The source flop counts remain skipped as cost-model prose. |
| Problem 8.7, strictly row diagonally dominant inverse norm theorem | `CLOSED` | Yes, direct integrated Split 1 dependency, now discharged locally | `higham8_7_rowDiagMargin`; `higham8_7_scaledRowDiagMargin`; `higham8_7_scaledStrictRowDiagDominant_invInfNorm_le`; `higham8_7_strictRowDiagDominant_invInfNorm_le`; `higham8_7_comparisonInverseOnes_infNorm_ge_inverseInfNorm` | Closed by the general real square-matrix `∞`-norm inverse bound `‖A⁻¹‖∞ ≤ 1 / min_i α_i`, its positive-diagonal scaled variant `‖A⁻¹‖∞ ≤ ‖D‖∞ / min_i β_i`, and the Chapter 8 comparison-matrix corollary rederiving `‖M(U)⁻¹ e‖∞ ≥ ‖U⁻¹‖∞`. |
| Problem 8.8(a), constructive singular rank-one perturbation when `(A^-1)_{ji} != 0` | `CLOSED` | No integrated previous-split blocker | `higham8_8_rankOne_singular_update` | This is the positive branch of the source iff statement. |
| Problem 8.8(a), converse/no-update branch and best perturbation location | `CLOSED` | No integrated previous-split blocker | `higham8_8_rankOne_singular_update_den_eq_zero`, `higham8_8_rankOne_singular_update_iff`, `higham8_8_rankOne_singular_update_abs_eq_inv_abs_inverse_entry`, `higham8_8_bestRankOneSingularUpdate_of_maxInverseEntry`, `higham8_8_bestRankOneSingularUpdate_exists` | Closed by the exact iff criterion `det(A + α e_i e_j^T) = 0 ↔ (A⁻¹)_{ji} ≠ 0 ∧ α = -((A⁻¹)_{ji})⁻¹`, the source magnitude identity `|α| = |(A⁻¹)_{ji}|⁻¹`, and the Appendix A best-place theorem obtained from a maximal-entry position of `A⁻¹`. |
| Problem 8.8(b), `T_n + alpha e_n e_1^T` singular example | `CLOSED` | Yes, indirect integrated Split 1 dependency, now discharged locally | `higham8_8b_stressUpper_lastFirst_singular_update` | Closed by instantiating the general rank-one singular-update theorem with the stress-family inverse entry `(T_n⁻¹)₁ₙ = 2^(n-2)`. |
| Problem 8.9, Kahan singular-value formula | `CLOSED` | Yes, direct integrated Split 1 dependency, discharged locally | `higham8_11_kahanMatrix_leadingBlock_succ`; `higham8_11_kahanGram_leadingBlock_succ`; `higham8_11_kahanMatrix_zero_one_eq_finiteId`; `higham8_problem8_9_secondSmallestIndex`; `higham8_problem8_9_thirdSmallestIndex`; `higham8_problem8_9_lastIndex`; `higham8_problem8_9_kahanSecondSmallestValue`; `higham8_problem8_9_kahan_secondSmallestSingularValue_of_gramEigenvalue`; `higham8_problem8_9_lastSingularValue_mul_norm_le_image_norm`; `higham8_problem8_9_lastSingularValue_mul_vecNorm_le_matMulVec_norm`; `higham8_problem8_9_kahan_stressInvLastColumn_action`; `higham8_problem8_9_kahan_smallestSingularValue_le_pow`; `higham8_problem8_9_kahan_smallestSingularValue_lt_candidate`; `higham8_problem8_9_kahan_smallestGramEigenvalue_lt_candidate`; `higham8_problem8_9_kahanRightWitness`; `higham8_problem8_9_kahanRightWitness_euclidean_ne_zero`; `higham8_problem8_9_kahanLeftWitness`; `higham8_problem8_9_kahan_witness_forward`; `higham8_problem8_9_kahan_witness_transpose`; `higham8_problem8_9_kahan_gram_witness`; `higham8_problem8_9_kahan_candidate_hasGramEigenvalue`; `higham8_problem8_9_kahan_candidate_mem_gramEigenvalues`; `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_le_candidate`; `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_lower_bound`; `higham8_problem8_9_kahan_secondSmallestSingularValue_of_lower_bound`; `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_two`; `higham8_problem8_9_kahan_secondSmallestSingularValue_two`; `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_interlacing`; `higham8_problem8_9_kahan_secondSmallestSingularValue_of_interlacing`; `higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_zero`; `higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_one`; `higham8_problem8_9_kahan_secondSmallestSingularValue_of_interior_lower_bound`; `higham8_problem8_9_kahan_secondSmallestSingularValue_of_kahanGram_interlacing`; `higham8_problem8_9_kahanGram_interlacing`; `higham8_problem8_9_kahan_secondSmallestSingularValue` | Closed by the Kahan-specific Gram interlacing theorem: the previous-size second-smallest Gram eigenvalue is at most the current third-smallest Gram eigenvalue. The proof uses singular-vector top/tail spans and a dimension-count intersection after appending a zero coordinate to the leading block. Composing this step with the existing induction and edge-case wrappers gives the full source formula under `c, s >= 0` and `c^2 + s^2 = 1`. |
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

## Hidden-Hypothesis And Weak-Component Audit

Final Problem 8.9 theorem assumptions:

- `n : Nat` and `h2 : 2 <= n`: domain/index assumption needed for the
  second-smallest singular-value slot.
- `c s : Real`, `hc : 0 <= c`, `hs : 0 <= s`, and
  `hcs : c^2 + s^2 = 1`: source Kahan-parameter assumptions.

The final theorem `higham8_problem8_9_kahan_secondSmallestSingularValue` does
not assume the target singular-value formula, the Gram equality, or a generic
interlacing theorem.  The formerly conditional step is discharged locally by
`higham8_problem8_9_kahanGram_interlacing`, whose only parameters are `c`, `s`,
and the size/index bound `hm : 3 <= m`.

Weak components checked:

- Kahan Gram interlacing: checked by theorem type, `#print axioms`, and report
  comparison with Appendix A's induction route.
- Final Problem 8.9 theorem: checked by theorem type, `#print axioms`, and
  composition through the all-cases wrapper.
- Documentation/progress claims: checked against `rg` stale-blocker scans,
  lookup entries, and the final focused plus umbrella builds.

No suspicious proof-artifact hypothesis remains on the final Problem 8.9
surface.  The source flop-count and underspecified algorithm-family prose remain
visible as `SKIP` rows rather than hidden proof obligations.

## Current Split 2 Proof/API Targets After Previous-Split Re-Audit

| Row family | Previous split | Contract family or missing result | Direct or indirect | Why not local |
| --- | --- | --- | --- | --- |
| Arbitrary evaluation order: Lemma 8.4 and full Theorem 8.5 | Split 2 (own primary labels) | `SumTree` (Algorithm 4.1) + `relErrorCounter` (Lemma 3.1), both present | Direct | **Closed locally:** Lemma 8.4 / Theorem 8.5 are Split 2's own labels per the blueprint, not a Split-1 reprove. Lemma 8.4 is closed at sharp `γ_n` via `SumTree.backward_error_pivot`; the upper/back arbitrary-order substitution lift is closed by `higham8_5_backSub_anyOrder_backward_error`; the lower/forward lift is closed by `higham8_5_forwardSub_anyOrder_backward_error`. |
| No-guard variant: Problem 8.1 | Split 1 | `H02.rounding_model` / no-guard subtraction variant | Direct | **Closed locally using the existing global no-guard model:** `NoGuardFPModel` supplies (2.6), and Chapter 8 now exposes the modified scalar and upper/lower triangular substitution theorems at `γ_(n+1)`. |
| Condition numbers and norm-general statements around (8.2) | Split 1 | `H06.norms`, `H06.condition_distance`, and condition-number APIs | Direct | Closed locally by reusing the shared API: Theorem 8.12 / Theorem 8.14 wrapper layers are closed, Chapter 9 equation (9.17) consumes Lemma 8.8 through the corrected `condSkeel` wrapper, Problems 8.3, 8.6, and 8.7 are closed, and arbitrary-order `(8.2)` is now closed by `higham8_2_backSub_anyOrder_relative_infNorm_bound` / `higham8_2_forwardSub_anyOrder_relative_infNorm_bound`. |
| Singular-value/Kahan rows: Problem 8.9 | Split 1 | `H06.svd` and singular-value span/factorization lemmas | Direct | **Closed locally:** Equation (8.11), its inverse formula, the leading-block identity, Appendix A's explicit scaled Kahan singular-vector witnesses, sorted-list candidate membership, the easy ordered upper half, the lower-bound bridge, the `n = 2` base case, `s = 0`, `s = 1`, the all-cases reduction wrapper, the Kahan Gram interlacing step, and the final source singular-value theorem are all closed. |
| Fan-in equations (8.14)-(8.20) | Split 1 | `H03.gamma_theta` matrix-product/fan-in rounding; `H06.norms` for norm forms | Direct for rounding/norm bounds; indirect through the current fan-in algorithm interface | **Closed locally:** exact factorization `(8.12)`, exact `n = 7` product `(8.13)`, rounded expression `(8.14)`, residual/backward-error rows `(8.15)`--`(8.17)`, forward-error rows `(8.18)`--`(8.19)`, and condition-cubing row `(8.20)` are now exposed as compiling theorem surfaces with explicit perturbation hypotheses. |

## Verification Ledger

Focused commands run after the final Chapter 8 selected-scope completion audit
(2026-06-27):

- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter8`
- `lake env lean examples/LibraryLookup.lean > /tmp/librarylookup_ch8_final_audit.errout 2>&1`
- `lake env lean --stdin` with `#print axioms` for
  `higham8_problem8_9_kahanGram_interlacing`,
  `higham8_problem8_9_kahan_secondSmallestSingularValue`, and
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_kahanGram_interlacing`.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean examples/LibraryLookup.lean`
- `rg` stale-blocker scans over the Chapter 8 report, unified Split 2 report,
  and FLARE dev-log status files.
- `rg` whitespace/conflict-marker scan over the FLARE dev-log files touched by
  this audit.
- `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter8_formalization_report.md chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md`
- `lake build LeanFpAnalysis.FP.Algorithms`

Results:

- Focused Chapter 8 Lean check, focused Chapter 8 module build, lookup check,
  and umbrella `LeanFpAnalysis.FP.Algorithms` build all passed.  The lookup
  output had 54206 lines.
- `#print axioms` for the final Kahan interlacing and singular-value surfaces
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Focused implementation/lookup placeholder scan found no `sorry`, `admit`,
  `axiom`, `unsafe`, or `opaque`.
- Stale Chapter 8 blocker scans found no active Problem 8.9 blocker text in
  the active Chapter 8 report/live-log surfaces; the unified report now points
  to the live Chapter 8 selected-scope `PASS` state.
- `git diff --check` passed for the touched repository files, and the direct
  dev-log whitespace/conflict-marker scan had no matches.
- The umbrella build emitted only pre-existing linter warnings in
  `QR/GivensSpec.lean` and `FastMatMul.lean`; no new Chapter 8 warning was
  emitted.

Focused commands run after the Problem 8.9 Kahan Gram interlacing closure pass
(2026-06-27):

- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter8`
- `lake env lean examples/LibraryLookup.lean > /tmp/librarylookup_ch8_kahan_closure.errout 2>&1`
- `lake env lean --stdin` with `#print axioms` for
  `higham8_problem8_9_kahanGram_interlacing`,
  `higham8_problem8_9_kahan_secondSmallestSingularValue`, and
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_kahanGram_interlacing`.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean examples/LibraryLookup.lean`
- `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter8_formalization_report.md`
- `lake build LeanFpAnalysis.FP.Algorithms`

Results:

- Focused `HighamChapter8.lean`, `HighamChapter8` module build, and
  `examples/LibraryLookup.lean` all passed; the redirected lookup output has
  54206 lines.
- `#print axioms` for the Kahan Gram interlacing theorem, the final Problem
  8.9 singular-value theorem, and the all-cases interlacing wrapper reported
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Focused implementation/lookup placeholder scan found no `sorry`, `admit`,
  `axiom`, `unsafe`, or `opaque`.
- `git diff --check` passed for the touched Lean/docs/report files.
- Umbrella `LeanFpAnalysis.FP.Algorithms` build passed:
  `Build completed successfully (3458 jobs)`.  The only emitted warnings were
  pre-existing linter warnings in `QR/GivensSpec.lean` and `FastMatMul.lean`;
  no new Chapter 8 warnings were emitted.

Focused commands run after the Problem 8.9 Kahan Gram interlacing-reduction
pass (2026-06-27):

- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter8`
- `lake env lean examples/LibraryLookup.lean > /tmp/librarylookup_ch8_interlacing.errout 2>&1`
- `lake env lean --stdin` with `#print axioms` for
  `higham8_11_kahanGram_leadingBlock_succ`,
  `higham8_problem8_9_kahan_smallestGramEigenvalue_lt_candidate`,
  `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_interlacing`,
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_interlacing`,
  and `higham8_problem8_9_kahan_secondSmallestSingularValue_of_kahanGram_interlacing`.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean examples/LibraryLookup.lean`
- `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter8_formalization_report.md chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md`
- `lake build LeanFpAnalysis.FP.Algorithms`

Results:

- Focused `HighamChapter8.lean`, `HighamChapter8` module build, and
  `examples/LibraryLookup.lean` all passed; the redirected lookup output has
  54196 lines.
- `#print axioms` for the new Kahan Gram block identity, smallest-slot
  exclusion, interlacing-to-source induction wrapper, singular-value wrapper,
  and all-cases interlacing wrapper reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Focused implementation/lookup placeholder scan found no `sorry`, `admit`,
  `axiom`, `unsafe`, or `opaque`.
- `git diff --check` passed for the touched Lean/docs/report files.
- Umbrella `LeanFpAnalysis.FP.Algorithms` build passed:
  `Build completed successfully (3458 jobs)`.  The only emitted warnings were
  pre-existing linter warnings in `QR/GivensSpec.lean` and `FastMatMul.lean`;
  no new Chapter 8 warnings were emitted.

Focused commands run after the Problem 8.9 edge-case and all-cases reduction
pass (2026-06-27):

- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter8`
- `lake env lean examples/LibraryLookup.lean`
- `printf ... | lake env lean --stdin` with `#print axioms` for
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_zero`,
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_s_eq_one`,
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_interior_lower_bound`,
  `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_s_eq_zero`,
  and `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_s_eq_one`.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean examples/LibraryLookup.lean`
- `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter8_formalization_report.md chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md`
- `lake build LeanFpAnalysis.FP.Algorithms`

Results:

- Focused `HighamChapter8.lean`, `HighamChapter8` module build, and
  `examples/LibraryLookup.lean` all passed.
- `#print axioms` for the new edge-case and reduction declarations reported
  only `propext`, `Classical.choice`, and `Quot.sound`.
- Focused implementation/lookup placeholder scan found no `sorry`, `admit`,
  `axiom`, `unsafe`, or `opaque`.
- `git diff --check` passed for the touched Lean/docs/report files.
- Umbrella `LeanFpAnalysis.FP.Algorithms` build passed:
  `Build completed successfully (3458 jobs)`.  The only emitted warnings were
  pre-existing linter warnings in `QR/GivensSpec.lean` and `FastMatMul.lean`;
  no new Chapter 8 warnings were emitted.

Focused commands run after the Problem 8.9 sorted-candidate / lower-bound
bridge / `n = 2` base-case pass (2026-06-27):

- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter8`
- `lake env lean examples/LibraryLookup.lean > /tmp/librarylookup_ch8.out`
- `printf ... | lake env lean --stdin` with `#print axioms` for
  `higham8_11_kahanMatrix_leadingBlock_succ`,
  `higham8_problem8_9_kahanRightWitness_euclidean_ne_zero`,
  `higham8_problem8_9_kahan_candidate_hasGramEigenvalue`,
  `higham8_problem8_9_kahan_candidate_mem_gramEigenvalues`,
  `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_le_candidate`,
  `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_of_lower_bound`,
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_lower_bound`,
  `higham8_problem8_9_kahan_secondSmallestGramEigenvalue_eq_candidate_two`,
  and `higham8_problem8_9_kahan_secondSmallestSingularValue_two`.
- `lake build LeanFpAnalysis.FP.Algorithms`
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean examples/LibraryLookup.lean`
- `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter8_formalization_report.md chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md`

Results:

- Focused `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
  passed.
- Focused `HighamChapter8` build passed:
  `Build completed successfully (3037 jobs).`
- `examples/LibraryLookup.lean` passed after the refreshed
  `HighamChapter8` object was built and now exposes the new Kahan
  leading-block, membership, upper-half, lower-bound bridge, and `n = 2`
  base-case declarations.
- `#print axioms` for the new Problem 8.9 declarations reported only the
  standard classical/library axioms `propext`, `Classical.choice`, and
  `Quot.sound`.
- Umbrella `LeanFpAnalysis.FP.Algorithms` build passed:
  `Build completed successfully (3458 jobs)`.  It replayed pre-existing
  unused-simp/unused-variable warnings in `QR/GivensSpec.lean` and
  `FastMatMul.lean`; no new Chapter 8 warnings were emitted.
- Placeholder scan over the touched Lean/example files found no `sorry`,
  `admit`, `axiom`, `unsafe`, or `opaque`.
- `git diff --check` passed for the touched Lean/docs/report files.

Focused commands run after the Lemma 8.4 arbitrary-order pass (2026-06-26):

- `lake env lean LeanFpAnalysis/FP/Algorithms/TriangularArbitraryOrder.lean`
  (clean: no errors, warnings, `sorry`, `admit`, `axiom`, `unsafe`, `opaque`).
- `lake build LeanFpAnalysis.FP.Algorithms.TriangularArbitraryOrder`
  → `Build completed successfully (2120 jobs).`
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter8`
  → `Build completed successfully (3036 jobs).`
- `#print axioms higham8_4_anyOrder` and `#print axioms
  SumTree.backward_error_pivot` → only `propext`, `Classical.choice`,
  `Quot.sound`.

New declarations: `SumTree.backward_error_pivot` (pivot-normalised summation-tree
backward error, sharp `γ_{n-1}` leaf/pivot ratio),
`higham8_relErrorCounter_one`, `higham8_relErrorCounter_single`,
`higham8_relErrorCounter_pad`, `higham8_relErrorCounter_pos`,
`higham8_4_anyOrder` (Lemma 8.4), and the Chapter 8 wrapper
`higham8_4_anyOrder_backwardError`.  New file
`LeanFpAnalysis/FP/Algorithms/TriangularArbitraryOrder.lean`, registered in
`LeanFpAnalysis/FP/Algorithms.lean` and imported by `HighamChapter8.lean`.

Focused commands run after the upper/back arbitrary-order Theorem 8.5 pass
(2026-06-27):

- `lake env lean LeanFpAnalysis/FP/Algorithms/TriangularArbitraryOrder.lean`
  (clean).
- `lake build LeanFpAnalysis.FP.Algorithms.TriangularArbitraryOrder`
  → `Build completed successfully (2120 jobs).`
- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
  passed with only the pre-existing nonfatal `ring_nf`/simp warnings.
- `lake build LeanFpAnalysis.FP.Algorithms.TriangularArbitraryOrder
  LeanFpAnalysis.FP.Algorithms.HighamChapter8`
  → `Build completed successfully (3036 jobs).`
- `lake env lean examples/LibraryLookup.lean`
  passed after prefixing the Chapter 8 local `relErrorCounter` helpers to avoid
  the existing `Horner` import name `relErrorCounter_one`.
- `#print axioms` for `higham8_4_anyOrder_mulSub_div`,
  `backSub_backward_error_anyOrder`, and
  `higham8_5_backSub_anyOrder_backward_error` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b"` over the touched Lean files
  found no placeholders.
- `git diff --check` over the touched Lean/docs/report files passed.

New declarations: `higham8_4_anyOrder_mulSub_div`,
`backSubAnyOrderRowTerms`, `BackSubAnyOrderSpec`,
`backSub_anyOrder_row_error`, `backSub_backward_error_anyOrder`, and
`higham8_5_backSub_anyOrder_backward_error`.  The helper counter declarations
are intentionally Chapter-8-prefixed (`higham8_relErrorCounter_one`,
`higham8_relErrorCounter_single`, `higham8_relErrorCounter_pad`,
`higham8_relErrorCounter_pos`) to avoid import-order collisions.

Focused commands run after the lower/forward arbitrary-order Theorem 8.5 pass
(2026-06-27):

- `lake env lean LeanFpAnalysis/FP/Algorithms/TriangularArbitraryOrder.lean`
  (clean).
- `lake build LeanFpAnalysis.FP.Algorithms.TriangularArbitraryOrder
  LeanFpAnalysis.FP.Algorithms.HighamChapter8`
  → `Build completed successfully (3036 jobs).`
- `lake env lean examples/LibraryLookup.lean > /tmp/librarylookup_ch8.out`
  passed.
- `#print axioms` for `forwardSub_backward_error_anyOrder` and
  `higham8_5_forwardSub_anyOrder_backward_error` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Placeholder scan over the touched Lean files found no `sorry`, `admit`,
  `axiom`, `unsafe`, or `opaque`.
- `git diff --check` over the touched Lean/docs/report files passed.

New declarations: `forwardSubAnyOrderRowTerms`, `ForwardSubAnyOrderSpec`,
`forwardSub_anyOrder_row_error`, `forwardSub_backward_error_anyOrder`, and
`higham8_5_forwardSub_anyOrder_backward_error`.

Focused commands run after the arbitrary-order `(8.2)` pass (2026-06-27):

- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter8`
  → `Build completed successfully (3036 jobs).`
- `lake env lean examples/LibraryLookup.lean > /tmp/librarylookup_ch8.out`
  passed.
- `#print axioms` for `higham8_2_backSub_anyOrder_relative_infNorm_bound`
  and `higham8_2_forwardSub_anyOrder_relative_infNorm_bound` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Placeholder scan over the touched Lean files found no `sorry`, `admit`,
  `axiom`, `unsafe`, or `opaque`.
- `git diff --check` over the touched Lean/docs/report files passed.

New declarations: `higham8_2_backSub_anyOrder_relative_infNorm_bound` and
`higham8_2_forwardSub_anyOrder_relative_infNorm_bound`.

Focused commands run after the no-guard Problem 8.1 pass (2026-06-27):

- `lake env lean LeanFpAnalysis/FP/Algorithms/TriangularNoGuard.lean`
  passed.
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter8`
  → `Build completed successfully (3037 jobs)` with only pre-existing
  nonfatal local linter hints in `HighamChapter8.lean`.
- `lake build LeanFpAnalysis.FP.Algorithms.QR.GramSchmidt`
  passed after renaming the QR-local duplicate theorem
  `opNorm2Le_mono` to `qr_opNorm2Le_mono`.
- `lake build LeanFpAnalysis.FP.Algorithms`
  → `Build completed successfully (3458 jobs)`, restoring the umbrella
  `LeanFpAnalysis.FP.Algorithms` import used by `LeanFpAnalysis.FP`.
- `lake env lean examples/LibraryLookup.lean > /tmp/librarylookup_ch8.out`
  passed.
- `#print axioms` for `noGuard_mulSub_div_row_tight`,
  `noGuard_backSub_backward_error`, `noGuard_forwardSub_backward_error`,
  `higham8_problem8_1_noGuard_mulSub_div_row_tight`,
  `higham8_problem8_1_noGuard_backSub_backward_error`, and
  `higham8_problem8_1_noGuard_forwardSub_backward_error` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Placeholder scan over the touched Lean files found no `sorry`, `admit`,
  `axiom`, `unsafe`, or `opaque`.
- `git diff --check` over the touched Lean/docs/report files passed.

New declarations: `NoGuardFPModel.gammaProxy`, `noGuardGamma`,
`noGuardGammaValid`, `noGuard_mulSub_div_row_tight`,
`noGuardBackSubRowFold`, `NoGuardBackSubSpec`,
`noGuard_backSub_row_error`, `noGuard_backSub_backward_error`,
`noGuardForwardSubRowFold`, `NoGuardForwardSubSpec`,
`noGuard_forwardSub_row_error`, `noGuard_forwardSub_backward_error`, and the
source-facing Problem 8.1 wrappers listed in the inventory above.

Focused commands run after the Kahan `(8.11)` pass:

- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter8`
- `printf ... | lake env lean --stdin` with `#print axioms` for
  `higham8_11_kahanInvFormula_isRightInverse` and
  `higham8_11_kahanInvFormula_isInverse`.
- `printf ... | lake env lean --stdin` with `#print axioms` for
  `higham8_13_fanIn7Matrix_eq_sequential7Matrix`.
- `lake env lean examples/LibraryLookup.lean`
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean chapter_splitting/reports/chapter8_formalization_report.md`
- `git diff --check -- LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean chapter_splitting/reports/chapter8_formalization_report.md`

Results:

- Focused `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
  passed.
- Focused `HighamChapter8` build passed:
  `Build completed successfully (3031 jobs).`
- `#print axioms` for the two final-facing Kahan inverse theorems reported only
  the standard classical/library axioms `propext`, `Classical.choice`, and
  `Quot.sound`.
- `#print axioms` for the exact fan-in parenthesization theorem reported only
  the standard classical/library axioms `propext`, `Classical.choice`, and
  `Quot.sound`.
- `examples/LibraryLookup.lean` passed and now exposes the Kahan `(8.11)` and
  fan-in `(8.13)` support declarations.
- Code scan found no Lean placeholders in the touched Chapter 8 Lean file; the
  report hits are the literal audit-command text and prior audit summary.
- `git diff --check` passed for the touched Lean/report files.

Focused commands run after the fan-in `(8.14)`--`(8.20)` and Problem 8.9
Kahan-witness / smallest-slot pass (2026-06-27):

- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter8`
- `lake build LeanFpAnalysis.FP.Algorithms`
- `lake env lean examples/LibraryLookup.lean > /tmp/librarylookup_ch8.out`
- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/TriangularNoGuard.lean LeanFpAnalysis/FP/Algorithms/TriangularArbitraryOrder.lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean LeanFpAnalysis/FP/Algorithms/QR/GramSchmidt.lean examples/LibraryLookup.lean`
- `printf ... | lake env lean --stdin` with `#print axioms` for
  `higham8_14_fanIn7RoundedMatrix`,
  `higham8_18_fanIn_forward_componentwise_bound`,
  `higham8_19_fanIn_forward_relative_infNorm_bound`,
  `higham8_15_fanIn_residual_componentwise_bound`,
  `higham8_16_fanIn_residual_infNorm_bound`,
  `higham8_17_backward_error_from_residual_infNorm_bound`,
  `higham8_20_condition_cubing_relative_infNorm_bound`,
  `higham8_problem8_9_kahan_secondSmallestSingularValue_of_gramEigenvalue`,
  `higham8_problem8_9_kahan_smallestSingularValue_le_pow`,
  `higham8_problem8_9_kahan_smallestSingularValue_lt_candidate`,
  `higham8_problem8_9_kahan_witness_forward`, and
  `higham8_problem8_9_kahan_witness_transpose`, and
  `higham8_problem8_9_kahan_gram_witness`.
- `git diff --check --` over the touched Lean/docs/report files.

Results:

- Focused `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
  passed.
- Focused `HighamChapter8` build passed:
  `Build completed successfully (3037 jobs).`
- Umbrella `LeanFpAnalysis.FP.Algorithms` build passed:
  `Build completed successfully (3458 jobs).`
- `examples/LibraryLookup.lean` passed and now exposes the fan-in
  `(8.14)`--`(8.20)` wrappers and the Problem 8.9 reduction/witness and
  smallest-slot declarations.
- Placeholder scan over the touched Lean files found no `sorry`, `admit`,
  `axiom`, `unsafe`, or `opaque`.
- `#print axioms` for the fan-in wrappers, Kahan reduction wrapper, Kahan
  witness theorems, Gram-witness theorem, and smallest-slot theorems reported
  only the standard
  classical/library axioms
  `propext`, `Classical.choice`, and `Quot.sound`.
- `git diff --check` passed for the touched Lean/docs/report files.

Oracle/GPT Pro proof-source note:

- A compact math-only consultation packet for the Problem 8.9 Kahan ordered
  singular-value/interlacing blocker was prepared, but the sandbox approval
  reviewer rejected the external Oracle/ChatGPT export because it would send
  private project/API details to an external model. No external content was
  sent.
  That row family and the fan-in wrapper family are now closed locally.  The
  former Problem 8.9 ordered Kahan singular-value/interlacing obstruction is
  closed by `higham8_problem8_9_kahanGram_interlacing`, so no external
  proof-source result was used.

## GitHub Synchronization

- Local branch: `main`.
- Local commit at audit: `a028f28`.
- Remote tracking ref after `git fetch origin`: `origin/main` at `c6d03f1`.
- Sync status: local branch is `ahead 6, behind 6` relative to `origin/main`.
- Milestone commit and split prefix: not created in this pass because the
  worktree contains mixed staged and unstaged changes across Chapter 8 work and
  unrelated files.
- Pushed to `origin/main`: no.
- Synchronization blocker: `git status -sb` shows a dirty mixed worktree, so the
  shared-main merge/push workflow must wait for a clean ownership boundary or
  an explicit user instruction. No merge or conflict resolution was attempted
  during this audit.

Focused commands run after the Problem 8.6 pass:

- `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
- `lake build LeanFpAnalysis.FP.Algorithms.HighamChapter8`
- `lake env lean examples/LibraryLookup.lean > /tmp/librarylookup.out 2>&1`
- `printf ... | lake env lean --stdin` with `#print axioms` for
  `higham8_6_comparisonInverseAbsVec_recurrence`,
  `higham8_6_WInverseAbsVec_recurrence`,
  `higham8_6_comparisonInverseAbsVec_le_WInverseAbsVec`, and
  `higham8_6_comparisonInverseAbsVecInfNorm_le_WInverseAbsVecInfNorm`.

Repository health commands run after this pass:

- `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean LeanFpAnalysis/FP/Algorithms/TriangularForwardComparison.lean LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean examples/LibraryLookup.lean`
- `rg -n "TODO|FIXME" LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean LeanFpAnalysis/FP/Algorithms/TriangularForwardComparison.lean LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean examples/LibraryLookup.lean`
- `git diff --check`

Results:

- Focused `lake env lean LeanFpAnalysis/FP/Algorithms/HighamChapter8.lean`
  passed.
- Focused `HighamChapter8` build passed:
  `Build completed successfully (3031 jobs).`
- `examples/LibraryLookup.lean` passed and now exposes
  the eight Problem 8.6 declarations listed above together with the previously
  refreshed Chapter 8 source wrappers.  The command was captured to `/tmp`
  because the full `#check` stream is very large.
- `#print axioms` for the four final-facing Problem 8.6 theorems reported only
  the standard classical/library axioms `propext`, `Classical.choice`, and
  `Quot.sound`.
- Code scan over the touched Chapter 8 and rebuild-support Lean files plus the
  lookup example found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`,
  `TODO`, or `FIXME`.
- `git diff --check` passed.

The Lean file and lookup example contain no new `sorry`, `admit`, `axiom`, or
`unsafe`, and the refreshed Chapter 8 surfaces compile cleanly on the current
branch.
