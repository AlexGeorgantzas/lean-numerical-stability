# Chapter 7 Formalization Report

Date: 2026-06-25; latest audit update: 2026-06-26.
Source: `/home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.ch7.pdf`.
Appendix source read: `/home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.appa.pdf`.
Split contract: Split 2, Chapter 7.
Planning documents consulted: `/home/mymel/flare-bundle/higham-split/planning/HIGHAM_PARALLEL_FORMALIZATION_BLUEPRINT.md`,
`/home/mymel/flare-bundle/higham-split/planning/split_primary_contracts.md`,
and `/home/mymel/flare-bundle/higham-split/planning/chapter_index.md`.
Current authoritative status: see `2026-06-26 Problem 7.5 SVD perturbation
closure and final Split 2 re-audit` at the end of this report. Historical
intermediate sections are retained as ledger history and may mention blockers
that are now superseded.

## Summary

The library contains substantial Chapter 7 perturbation theory in
`PerturbationTheory.lean` and source-facing Chapter 7 wrappers in
`LeanFpAnalysis.FP.Analysis.HighamChapter7`.

The first proof-completion update added Problem 7.7's Split 2-local comparison
theorems for both the componentwise Oettli-Prager surface and the infinity-norm
Rigal-Gaches surface:

- `problem7_7_componentwise_abs_rhs_to_zero_rhs_residual_bound`
- `problem7_7_componentwise_zero_rhs_feasible_of_abs_rhs_feasible`
- `problem7_7_normwise_inf_residual_bound`
- `problem7_7_normwise_zero_rhs_feasible_of_abs_rhs_feasible`

The local-infrastructure update added the two remaining Split 2-local items
identified after excluding direct/indirect Split 1 dependencies:

- Problem 7.1 local Neumann and exact resolvent infrastructure:
  `ch7Problem71ContractionMatrix`,
  `problem7_1_componentwise_contraction_ineq`,
  `problem7_1_componentwise_neumann_scalar_bound`,
  `ch7NonnegativeResolvent`,
  `problem7_1_resolvent_componentwise_inequality_bound`,
  `ch7NonnegativeResolvent_nonsingInv_of_infNormBound`,
  `problem7_1_componentwise_resolvent_bound`, and
  `problem7_1_componentwise_nonsingInv_resolvent_bound`.
- Problem 7.8 rectangular Frobenius minimization, encoded as lower bound plus
  rank-one attainment:
  `problem7_8_frobenius_characterization_pos`,
  `problem7_8_rankOne_attains_pos`,
  `problem7_8_zero_parameter_attains`, and
  `problem7_8_source_value_eq_augmented_value`.

The 2026-06-24 computed-residual re-audit checked the old Split 1 wait rows
against the integrated branch `split2-integrate-kimon-main` after Kimon's
`origin/main` merge through `e7269ce`. This closed the Chapter 7 practical
computed-residual equations directly on the current branch:

- Equation (7.30): `eq_7_30_conventional_residual_error`
- Equation (7.31) source-shaped computed-residual safety term/image plus
  componentwise and relative-infinity-norm bounds:
  `ch7ComputedResidualSafetyTerm`,
  `ch7ComputedResidualImage`,
  `eq_7_31_componentwise_bound`, and
  `eq_7_31_relative_infNorm_bound`

The same re-audit showed that Problem 7.13 is no longer a valid previous-split
wait. The current pass now closes the sparse computed-residual row from
Appendix A.12 by introducing a support-compressed sparse matvec/residual model
that skips structural zeros and tracks row budgets `γ_(w_i+1)`:

- `ch7SparseResidual`
- `ch7SparseComputedResidualSafetyTerm`
- `ch7SparseComputedResidualImage`
- `problem7_13_sparse_residual_error`
- `problem7_13_componentwise_bound`
- `problem7_13_relative_infNorm_bound`

The current condition-number pass closes the remaining source-model choice for
equation `(7.12)` in the Skeel infinity-norm specialization by defining the
global nonzero-solution supremum and proving it equals Higham's `cond(A)`.
It also formalizes the adjacent source prose that the `f = |b| = |Ax|`
componentwise-data condition differs from `cond(A,x)` by at most a factor `2`:

- `ch7CondEFGlobalInf`
- `ch7SkeelGlobalCondInf`
- `ch7SkeelCondAtSolutionInf_le_condSkeel`
- `eq_7_12_skeel_global_conditionNumber_eq_condSkeel`
- `ch7ComponentwiseDataCondAtSolutionInf`
- `ch7SkeelCondAtSolutionInf_le_componentwiseDataCondAtSolutionInf`
- `ch7ComponentwiseDataCondAtSolutionInf_le_two_mul_skeelCondAtSolutionInf`

The current row-scaling pass closes the Appendix A.3 row-equilibration
dependency package, the positive-row-scaling infimum model of equation
`(7.15)`, and equation `(7.16)` for a positive diagonal row-equilibrating
scaling:

- `ch7RowScale`
- `ch7InverseRowScale`
- `ch7RowsEquilibratedInf`
- `ch7RowScale_inverse`
- `ch7_condSkeel_rowScale_eq`
- `ch7_condSkeel_eq_kappaInf_of_rowsEquilibratedInf`
- `problem7_3_rowEquilibrated_scaling_condition_eq`
- `problem7_3_rowEquilibrated_kappaInf_le_diagKappa_mul_condSkeel`
- `problem7_3_rowEquilibrated_lower_bound`
- `eq_7_16_rowEquilibrated_bounds`
- `ch7PositiveRowScaledKappaInfSet`
- `ch7RowEquilibratingScale`
- `ch7RowsEquilibratedInf_rowEquilibratingScale_of_right_inverse`
- `eq_7_15_positive_rowScaling_sInf_eq_condSkeel_of_right_inverse`

The current van der Sluis dependency pass closes the finite Euclidean
column-equilibration inequalities behind equations `(7.20)` and `(7.21)` in
the repository's `rectOpNorm2Le` operator-certificate form.  It also closes
the `p = 1` column-equilibration specialization of `(7.21)`, the inverse-side
algebraic inequality `(7.22)` for an explicit inverse-side matrix, and the
pairwise `p = 1` column-scaling bound behind `(7.18)`.  Later continuations
close the analogous `p = ∞` row-equilibration specialization of `(7.19)`,
including the inverse-side algebraic inequality for an explicit inverse-side
matrix, and the `p = 2` pairwise column-scaling condition-product bound
`κ₂(AD_C) <= sqrt(n) κ₂(AD)` for an explicit inverse-side matrix.  The latest
continuation packages these pairwise inequalities as `sInf` wrappers over
reciprocal diagonal scaling value sets for the `p = 1`, `p = 2`, and `p = ∞`
specialized explicit-`Aplus` models.  This pass also closes the Corollary 7.6
Cholesky-factor bridge showing that the source SPD scale
`D* = diag(a_jj^{-1/2})` is exactly the `p = 2` column-equilibrating scale for
a factor `R` with `A = RᵀR` on the diagonal, and instantiates the closed
Theorem 7.5 `p = 2` `sInf` wrapper for that Cholesky factor.  This is genuine
proof work.  The latest continuation also proves the explicit Cholesky inverse
Gram certificate and product-square bridge: if `A = RᵀR`, `Rinv` inverts `R`,
and `d*dInv=1`, then `D⁻¹(Rinv Rinvᵀ)D⁻¹` is a genuine inverse-side witness
for `DAD`, and the corresponding operator-2 product equals the square of the
right-scaled Cholesky-factor product.  This continuation squares the closed
factor `sInf` inequality to prove the source SPD scale is bounded by
`n * (sInf factor-values)^2`.  The latest two-sided transfer continuation
defines the symmetric SPD scaling value set, proves the Cholesky-factor
infimum square is bounded by the infimum over reciprocal two-sided scalings of
`DAD`, and closes the source-scale Corollary 7.6 bound in the repository's
`sInf` model:
`κ₂(D*AD*) <= n * sInf {κ₂(DAD)}`.  This is a stronger infimum-form statement
than the source `min` wording when a minimizer exists; no separate minimizer
existence or attainment theorem is asserted.  The latest finite-real `p`
continuation closes the source equations `(7.20)` and `(7.21)` column-bound
dependencies for `1 <= p < ∞`: every column `p`-norm is bounded by the local
least matrix `p`-norm, a uniform column bound `B` gives
`‖A‖_p <= n^(1-1/p) B`, and the reciprocal column-equilibrating scale gives
`‖A D_C‖_p <= n^(1-1/p)` when all source column norms are positive.  The
newest finite-real `p` continuation also closes the explicit inverse-side
inequality `(7.22)` and the resulting pairwise/`sInf` `(7.18)` bound over
reciprocal right-scalings for the explicit `Aplus` condition-product model,
using `complexMatrixLpNormOfReal_mul_le` and a proved finite-`Lp`
coordinatewise diagonal multiplier bound.  This continuation closes the
conjugate-row finite-real `p` proof-route branch for `(7.19)`: using the
source proof's transpose identity `(6.21)`, it proves the dual-row
equilibrated matrix-norm bound, the explicit inverse-side inequality for
`Aplus D^{-1}`, and pairwise/`sInf` left-scaling wrappers over reciprocal
diagonal row scalings.  The printed source row scale still remains visible in
the full theorem ledger, since the PDF states `‖A(i,:)‖_p` while the proof
route uses the Holder-conjugate row norm.  The full source Theorem 7.5 remains
open for the Moore-Penrose existence/projection wrapper, printed row-scale
reconciliation, and proof that the general/non-endpoint value sets attain their
infima.  Conditional source-`min` adapters now rewrite the existing finite-real
and `p = 2` non-endpoint `sInf` bounds through supplied `IsLeast`
certificates.  The endpoint `p = 1` column-scaling and `p = ∞` row-scaling
explicit-`Aplus` models now have genuine least-element witnesses.  The latest
rank-side continuation proves the positivity side conditions for the
finite-real column, `p = 1`, `p = 2`, conjugate-row, and endpoint row models
from explicit rectangular one-sided inverse witnesses (`Aplus A = I` or
`A Aplus = I`) and adds source-shaped wrappers that no longer require separate
nonzero-column/nonzero-row hypotheses.  The current rank-form continuation
proves that injectivity of the rectangular map `x ↦ A*x` yields a concrete
left-inverse matrix and that surjectivity yields a concrete right-inverse
matrix, then adds existential Theorem 7.5 wrappers for the already-proved
column and row specializations.  The latest source-rank continuation proves
that Mathlib's real rectangular matrix rank condition `(Matrix.of A).rank = n`
implies injectivity and `(Matrix.of A).rank = m` implies surjectivity by
rank-nullity, then adds source-facing wrappers matching the printed
`rank(A) = n` and `rank(A) = m` hypotheses for the same closed column and row
specializations.  The latest projection-dependency continuations add reusable
rectangular product identity/associativity APIs, prove that `A Aplus` and
`Aplus A` are idempotent from explicit one-sided inverse witnesses, prove the
corresponding operator-2 nonexpansiveness certificates when the induced
projection is also symmetric, prove the range-fixing, residual orthogonality,
squared-/ordinary-norm best-approximation inequalities, and package those
inequalities as set-level `IsLeast` projection-minimizer declarations for those
symmetric projections.  These are genuine
algebraic and symmetric-idempotent projection facts needed by the
Moore-Penrose route, but they do not construct a Moore-Penrose inverse or
discharge the construction-side Penrose witnesses.  The Penrose-bridge
continuation closes the next source-facing dependency: from the first Penrose
equation `A A⁺ A = A`, injectivity of `x ↦ A*x` proves `A⁺ A = I`, while
surjectivity proves `A A⁺ = I`.  Rank-nullity wrappers specialize these to the
printed `rank(A)=n/m` hypotheses, and the symmetric-projection contraction,
orthogonality, and least-residual wrappers now consume Penrose equation plus
rank/injectivity/surjectivity directly.  The newest continuation proves that
an explicit one-sided inverse plus the relevant projection symmetry supplies
the full four-condition Penrose equation package; rank/injective/surjective
wrappers expose the same package under `AA⁺A=A` plus the printed rank
hypotheses.  The current source-rank/min continuation adds Penrose1-plus-
matrix-rank adapters for the `p = 1` and `p = ∞` endpoint least-element
statements, plus the `p = 2` and finite-real non-endpoint `sInf` and
conditional source-`min` statements, deriving the required one-sided inverse
from `AA⁺A=A` and the printed rank hypothesis rather than assuming it
separately.  The remaining source gap is the actual Moore-Penrose construction
and proof of the first Penrose equation and needed projection-symmetry
witnesses from the book's rank hypotheses:

- `ch7RectColumnLpNormOfReal`
- `ch7RectColumnLpNormOfReal_nonneg`
- `ch7RectColumnLpNormOfReal_pos_of_rect_left_inverse`
- `ch7RectMatMulVecLinearMap`
- `ch7_exists_rect_left_inverse_of_linear_left_inverse`
- `ch7_exists_rect_right_inverse_of_linear_right_inverse`
- `ch7_exists_rect_left_inverse_of_rectMatMulVec_injective`
- `ch7_exists_rect_right_inverse_of_rectMatMulVec_surjective`
- `ch7_rectMatMulVec_injective_of_matrix_rank_eq_width`
- `ch7_rectMatMulVec_surjective_of_matrix_rank_eq_height`
- `theorem7_5_rect_left_inverse_of_penrose1_rectMatMulVec_injective`
- `theorem7_5_rect_right_inverse_of_penrose1_rectMatMulVec_surjective`
- `theorem7_5_rect_left_inverse_of_penrose1_matrix_rank_eq_width`
- `theorem7_5_rect_right_inverse_of_penrose1_matrix_rank_eq_height`
- `theorem7_5_p1_column_equilibration_isLeast_right_scalings_of_penrose1_matrix_rank_eq_width`
- `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings_of_penrose1_matrix_rank_eq_width`
- `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_penrose1_matrix_rank_eq_width`
- `theorem7_5_lp_column_equilibration_le_card_rpow_sInf_right_scalings_of_penrose1_matrix_rank_eq_width`
- `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings_of_penrose1_matrix_rank_eq_width`
- `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings_of_penrose1_matrix_rank_eq_height`
- `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings_of_penrose1_matrix_rank_eq_height`
- `theorem7_5_p2_row_equilibration_le_sqrt_card_sInf_left_scalings_of_penrose1_matrix_rank_eq_height`
- `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_penrose1_matrix_rank_eq_height`
- `theorem7_5_pinf_row_equilibration_isLeast_left_scalings_of_penrose1_matrix_rank_eq_height`
- `theorem7_5_rect_left_inverse_symmetric_penrose_equations`
- `theorem7_5_rect_right_inverse_symmetric_penrose_equations`
- `theorem7_5_rect_penrose_injective_symmetric_range_penrose_equations`
- `theorem7_5_rect_penrose_surjective_symmetric_domain_penrose_equations`
- `theorem7_5_rect_penrose_matrix_rank_eq_width_symmetric_range_penrose_equations`
- `theorem7_5_rect_penrose_matrix_rank_eq_height_symmetric_domain_penrose_equations`
- `rectMatMul_id_left`
- `rectMatMul_id_right`
- `rectMatMul_assoc`
- `rectMatMul_rangeProjection_idempotent_of_left_inverse`
- `rectMatMul_domainProjection_idempotent_of_right_inverse`
- `rectOpNorm2Le_rangeProjection_of_symmetric_left_inverse`
- `rectOpNorm2Le_domainProjection_of_symmetric_right_inverse`
- `finiteMatVec_projection_residual_eq_zero_of_idempotent`
- `finiteVecInnerProduct_projection_residual_range_eq_zero`
- `finiteVecNorm2Sq_add_of_inner_eq_zero`
- `finiteVecNorm2Sq_projection_residual_le_residual_to_range_of_symmetric_idempotent`
- `finiteVecNorm2_projection_residual_le_residual_to_range_of_symmetric_idempotent`
- `rectMatMulVec_idMatrix`
- `rectMatMulVec_rangeProjection_apply_range_of_left_inverse`
- `rectMatMulVec_domainProjection_apply_range_of_right_inverse`
- `rectMatMulVec_rangeProjection_residual_orthogonal_range_of_symmetric_left_inverse`
- `rectMatMulVec_domainProjection_residual_orthogonal_range_of_symmetric_right_inverse`
- `rectMatMulVec_rangeProjection_residual_normSq_le_range_residual_of_symmetric_left_inverse`
- `rectMatMulVec_domainProjection_residual_normSq_le_range_residual_of_symmetric_right_inverse`
- `rectMatMulVec_rangeProjection_residual_norm_le_range_residual_of_symmetric_left_inverse`
- `rectMatMulVec_domainProjection_residual_norm_le_range_residual_of_symmetric_right_inverse`
- `theorem7_5_rect_left_inverse_range_projection_idempotent`
- `theorem7_5_rect_right_inverse_domain_projection_idempotent`
- `theorem7_5_rect_left_inverse_symmetric_range_projection_op2Le_one`
- `theorem7_5_rect_right_inverse_symmetric_domain_projection_op2Le_one`
- `theorem7_5_rect_left_inverse_range_projection_fixes_range`
- `theorem7_5_rect_right_inverse_domain_projection_fixes_range`
- `theorem7_5_rect_left_inverse_symmetric_range_projection_residual_orthogonal_range`
- `theorem7_5_rect_right_inverse_symmetric_domain_projection_residual_orthogonal_range`
- `theorem7_5_rect_left_inverse_symmetric_range_projection_residual_normSq_le_range_residual`
- `theorem7_5_rect_right_inverse_symmetric_domain_projection_residual_normSq_le_range_residual`
- `theorem7_5_rect_left_inverse_symmetric_range_projection_residual_norm_le_range_residual`
- `theorem7_5_rect_right_inverse_symmetric_domain_projection_residual_norm_le_range_residual`
- `theorem7_5_rect_left_inverse_symmetric_range_projection_residual_normSq_isLeast`
- `theorem7_5_rect_right_inverse_symmetric_domain_projection_residual_normSq_isLeast`
- `theorem7_5_rect_left_inverse_symmetric_range_projection_residual_norm_isLeast`
- `theorem7_5_rect_right_inverse_symmetric_domain_projection_residual_norm_isLeast`
- `theorem7_5_rect_penrose_injective_symmetric_range_projection_op2Le_one`
- `theorem7_5_rect_penrose_surjective_symmetric_domain_projection_op2Le_one`
- `theorem7_5_rect_penrose_injective_symmetric_range_projection_residual_orthogonal_range`
- `theorem7_5_rect_penrose_surjective_symmetric_domain_projection_residual_orthogonal_range`
- `theorem7_5_rect_penrose_injective_symmetric_range_projection_residual_normSq_isLeast`
- `theorem7_5_rect_penrose_surjective_symmetric_domain_projection_residual_normSq_isLeast`
- `theorem7_5_rect_penrose_injective_symmetric_range_projection_residual_norm_isLeast`
- `theorem7_5_rect_penrose_surjective_symmetric_domain_projection_residual_norm_isLeast`
- `theorem7_5_rect_penrose_matrix_rank_eq_width_symmetric_range_projection_residual_normSq_isLeast`
- `theorem7_5_rect_penrose_matrix_rank_eq_height_symmetric_domain_projection_residual_normSq_isLeast`
- `eq_7_20_column_lpNorm_le_matrixLpNormOfReal`
- `ch7_complexVecLpNorm_realRect_matVec_le_sum_column_lpNorm`
- `eq_7_20_matrixLpNormOfReal_le_card_rpow_mul_column_bound`
- `ch7ColumnEquilibratingScaleLpOfReal`
- `ch7RectColumnLpNormOfReal_rightScale`
- `ch7RectColumnLpNormOfReal_rightScale_equilibrating`
- `eq_7_21_matrixLpNormOfReal_column_equilibrated`
- `ch7RectColumnNorm2`
- `ch7RectColumnNorm2_pos_of_rect_left_inverse`
- `ch7RectRightScale`
- `ch7ColumnEquilibratingScale2`
- `eq_7_20_column_norm_le_of_rectOpNorm2Le`
- `ch7RectColumnNorm2_le_frobNormRect`
- `ch7_frobNormRect_le_sqrt_card_mul_column_bound`
- `eq_7_20_rectOpNorm2Le_of_column_bound`
- `eq_7_21_rectOpNorm2Le_column_equilibrated`
- `ch7RectColumnNorm1`
- `ch7RectColumnNorm1_pos_of_rect_left_inverse`
- `ch7RectLeftScale`
- `ch7ColumnEquilibratingScale1`
- `eq_7_21_oneNormRect_column_equilibrated`
- `ch7OneNormRightScaledCond`
- `ch7OneNormRightScaledCondSet`
- `eq_7_22_oneNormRect_inverseSide_bound`
- `theorem7_5_p1_column_equilibration_le_right_scaling`
- `theorem7_5_p1_column_equilibration_sInf_eq_right_scalings`
- `theorem7_5_p1_column_equilibration_isLeast_right_scalings`
- `theorem7_5_p1_column_equilibration_isLeast_right_scalings_of_rect_left_inverse`
- `theorem7_5_p1_column_equilibration_exists_left_inverse_of_rectMatMulVec_injective`
- `theorem7_5_p1_column_equilibration_exists_left_inverse_of_matrix_rank_eq_width`
- `ch7_vecNorm2_mul_le_of_abs_le`
- `ch7RectLeftScale_rectOpNorm2Le_of_abs_le`
- `ch7Op2RightScaledCond`
- `ch7Op2RightScaledCondSet`
- `ch7Op2RightScaledCondSet_nonempty`
- `ch7Op2RightScaledCondSet_bddBelow`
- `eq_7_22_op2_inverseSide_bound`
- `theorem7_5_p2_column_equilibration_le_sqrt_card_right_scaling`
- `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings`
- `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings_of_rect_left_inverse`
- `theorem7_5_p2_column_equilibration_exists_left_inverse_of_rectMatMulVec_injective`
- `theorem7_5_p2_column_equilibration_exists_left_inverse_of_matrix_rank_eq_width`
- `complexMatrixLpNormOfReal_mul_le`
- `ch7_complexMatrixLpNormOfReal_nonneg`
- `ch7_complexVecLpNormOfReal_diagScale_le_of_norm_le`
- `eq_7_22_matrixLpNormOfReal_inverseSide_bound`
- `ch7LpRightScaledCondOfReal`
- `ch7LpRightScaledCondSetOfReal`
- `ch7LpRightScaledCondOfReal_nonneg`
- `ch7LpRightScaledCondOfReal_mem_set`
- `ch7LpRightScaledCondSetOfReal_nonempty`
- `ch7LpRightScaledCondSetOfReal_bddBelow`
- `ch7LpRightScaledCondSetOfReal_sInf_nonneg`
- `theorem7_5_lp_column_equilibration_le_card_rpow_right_scaling`
- `theorem7_5_lp_column_equilibration_le_card_rpow_sInf_right_scalings`
- `theorem7_5_lp_column_equilibration_le_card_rpow_sInf_right_scalings_of_rect_left_inverse`
- `theorem7_5_lp_column_equilibration_exists_left_inverse_of_rectMatMulVec_injective`
- `theorem7_5_lp_column_equilibration_exists_left_inverse_of_matrix_rank_eq_width`
- `ch7RectRowDualLpNormOfReal`
- `ch7RectRowDualLpNormOfReal_nonneg`
- `ch7RectRowDualLpNormOfReal_pos_of_rect_right_inverse`
- `ch7RowDualEquilibratingScaleLpOfReal`
- `ch7RectRowDualLpNormOfReal_leftScale`
- `ch7RectRowDualLpNormOfReal_leftScale_equilibrating`
- `eq_7_19_matrixLpNormOfReal_dual_row_equilibrated`
- `eq_7_19_matrixLpNormOfReal_dual_row_inverseSide_bound`
- `ch7LpLeftScaledCondOfReal`
- `ch7LpLeftScaledCondSetOfReal`
- `ch7LpLeftScaledCondOfReal_nonneg`
- `ch7LpLeftScaledCondOfReal_mem_set`
- `ch7LpLeftScaledCondSetOfReal_nonempty`
- `ch7LpLeftScaledCondSetOfReal_bddBelow`
- `ch7LpLeftScaledCondSetOfReal_sInf_nonneg`
- `theorem7_5_lp_dual_row_equilibration_le_card_rpow_left_scaling`
- `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings`
- `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings_of_rect_right_inverse`
- `theorem7_5_lp_dual_row_equilibration_exists_right_inverse_of_rectMatMulVec_surjective`
- `theorem7_5_lp_dual_row_equilibration_exists_right_inverse_of_matrix_rank_eq_height`
- `ch7RectRowNorm2`
- `ch7RectRowNorm2_pos_of_rect_right_inverse`
- `theorem7_5_p2_row_equilibration_le_sqrt_card_sInf_left_scalings_of_rect_right_inverse`
- `theorem7_5_p2_row_equilibration_exists_right_inverse_of_rectMatMulVec_surjective`
- `theorem7_5_p2_row_equilibration_exists_right_inverse_of_matrix_rank_eq_height`
- `ch7RectRowNorm1`
- `ch7RectRowNorm1_pos_of_rect_right_inverse`
- `ch7RowEquilibratingScale1Rect`
- `eq_7_19_infNormRect_row_equilibrated`
- `ch7InfNormLeftScaledCond`
- `ch7InfNormLeftScaledCondSet`
- `eq_7_19_infNormRect_inverseSide_bound`
- `theorem7_5_pinf_row_equilibration_le_left_scaling`
- `theorem7_5_pinf_row_equilibration_sInf_eq_left_scalings`
- `theorem7_5_pinf_row_equilibration_isLeast_left_scalings`
- `theorem7_5_pinf_row_equilibration_isLeast_left_scalings_of_rect_right_inverse`
- `theorem7_5_pinf_row_equilibration_exists_right_inverse_of_rectMatMulVec_surjective`
- `theorem7_5_pinf_row_equilibration_exists_right_inverse_of_matrix_rank_eq_height`
- `ch7SymmetricDiagEquilibratingScale2`
- `ch7SymmetricDiagEquilibratingInvScale2`
- `corollary7_6_cholesky_diag_eq_column_norm_sq`
- `corollary7_6_cholesky_diag_invScale_eq_column_norm`
- `corollary7_6_cholesky_diag_scale_eq_column_equilibrating`
- `corollary7_6_cholesky_column_norm_pos`
- `corollary7_6_cholesky_factor_column_equilibrated`
- `corollary7_6_cholesky_factor_op2Le_sqrt_card`
- `corollary7_6_cholesky_factor_column_scaling_le_sqrt_card_sInf_right_scalings`
- `ch7SymmetricOp2ScaledCond`
- `ch7SymmetricOp2ScaledCondSet`
- `ch7SymmetricOp2ScaledCond_mem_set`
- `ch7SymmetricOp2ScaledCondSet_nonempty`
- `ch7SymmetricOp2ScaledCond_nonneg`
- `ch7SymmetricOp2ScaledCondSet_bddBelow`
- `ch7CholeskyInverseGram`
- `corollary7_6_cholesky_scaled_gram_eq`
- `corollary7_6_cholesky_scaled_inverse_gram_eq`
- `corollary7_6_cholesky_scaled_cond_eq_factor_cond_sq`
- `corollary7_6_cholesky_scaled_cond_le_card_sInf_right_scalings_sq`
- `corollary7_6_cholesky_right_sInf_sq_le_symmetric_sInf`
- `corollary7_6_cholesky_scaled_cond_le_card_sInf_symmetric_scalings`
- `corollary7_6_cholesky_inverse_gram_isInverse`
- `corollary7_6_cholesky_scaled_inverse_gram_isInverse`

The current Stewart-Sun Frobenius scaling pass closes Theorem 7.7 in the
nonsingular real finite-dimensional form.  It defines the source column and
inverse-row Euclidean norm product, proves the Cauchy lower bound for every
inverse diagonal right-scaling pair, proves the canonical
`sqrt(||b_j||_2 / ||a_j||_2)` scaling attains the lower bound, and derives the
needed positive norm side conditions from `A_inv * A = I` rather than assuming
them as theorem-equivalent hypotheses:

- `ch7ColumnNorm2`
- `ch7InverseRowNorm2`
- `ch7StewartSunFrobeniusValue`
- `ch7FrobeniusRightScaledCond`
- `ch7StewartSunScale`
- `ch7StewartSunInvScale`
- `theorem7_7_frobenius_right_scaling_lower_bound`
- `theorem7_7_stewart_sun_frobenius_scaling`
- `theorem7_7_stewart_sun_frobenius_scaling_of_left_inverse`

The current Bauer scaling pass closes the algebraic core of Problem 7.10(a)
under the explicit positive Perron-vector certificate used in Higham's hint and
closes the Problem 7.10(b) absolute-value instantiation `B = |A|`,
`C = |A⁻¹|` under the same certificate.  It proves that every positive
two-sided diagonal scaling has infinity-norm product at least the certified
eigenvalue `ρ`, that the canonical scaling `D₁ = diag(x)⁻¹`,
`D₂ = diag(Cx)` attains `ρ`, and that the actual scaled `κ∞` product agrees
with the repository `kappaInf` value for the two-sided scaled matrix when the
inverse-scaled partner is supplied from a genuine inverse certificate, then
with the Problem 7.10(a) product after taking componentwise absolute values.
The latest Bauer adapter pass also proves the positive-entry side condition
needed to connect Problem 7.10(b) to the irreducibility hypotheses in Theorem
7.8/Problem 7.10(d): strictly positive matrices are primitive, hence
irreducible in Mathlib's matrix-connectivity API, and positive Bauer factors
have positive products.  The current continuation also closes the one-norm
transpose branch of Problem 7.10(e) under the corresponding explicit positive
Perron-vector certificate for `BᵀCᵀ`, including the `B = |A|`,
`C = |A⁻¹|` scaled-`κ₁` absolute-value instantiation.  The latest
continuations close the algebraic `CB(Cx)` Perron-vector transfer, the
irreducible-matrix theorem that a nonzero nonnegative eigenvector with a
positive eigenvalue is strictly positive, the resulting Problem 7.10(d)
`Cx > 0` transfer under irreducible `CB`, proves the strict-eigenvalue side
condition from a positive `BC` entry, and now strengthens that side condition to
the source-shaped irreducible-`BC` hypothesis, including the direct
`B = |A|`, `C = |A⁻¹|` specialization.  It also closes the 2-norm interpolation ingredient
in Problem 7.10(e), and the order-theoretic
`sInf` upper-bound packaging for any supplied positive reciprocal scaling with
both `κ₁` and `κ∞` products bounded by `ρ`.  The latest continuation also
defines the positive reciprocal scaling value sets for the infinity-norm Bauer
product, the scaled `κ∞` product, and the scaled `κ₁` transpose product, and
proves exact `sInf = ρ` equalities for Problem 7.10(a), Problem 7.10(b), and
the one-norm branch of Problem 7.10(e) under the same explicit positive
Perron-vector certificates.  This continuation upgrades those certificate-level
`sInf = ρ` statements to genuine `IsLeast` value-set theorems for the
Problem 7.10(a) infinity-product, Problem 7.10(b) scaled-`κ∞` product, and
Problem 7.10(e) one-norm scaled-`κ₁` product, including positive-entry and
irreducible-product/nonzero-nonnegative variants.  The current continuation
upgrades the one-norm branch of Problem 7.10(e) to source-shaped irreducible
transpose products and a supplied nonzero nonnegative transpose-side
eigenvector, deriving `y > 0` and `|A⁻¹|ᵀy > 0` locally rather than assuming
them.  The latest pass removes the
remaining transpose-product side-condition mismatch for the one-norm branch:
irreducibility of the source products `BC` and `CB` is transported through
`(BC)ᵀ = CᵀBᵀ`, so the Problem 7.10(e) one-norm scaled-`κ₁` wrappers now use
the same original-product irreducibility hypotheses printed in Theorem 7.8 /
Problem 7.10(d).  This is genuine proof work, but it does not assert
Perron-Frobenius existence of the required nonzero nonnegative eigenvector from
irreducibility or prove that the compatible common one-/infinity-norm scaling
exists for `ρ = ρ(|A||A⁻¹|)`.  The spectral-dominance continuations prove the
finite complex-eigenvalue-radius half under a supplied positive Perron-vector
certificate: `ρ` is a complexified eigenvalue, and every complex eigenvalue
certificate has modulus at most `ρ`; they extend that local radius result to
every positive reciprocal two-sided scaling of the Bauer product, export the
Chapter 7 carrier to the generic Split 1 maximum-modulus interface, identify it
with the Mathlib `spectrum (Matrix.toLin' ...)` modulus set, and reuse the
integrated Split 1 norm-existence theorem to obtain consistent norm values at
most `ρ + δ`.  The latest spectral-radius bridge also identifies the same
certificate with Mathlib's Banach-algebra `spectralRadius` as
`spectralRadius ℂ (Matrix.toLin' ...) = ENNReal.ofReal ρ`.  The current
nonzero-nonnegative spectral-radius continuation derives those product,
absolute-product, scaled-product, and one-norm transpose-product
`spectralRadius` wrappers from source-shaped irreducibility plus a supplied
nonzero nonnegative eigenpair, so strict positivity is no longer a separate
assumption in those theorem surfaces.  The remaining spectral work is
Perron-Frobenius eigenpair existence from irreducibility and the
compatible common-scaling theorem for the full Bauer op-2 row:

- `ch7TwoSidedScale`
- `ch7TwoSidedScaledInfCond`
- `ch7TwoSidedScaledInfCondSet`
- `ch7TwoSidedScaledInfCond_mem_set`
- `ch7TwoSidedScaledInfCondSet_nonempty`
- `ch7TwoSidedScaledInfCondSet_bddBelow`
- `ch7_infNorm_ge_of_nonneg_right_eigenvector`
- `ch7IsComplexEigenvalueRadius`
- `ch7ComplexEigenvalueModulusSet`
- `complexMatrixEigenvalueModulusSet_eq_toLin_spectrum_modulusSet`
- `ch7_complexEigenvalueModulusSet_eq_complexMatrixEigenvalueModulusSet`
- `ch7_complexEigenvalueModulusSet_eq_toLin_spectrum_modulusSet`
- `ch7_isMaxComplexMatrixEigenvalueModulus_of_isComplexEigenvalueRadius`
- `ch7_toLin_spectrum_modulusSet_isGreatest_of_isComplexEigenvalueRadius`
- `ch7_toLin_spectrum_modulusSet_sSup_eq_of_isComplexEigenvalueRadius`
- `ch7_exists_mixedSubordinateMatrixNormValue_le_of_isComplexEigenvalueRadius`
- `ch7_complex_eigenvalue_norm_le_of_positive_real_eigenvector`
- `ch7_real_positive_eigenvector_complexified`
- `ch7_isComplexEigenvalueRadius_of_positive_real_eigenvector`
- `problem7_10a_product_isComplexEigenvalueRadius_of_positive_eigenvector`
- `problem7_10a_product_isMaxComplexMatrixEigenvalueModulus_of_positive_eigenvector`
- `problem7_10a_product_exists_mixedSubordinateMatrixNormValue_le_perron_add_delta`
- `problem7_10a_product_toLin_spectrum_modulusSet_sSup_eq_of_positive_eigenvector`
- `problem7_10b_abs_product_isComplexEigenvalueRadius_of_positive_eigenvector`
- `problem7_10b_abs_product_isMaxComplexMatrixEigenvalueModulus_of_positive_eigenvector`
- `problem7_10b_abs_product_exists_mixedSubordinateMatrixNormValue_le_perron_add_delta`
- `problem7_10b_abs_product_toLin_spectrum_modulusSet_sSup_eq_of_positive_eigenvector`
- `problem7_10a_scaled_product_isComplexEigenvalueRadius_of_positive_eigenvector`
- `problem7_10a_scaled_product_isMaxComplexMatrixEigenvalueModulus_of_positive_eigenvector`
- `problem7_10a_scaled_product_exists_mixedSubordinateMatrixNormValue_le_perron_add_delta`
- `problem7_10a_scaled_product_toLin_spectrum_modulusSet_sSup_eq_of_positive_eigenvector`
- `problem7_10a_scaled_product_complexEigenvalueModulusSet_isGreatest_of_positive_eigenvector`
- `problem7_10a_scaled_product_complexEigenvalueModulusSet_sSup_eq_of_positive_eigenvector`
- `problem7_10a_scaled_infCond_ge_perron_of_positive_eigenvector`
- `ch7_bauer_Cx_eigenvector_CB`
- `ch7_matrix_mulVec_eq_matMulVec`
- `ch7_matrix_pow_mulVec_eigen`
- `ch7_perronScalar_pos_of_nonneg_irreducible_eigenvector`
- `ch7_nonneg_irreducible_right_eigenvector_pos`
- `problem7_10d_Cx_pos_of_irreducible_CB`
- `ch7_perronScalar_pos_of_nonneg_eigenvector_entry_pos`
- `problem7_10d_Cx_pos_of_irreducible_CB_of_positive_BC_entry`
- `problem7_10d_Cx_pos_of_irreducible_BC_CB`
- `ch7_matrix_isPrimitive_of_pos_entries`
- `ch7_matrix_isIrreducible_of_pos_entries`
- `ch7_matMul_pos_of_pos`
- `ch7_bauer_positive_products_irreducible`
- `problem7_10a_canonical_scaled_infCond_eq_perron_of_positive_eigenvector`
- `problem7_10a_positive_entries_canonical_scaled_infCond_eq_perron`
- `problem7_10a_scaledInfCondSet_sInf_eq_perron_of_positive_eigenvector`
- `problem7_10a_positive_entries_scaledInfCondSet_sInf_eq_perron`
- `ch7TwoSidedScale_absMatrix_eq`
- `ch7_infNorm_twoSidedScale_absMatrix_eq`
- `ch7TwoSidedScaledInfKappa`
- `ch7TwoSidedScaledInfKappaSet`
- `ch7TwoSidedScaledInfKappa_mem_set`
- `ch7TwoSidedScaledInfKappaSet_nonempty`
- `ch7TwoSidedScaledInfKappaSet_bddBelow`
- `ch7TwoSidedScale_isLeftInverse`
- `ch7TwoSidedScale_isRightInverse`
- `ch7TwoSidedScale_isInverse`
- `ch7TwoSidedScaledInfKappa_eq_kappaInf_of_inverse`
- `ch7TwoSidedScaledInfKappa_eq_abs_scaledInfCond`
- `problem7_10b_scaled_infKappa_ge_perron_of_abs_inverse_positive_eigenvector`
- `problem7_10b_canonical_scaled_infKappa_eq_perron_of_abs_inverse_positive_eigenvector`
- `problem7_10d_abs_inverse_Cx_pos_of_irreducible_products`
- `problem7_10b_irreducible_products_canonical_scaled_infKappa_eq_perron`
- `problem7_10b_positive_abs_entries_canonical_scaled_infKappa_eq_perron`
- `problem7_10b_scaledInfKappaSet_sInf_eq_perron_of_abs_inverse_positive_eigenvector`
- `problem7_10b_irreducible_products_scaledInfKappaSet_sInf_eq_perron`
- `problem7_10b_positive_abs_entries_scaledInfKappaSet_sInf_eq_perron`
- `problem7_10b_positive_abs_entries_products_irreducible`
- `ch7TwoSidedScaledOneCond`
- `ch7TwoSidedScaledOneCond_eq_transpose_infCond`
- `problem7_10e_scaled_oneCond_ge_perron_of_transpose_positive_eigenvector`
- `problem7_10e_canonical_scaled_oneCond_eq_perron_of_transpose_positive_eigenvector`
- `problem7_10e_positive_entries_canonical_scaled_oneCond_eq_perron_of_transpose`
- `ch7TwoSidedScaledOneKappa`
- `ch7TwoSidedScaledOneKappaSet`
- `ch7TwoSidedScaledOneKappa_mem_set`
- `ch7TwoSidedScaledOneKappaSet_nonempty`
- `ch7TwoSidedScaledOneKappaSet_bddBelow`
- `ch7TwoSidedScaledOneKappa_eq_abs_scaledOneCond`
- `problem7_10e_scaled_oneKappa_ge_perron_of_abs_inverse_transpose_positive_eigenvector`
- `problem7_10e_canonical_scaled_oneKappa_eq_perron_of_abs_inverse_transpose_positive_eigenvector`
- `problem7_10e_positive_abs_entries_canonical_scaled_oneKappa_eq_perron_of_transpose`
- `problem7_10e_scaledOneKappaSet_sInf_eq_perron_of_abs_inverse_transpose_positive_eigenvector`
- `problem7_10e_positive_abs_entries_scaledOneKappaSet_sInf_eq_perron_of_transpose`
- `problem7_10e_irreducible_transpose_products_canonical_scaled_oneCond_eq_perron_of_nonzero_nonneg_eigenvector`
- `problem7_10e_irreducible_transpose_products_canonical_scaled_oneKappa_eq_perron_of_nonzero_nonneg_eigenvector`
- `problem7_10e_irreducible_transpose_products_scaledOneKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector`
- `ch7_matrix_of_matTranspose`
- `ch7_irreducible_matTranspose`
- `ch7_irreducible_transpose_product_of_irreducible_product`
- `problem7_10e_irreducible_products_canonical_scaled_oneCond_eq_perron_of_nonzero_nonneg_eigenvector`
- `problem7_10e_irreducible_products_canonical_scaled_oneKappa_eq_perron_of_nonzero_nonneg_eigenvector`
- `problem7_10e_irreducible_products_scaledOneKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector`
- `ch7_complexMatrixOneNorm_realRectToCMatrix_le_oneNorm`
- `ch7_complexMatrixInfNorm_realRectToCMatrix_le_infNorm`
- `problem7_10e_complexMatrixOp2_realRectToCMatrix_le_sqrt_one_mul_inf`
- `ch7TwoSidedScaledOp2Kappa`
- `problem7_10e_scaled_op2Kappa_le_sqrt_oneKappa_mul_infKappa`
- `problem7_10e_scaled_op2Kappa_le_of_one_inf_bounds`
- `ch7TwoSidedScaledOp2Kappa_mem_set`
- `ch7TwoSidedScaledOp2KappaSet_bddBelow`
- `ch7TwoSidedScaledOp2KappaSet_sInf_nonneg`
- `problem7_10e_twoSidedScaledOp2Kappa_sInf_le_of_one_inf_bounds`

The current Problem 7.15 pass closes the reciprocal two-sided diagonal-scaling
algebra for the Hadamard matrix `A ∘ A^{-T}`.  If
`D₁AD₂` is paired with the compatible inverse partner
`D₂⁻¹A_invD₁⁻¹`, then the source matrix
`(D₁AD₂) ∘ (D₂⁻¹A_invD₁⁻¹)^T` is definitionally equal, after proved
entrywise algebra, to `A ∘ A_inv^T`.  The continuation also closes the
transpose/operator-2 certificate side condition for the inverse-scaled partner
and proves the Horn-Johnson operator-2 Hadamard inequality in certificate form,
by identifying `(A ∘ B)x` with the diagonal of `A * diag(x) * B^T` and bounding
that diagonal through the Frobenius triple-product inequality.  The final
Problem 7.15 continuation defines the exact positive two-sided scaling value
set using `complexMatrixOp2` of real-to-complex matrix embeddings and proves
`||A ∘ A_inv^T||₂ <= sInf {κ₂(D₁ A D₂)}` for reciprocal positive diagonal
scalings.  It also records the source attainability discussion as a conditional
certificate: if one positive reciprocal scaling realizes the Hadamard
lower-bound value, then the `sInf` is equal to that value.  The diagonal
attainability continuation closes Appendix A.7.15's diagonal case for every
nonsingular diagonal matrix: with `A = diag(a)` and all `a_i != 0`, the
positive scaling `D₁ = diag(|a_i|^{-1})`, `D₂ = I` makes both scaled factors
real orthogonal sign-diagonal matrices, proves `||A ∘ A^{-T}||₂ = 1`, and
proves both `sInf = 1` and `IsLeast 1` for the exact positive two-sided
operator-2 condition-product value set.

- `ch7HadamardProduct`
- `ch7_matTranspose_twoSidedScale`
- `ch7HadamardProduct_twoSidedScale_transpose_inverse_eq`
- `problem7_15_twoSidedScale_hadamard_transpose_inverse_invariant`
- `opNorm2Le_transpose`
- `problem7_15_transpose_inverse_partner_opNorm2Le`
- `frobNormRect_diagMatrix`
- `vecNorm2_diagonal_le_frobNormRect`
- `matMulVec_hadamard_eq_diag_rectMatMul_diag_transpose`
- `opNorm2Le_hadamard`
- `complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le`
- `opNorm2Le_complexMatrixOp2_realRectToCMatrix`
- `problem7_15_hornJohnson_hadamard_opNorm2Le`
- `problem7_15_scaled_inverse_hadamard_opNorm2Le`
- `ch7TwoSidedScaledOp2KappaSet`
- `ch7TwoSidedScaledOp2KappaSet_nonempty`
- `problem7_15_hadamard_op2_le_twoSidedScaledOp2Kappa_mem`
- `problem7_15_twoSidedScaledOp2Kappa_sInf_ge_hadamard_op2`
- `problem7_15_twoSidedScaledOp2Kappa_sInf_ge_hadamard_op2_of_inverse`
- `problem7_15_twoSidedScaledOp2Kappa_sInf_eq_hadamard_op2_of_mem`
- `problem7_15_twoSidedScaledOp2Kappa_isLeast_hadamard_op2_of_mem`
- `problem7_15_twoSidedScaledOp2Kappa_sInf_eq_hadamard_op2_of_attaining_scaling`
- `problem7_15_twoSidedScaledOp2Kappa_isLeast_hadamard_op2_of_attaining_scaling`
- `problem7_15_complexMatrixOp2_realRectToCMatrix_orthogonal_eq_one`
- `problem7_15_ch7TwoSidedScale_diagMatrix_eq`
- `problem7_15_hadamard_diag_inverse_transpose_eq_idMatrix`
- `problem7_15_diagonal_hadamard_op2_eq_one`
- `problem7_15_diagonal_attaining_scaling_eq_hadamard_op2`
- `problem7_15_diagonal_twoSidedScaledOp2Kappa_sInf_eq_one`
- `problem7_15_diagonal_twoSidedScaledOp2Kappa_isLeast_one`

The current row-wise data-condition pass closes Problem 7.6(a), the row-wise
relative perturbation model `E = |A| e e^T`, `f = |b| = |Ax|`, in the
infinity-norm source specialization:

- `ch7_abs_le_oneNormVec`
- `ch7RowwiseRelativeToleranceMatrix`
- `ch7RowwiseDataCondAtSolutionInf`
- `ch7_rowwiseDataForwardBound_lower`
- `ch7_rowwiseDataForwardBound_upper`
- `problem7_6a_rowwise_data_condition_bounds`

The current columnwise data-condition pass closes Problem 7.6(b), the source
model `E = e e^T |A|`, `f = ‖b‖₁ e = ‖Ax‖₁ e`, in the infinity-norm
specialization:

- `ch7ColumnwiseRelativeToleranceMatrix`
- `ch7AbsMatrixAbsVecOneNorm`
- `ch7ColumnwiseDataCondAtSolutionInf`
- `ch7_columnwiseDataForwardBound_lower`
- `ch7_columnwiseDataForwardBound_upper`
- `problem7_6b_columnwise_data_condition_bounds`

The current scalar-output pass closes the finite first-order componentwise
formula from Problem 7.9.  For nonnegative tolerances `E,f` and nonzero
`c^T x`, every admissible first-order perturbation satisfies the source
upper bound
`|c^T A⁻¹(Δb - ΔA x)| / |c^T x| ≤ ε |c^T A⁻¹|(E|x|+f)/|c^T x|`, and an
explicit sign perturbation attains the linearized numerator.  A follow-up
proof closes the source lower-bound specialization
`χ_{E,f}(A,x) ≥ 1` for the finite linearized condition when either `E = |A|`
or `f = |b|`.  A further finite normwise pass proves the first-order
operator-2 certificate formula
`‖c^T A⁻¹‖₂(‖E‖₂‖x‖₂+‖f‖₂)/|c^T x|` and constructs an attaining rank-one
matrix perturbation plus aligned right-hand-side perturbation.  This pass also
packages both finite first-order formulas as positive-radius suprema and closes
the nonlinear componentwise source-radius wrapper for `χ`: the exact perturbed
solution `x̂ = (A + ΔA)⁻¹(Ax + Δb)` is represented by the constructed local
inverse candidate, its scalar output is squeezed by the linearized formula plus
an explicit `O(ε²)` remainder, and the shrinking-radius `sSup` converges to
`|c^T A⁻¹|(E|x|+f)/|c^T x|`.  The latest normwise nonlinear pass closes the
matching exact source-radius wrapper for `ψ`: basis-vector testing turns
`opNorm2Le ΔA (ε‖E‖₂)` into a conservative constant componentwise envelope for
the local inverse candidate, coordinate bounds turn `‖Δb‖₂ ≤ ε‖f‖₂` into the
right-hand-side envelope, the exact scalar change is squeezed by the normwise
linearized formula plus a proved quadratic remainder, and the shrinking-radius
`sSup` converges to
`‖c^T A⁻¹‖₂(‖f‖₂+‖E‖₂‖x‖₂)/|c^T x|`:

- `ch7LinearFunctional`
- `ch7Problem79AdjointWeight`
- `ch7Problem79FirstOrderChange`
- `ch7Problem79ComponentwiseSensitivity`
- `ch7Problem79LinearizedCond`
- `ch7Problem79LinearizedRelativeChange`
- `ch7Problem79AttainingDeltaA`
- `ch7Problem79AttainingDeltaB`
- `problem7_9_linearized_componentwise_functional_formula`
- `ch7Problem79_adjointWeight_mul_vec_eq_linearFunctional_matMulVec`
- `ch7Problem79_linearFunctional_eq_adjointWeight_mul_Ax`
- `ch7Problem79ComponentwiseSensitivity_ge_abs_functional_of_abs_matrix`
- `ch7Problem79ComponentwiseSensitivity_ge_abs_functional_of_abs_rhs`
- `problem7_9_linearized_componentwise_functional_ge_one_of_abs_matrix`
- `problem7_9_linearized_componentwise_functional_ge_one_of_abs_rhs`
- `ch7Problem79NormwiseSensitivity`
- `ch7Problem79NormwiseLinearizedCond`
- `ch7Problem79NormwiseSensitivity_nonneg`
- `ch7Problem79_normwise_firstOrder_abs_le`
- `ch7Problem79_normwiseLinearizedRelativeChange_le`
- `ch7Problem79NormwiseAttainingDeltaB`
- `ch7Problem79NormwiseAttainingDeltaA`
- `ch7Problem79_normwiseAttainingDeltaA_bound`
- `ch7Problem79_normwiseAttainingDeltaB_bound`
- `ch7Problem79_normwise_attaining_firstOrder_eq`
- `problem7_9_linearized_normwise_functional_formula`
- `problem7_9_componentwise_linearized_radiusSup_tendsto_formula`
- `problem7_9_normwise_linearized_radiusSup_tendsto_formula`
- `ch7Problem79PerturbedSolutionWithInverse`
- `ch7Problem79ExactScalarRelativeChange`
- `problem7_9_exact_componentwise_relative_change_le_linearized_plus_quadratic`
- `problem7_9_exact_componentwise_relative_change_ge_linearized_minus_quadratic`
- `Ch7Problem79ComponentwiseExactRadiusSet`
- `ch7Problem79ComponentwiseExactRadiusSup`
- `ch7Problem79ComponentwiseExactRadiusSet_value_le`
- `exists_ch7Problem79ComponentwiseExactRadiusSet_lower_witness`
- `problem7_9_componentwise_exact_radiusSup_tendsto_linearized`
- `problem7_9_componentwise_exact_condition_of_positive_radii`
- `ch7Problem79NormwiseConstantEnvelopeMatrix`
- `ch7Problem79_normwise_deltaA_componentwise_bound`
- `ch7Problem79_normwise_deltaB_componentwise_bound`
- `ch7Problem79NormwiseExactRemainderBound`
- `problem7_9_exact_normwise_relative_change_le_linearized_plus_quadratic`
- `problem7_9_exact_normwise_relative_change_ge_linearized_minus_quadratic`
- `Ch7Problem79NormwiseExactRadiusSet`
- `ch7Problem79NormwiseExactRadiusSup`
- `ch7Problem79NormwiseExactRadiusSet_value_le`
- `exists_ch7Problem79NormwiseExactRadiusSet_lower_witness`
- `problem7_9_normwise_exact_radiusSup_tendsto_linearized`
- `problem7_9_normwise_exact_condition_of_positive_radii`

The current inverse-condition pass closes the Appendix A.11 first-order core of
Problem 7.11 in finite componentwise form: for nonnegative `E` and nonzero
entries of `A⁻¹`, the maximum relative linearized inverse change over
`|ΔA| ≤ εE` equals
`ε maxᵢⱼ (|A⁻¹|E|A⁻¹|)ᵢⱼ / |(A⁻¹)ᵢⱼ|`, and the source sign perturbation
`ΔA = εD₁ED₂` attains a maximizing entry.  The continuation pass also closes
the exact finite-dimensional algebraic identity
`(A + ΔA)⁻¹ - A⁻¹ = -A⁻¹ΔAA⁻¹ + A⁻¹ΔAA⁻¹ΔA(A + ΔA)⁻¹` under left/right
inverse certificates, the explicit componentwise quadratic-remainder bound,
and the finite exact maximum upper envelope
`max |(A + ΔA)⁻¹ - A⁻¹|/|A⁻¹| ≤ ε µ'_lin + ε² R`.  The latest pass also
closes the matching finite exact maximum upper/lower envelopes against the
actual linearized maximum and proves that the exact relative-change quotient
has the same filter limit as the linearized quotient when `ε > 0`, `ε → 0`,
the admissibility/right-inverse certificates hold eventually, and the
quadratic coefficient is eventually bounded.  The finite-radius dependency
also proves `R ≥ 0` and
`max |(A + ΔA)⁻¹ - A⁻¹|/|A⁻¹| ≤ ε(µ'_lin + δC)` whenever `ε ≤ δ` and
`R ≤ C`.  It also proves the filter-level asymptotic dependency
`εR → 0` whenever `ε → 0` and `R` is eventually bounded.  The latest
entry-bound continuation discharges the bounded quadratic-coefficient
hypothesis from an eventual entrywise bound on the exact perturbed inverses,
via a finite envelope
`ch7InverseQuadraticRemainderRelativeMaxEntryBound`.  The latest infinity-norm
continuation further proves that an eventual matrix `∞`-norm bound on the same
inverse family supplies the required entrywise bound.  The latest local inverse
continuation constructs the perturbed inverse family
`ch7Problem711PerturbedInverseCandidate`, proves it is a right inverse of
`A + ΔA` under the strict `‖ |A⁻¹ΔA| ‖∞ < 1` route, proves a concrete `∞`-norm
bound for it, derives the needed half-contraction eventually from
`|ΔA| ≤ εE` and `ε → 0`, and closes the exact-to-linearized bridge without
supplied right-inverse or boundedness hypotheses.  The latest source-radius
continuation defines the Problem 7.11 feasible exact inverse-change set over
all componentwise admissible perturbations, proves sharp upper/lower envelopes
`µ'_lin ± ρC` for its `sSup`, and proves that the shrinking-radius supremum
tends to the finite linearized value.  Thus the nonlinear Problem 7.11
source-radius `sSup`/`lim sup` wrapper is closed for the modeled componentwise
setting; the remaining source-level spectral comparison work belongs to other
open Chapter 7 rows rather than an unproved Problem 7.11 assumption:

- `ch7InverseLinearizedEntry`
- `ch7InverseCompSensitivityEntry`
- `ch7InverseCompSensitivityRatio`
- `ch7InverseComponentwiseLinearizedCond`
- `ch7InverseLinearizedRelativeChangeMax`
- `ch7Problem711AttainingDelta`
- `problem7_11_linearized_inverse_componentwise_upper_and_sign_attainment`
- `problem7_11_linearized_inverse_componentwise_formula`
- `ch7InverseQuadraticRemainderEntry`
- `ch7InverseFirstProductSensitivity`
- `ch7InverseQuadraticRemainderSensitivityEntry`
- `ch7InverseExactRelativeChangeMax`
- `ch7InverseQuadraticRemainderRelativeMax`
- `ch7InverseQuadraticRemainderRelativeMax_nonneg`
- `ch7InverseQuadraticRemainderRelativeMaxEntryBound`
- `ch7InverseQuadraticRemainderRelativeMaxEntryBound_nonneg`
- `ch7InverseQuadraticRemainderSensitivityEntry_le_of_entry_bound`
- `ch7InverseQuadraticRemainderRelativeMax_le_of_entry_bound`
- `ch7InverseQuadraticRemainderRelativeMax_abs_le_of_entry_bound`
- `ch7_abs_entry_le_infNorm`
- `ch7InverseQuadraticRemainderRelativeMax_le_of_infNorm_bound`
- `ch7InverseQuadraticRemainderRelativeMax_abs_le_of_infNorm_bound`
- `ch7InverseQuadraticRemainderEntry_abs_le`
- `problem7_11_exact_inverse_firstOrder_remainder_identity`
- `problem7_11_exact_inverse_relative_entry_le_linearized_plus_quadratic`
- `problem7_11_exact_inverse_relative_entry_ge_linearized_minus_quadratic`
- `problem7_11_exact_inverse_relative_change_max_ge_linearized_entry_minus_quadratic`
- `problem7_11_exact_inverse_relative_change_max_le_condition_plus_quadratic`
- `problem7_11_exact_inverse_relative_change_max_le_linearized_max_plus_quadratic`
- `problem7_11_exact_inverse_relative_change_max_ge_linearized_max_minus_quadratic`
- `problem7_11_exact_inverse_relative_change_max_le_condition_plus_radius_bound`
- `problem7_11_exact_inverse_relative_change_max_ge_condition_minus_quadratic_of_linearized_attainer`
- `problem7_11_exists_exact_inverse_relative_change_max_lower_witness`
- `problem7_11_quadratic_remainder_relative_scaled_tendsto_zero_of_eventually_bounded`
- `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_quadratic_bound`
- `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_eventually_entry_bound`
- `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_eventually_infNorm_bound`
- `ch7MatAddId`
- `ch7_isRightInverse_of_isLeftInverse`
- `ch7_matAdd_id_abs_solution_bound_of_abs_infNorm_bound`
- `ch7_matAdd_id_det_ne_zero_of_abs_infNorm_bound`
- `ch7_nonsingInv_matAdd_id_entry_abs_le_of_abs_infNorm_bound`
- `ch7_nonsingInv_matAdd_id_infNorm_le_of_abs_infNorm_bound`
- `ch7Problem711PerturbedInverseCandidate`
- `problem7_11_perturbed_inverse_candidate_right_inverse_of_abs_left_product_bound`
- `problem7_11_perturbed_inverse_candidate_infNorm_bound_of_abs_left_product_bound`
- `ch7_abs_left_product_infNorm_le_of_componentwise_bound`
- `problem7_11_eventually_abs_left_product_infNormBound_half_of_componentwise_tendsto_zero`
- `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_eventually_abs_left_product_bound`
- `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_componentwise_tendsto_zero`
- `Ch7InverseComponentwiseRadiusSet`
- `ch7InverseComponentwiseRadiusSup`
- `IsCh7InverseComponentwiseRadiusLimitValue`
- `IsCh7InverseComponentwiseCondValue`
- `ch7Problem711LocalInverseInfNormBound`
- `ch7InverseComponentwiseRadiusRemainderBound`
- `ch7InverseComponentwiseRadiusSet_value_le`
- `exists_ch7InverseComponentwiseRadiusSet_lower_witness`
- `problem7_11_inverse_componentwise_radiusSup_tendsto_linearized`
- `problem7_11_inverse_componentwise_condition_of_positive_radii`

All Chapter 7 declarations in the Lean module are theorem/definition-level work
with no `sorry`, `admit`, local axioms, orphan typeclass hypotheses, or vacuous
proof-only wrappers. Deferred rows below are not claimed complete.

The 2026-06-24 integrated Split 1 re-audit removed the old Split 1-gate
classification from the live Chapter 7 ledger.  Kimon's Split 1 work is
integrated on `split2-integrate-kimon-main`; remaining gaps below are therefore
classified as current Split 2 proof/API work, later-split/later-chapter
deferments, or skips.  Some open rows still use integrated Split 1 declarations
directly or require a thin source-shaped wrapper around them, but dependency on
Split 1 by itself is no longer recorded as a completion blocker.

The current pass closes the arbitrary subordinate-norm Rigal-Gaches block from
§7.1 by reusing the integrated dual-functional and mixed-subordinate APIs:

- `theorem7_1_subordinate_necessary`
- `eq_7_3_subordinate_attaining_perturbations`
- `theorem7_1_subordinate_sufficient`
- `theorem7_1_subordinate`

The current pass also closes the generic normwise condition-number row
equation `(7.5)` by adding a source-radius `lim sup` model and sharp wrapper
theorems:

- `Ch7NormwiseCondEFRadiusSet`
- `ch7NormwiseCondEFRadiusSup`
- `IsCh7NormwiseCondEFRadiusLimitValue`
- `IsCh7NormwiseCondEFValue`
- `eq_7_5_subordinate_conditionNumberRadiusLimitValue_of_positive_radii`
- `eq_7_5_subordinate_conditionNumber_of_positive_radii`

Classification terms used below:

- `CLOSED`: fully proved for the stated Lean surface.
- `PROVE-NOW-SPLIT2`: selected as local Split 2 work in this pass; all such
  rows are either closed or have a concrete next theorem/API target over the
  integrated branch.
- `DEFER-LATER-SPLIT`: belongs naturally to another split's foundations.
- `DEFER-LATER-CHAPTER`: precise but intentionally after a prerequisite
  Chapter 7 block in this report.
- `SKIP`: empirical, expository, or not a mathematical proof target.

Rows that previously mentioned old Split 1 gates have been re-audited
against `docs/LIBRARY_LOOKUP.md`, `examples/LibraryLookup.lean`, and the live
Split 1 modules.  The current branch exposes generic norm, mixed subordinate
norm, condition-product/radius, rank, SVD, Frobenius, and partial spectral-radius
infrastructure.  It does not expose every Chapter 7 source-facing wrapper yet,
notably pseudoinverse existence/projection, diagonal scaling minimization, and
Perron-Frobenius/Bauer scaling.  Those are now listed as current proof/API
follow-up targets rather than external Split 1 blockers.

The 2026-06-25 current-branch API re-audit sharpened those two remaining
source-facing blockers.  Direct searches found the integrated rectangular SVD
surface in `LeanFpAnalysis.FP.Analysis.Norms`, including
`exists_complexMatrixSVDUnitary_diagonal_eq`,
`exists_complexMatrixSVDUnitary_diagonal_eq_with_entry_formula`, and
`exists_isComplexMatrixSVD`, but found no repository or Mathlib
Moore-Penrose/pseudoinverse API, no projection-minimizer theorem for the
full Theorem 7.5 source statement, and no declaration tying the printed
source minimizer-existence theorem to the repository `sInf` model in the
remaining general cases.  The current report now contains conditional
`IsLeast` adapters for those non-endpoint value sets, but not a proof that such
least elements exist.
The same audit found Mathlib's finite matrix irreducibility API
`Matrix.IsIrreducible` and this chapter's certificate-level Bauer positivity
bridges.  The current spectral-interface continuation closes the local bridge
from Chapter 7's finite eigenvalue-modulus carrier to both the generic Split 1
`IsMaxComplexMatrixEigenvalueModulus` carrier and the Mathlib
`spectrum (Matrix.toLin' ...)` modulus set, including real `sSup = ρ`
wrappers for the unscaled, absolute-value, and scaled Bauer products under a
supplied positive Perron-vector certificate.  Current searches still found no
Perron-Frobenius existence theorem producing that positive eigenvector/eigenvalue
from nonnegative irreducibility and no theorem identifying the proved real
spectrum-modulus supremum with Mathlib's Banach-algebra `spectralRadius` value
representation.  These are current Split 2 proof/API gaps, not unresolved
previous-split dependencies.

## Progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 96 | ~2 | Historical snapshot: full source Moore-Penrose/projection/general-minimizer and Bauer work was still being reduced.  Subsequent rows below close the Moore-Penrose construction, row-scale source audit, and conditional Banach-algebra `spectralRadius` bridge under supplied Perron-vector certificates; the current open rows are actual general/non-endpoint minimizer existence plus Perron-Frobenius eigenpair existence and compatible common Bauer scaling. | Medium-high |

Current progress snapshot after the Mathlib `spectralRadius` bridge:

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 96 | ~2 | Full source Moore-Penrose inverse construction/projection-symmetry/general-minimizer packaging, printed Theorem 7.5 row-scale reconciliation, Perron-Frobenius eigenpair existence from irreducibility, and compatible common Bauer scaling for the full Problem 7.10(e) op-2 theorem. The former Banach-algebra `spectralRadius` value-representation gap is closed under supplied positive Perron-vector certificates by the `toLin_spectralRadius...` wrappers. | Medium-high |

Current progress snapshot after the Theorem 7.5 same-`A⁺` conditional source-`min`
continuation:

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 97 | ~2 | The printed-rank Moore-Penrose construction, Penrose-equation witnesses, endpoint/`sInf` scaling wrappers, and same-`A⁺` conditional source-`min` wrappers are now closed for full-column and full-row rank via normal-equations candidates. Remaining Theorem 7.5 work is printed row-scale notation reconciliation with the conjugate-row proof route plus proof of actual general/non-endpoint minimizer existence. Remaining Theorem 7.8/Problem 7.10 work is Perron-Frobenius eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 theorem. | Medium-high |

Current progress snapshot after the Theorem 7.5 literal row-`∞`
source-audit counterexample:

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 98 | ~2 | The printed-rank Moore-Penrose construction, Penrose-equation witnesses, endpoint/`sInf` scaling wrappers, same-`A⁺` conditional source-`min` wrappers, and a formal source-audit counterexample to the literal printed row-`∞` max-entry scaling are now closed. The proved row route remains the conjugate-row/row-`1` scale dictated by the source proof. Remaining Theorem 7.5 work is actual general/non-endpoint minimizer existence rather than row-scale notation reconciliation. Remaining Theorem 7.8/Problem 7.10 work is Perron-Frobenius eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 theorem. | Medium-high |

Current progress snapshot after the Theorem 7.5 `p = 2` global-rescaling
normalization dependency:

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 98 | ~2 | The explicit-`Aplus` `p = 2` right- and left-scaling value-set models now have proved global-rescaling invariance lemmas, so the diagonal normalization step needed for a compact-slice minimizer proof is no longer an unformalized local dependency. Remaining Theorem 7.5 work is still the actual general/non-endpoint source `min` minimizer-existence proof. Remaining Theorem 7.8/Problem 7.10 work is Perron-Frobenius eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 theorem. | Medium-high |

Current progress snapshot after the Theorem 7.5 `p = 2` absolute-sum-one
normalization witness dependency:

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 98 | ~2 | The explicit-`Aplus` `p = 2` right- and left-scaling value-set models now have proved global-rescaling invariance and concrete reciprocal-diagonal witnesses normalized to `∑ |d_i| = 1` on nonempty index sets. This closes another local compact-slice dependency for the remaining source `min` attainment proof but does not itself prove attainment. Remaining Theorem 7.5 work is actual general/non-endpoint source minimizer existence; remaining Theorem 7.8/Problem 7.10 work is Perron-Frobenius eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 theorem. | Medium-high |

Current progress snapshot after the Theorem 7.5 `p = 2` normalized value-set
equality dependency:

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 98 | ~2 | The explicit-`Aplus` `p = 2` right- and left-scaling value sets are now proved equal to their `∑ |d_i| = 1` normalized slices on nonempty index types. This proves the set-level compact-slice reduction needed before an attainment proof, but the source `min` still requires proving an actual least value of the normalized condition-product set. Remaining Theorem 7.8/Problem 7.10 work is unchanged: Perron-Frobenius eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 theorem. | Medium-high |

Current progress snapshot after the Theorem 7.5 `p = 2` normalized
least-certificate transfer:

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 98 | ~2 | The `p = 2` right/left normalized value-set equalities now also transfer `IsLeast` certificates, and the printed-rank Penrose wrappers can consume normalized-slice minima directly. This closes normalized certificate plumbing for the compact-slice path; actual normalized-slice least-value existence remains open. Theorem 7.8/Problem 7.10 is unchanged: Perron-Frobenius eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 theorem. | Medium-high |

Current progress snapshot after the Theorem 7.5 `p = 2` reciprocal-domain
continuity and coercivity pass:

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 98 | ~2 | The normalized `p = 2` right/left value sets are now proved equal to one-diagonal reciprocal image sets, `complexMatrixOp2` and the reciprocal condition products have continuity lemmas, and the normalized reciprocal products have proved boundary/coercivity estimates bounding inverse diagonal coordinates on bounded sublevels. This closes the main local analytic dependencies for the remaining normalized-slice minimizer route; the still-open Theorem 7.5 work is packaging these estimates into a closed compact sublevel and extracting an actual `IsLeast` value. Theorem 7.8/Problem 7.10 remains open only at Perron-Frobenius eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 theorem. | Medium-high |

Latest delta: the Bauer spectrum-interface continuation adds
`complexMatrixEigenvalueModulusSet_eq_toLin_spectrum_modulusSet`,
`ch7_complexEigenvalueModulusSet_eq_complexMatrixEigenvalueModulusSet`,
`ch7_complexEigenvalueModulusSet_eq_toLin_spectrum_modulusSet`,
`ch7_isMaxComplexMatrixEigenvalueModulus_of_isComplexEigenvalueRadius`,
`ch7_toLin_spectrum_modulusSet_sSup_eq_of_isComplexEigenvalueRadius`,
`toLin_spectralRadius_eq_of_spectrum_modulusSet_isGreatest`,
`ch7_toLin_spectralRadius_eq_of_isComplexEigenvalueRadius`,
`ch7_exists_mixedSubordinateMatrixNormValue_le_of_isComplexEigenvalueRadius`,
and source-facing Problem 7.10 product/absolute/scaled wrappers exporting the
positive-Perron-vector certificate to the generic Split 1 maximum-modulus and
norm-existence APIs and to Mathlib's Banach-algebra `spectralRadius`:
`problem7_10a_product_isMaxComplexMatrixEigenvalueModulus_of_positive_eigenvector`,
`problem7_10a_product_exists_mixedSubordinateMatrixNormValue_le_perron_add_delta`,
`problem7_10a_product_toLin_spectrum_modulusSet_sSup_eq_of_positive_eigenvector`,
`problem7_10a_product_toLin_spectralRadius_eq_of_positive_eigenvector`,
`problem7_10b_abs_product_isMaxComplexMatrixEigenvalueModulus_of_positive_eigenvector`,
`problem7_10b_abs_product_exists_mixedSubordinateMatrixNormValue_le_perron_add_delta`,
`problem7_10b_abs_product_toLin_spectrum_modulusSet_sSup_eq_of_positive_eigenvector`,
`problem7_10b_abs_product_toLin_spectralRadius_eq_of_positive_eigenvector`,
`problem7_10a_scaled_product_isMaxComplexMatrixEigenvalueModulus_of_positive_eigenvector`,
`problem7_10a_scaled_product_exists_mixedSubordinateMatrixNormValue_le_perron_add_delta`,
and
`problem7_10a_scaled_product_toLin_spectrum_modulusSet_sSup_eq_of_positive_eigenvector`,
`problem7_10a_scaled_product_toLin_spectralRadius_eq_of_positive_eigenvector`.
This proves that the local Chapter 7 eigenvalue-modulus supremum is exactly the
real supremum of moduli of Mathlib `spectrum (Matrix.toLin' ...)` elements for
the complexified matrix, identifies Mathlib's `spectralRadius` as
`ENNReal.ofReal ρ`, and reuses the integrated Split 1 Problem 6.8 theorem to
obtain consistent norm values at most `ρ + δ`.  Remaining spectral work is
Perron-Frobenius eigenpair existence from irreducibility and compatible common
scaling for the full source theorem.
Previous delta: the Bauer scaled-product spectral continuation adds
`problem7_10a_scaled_product_isComplexEigenvalueRadius_of_positive_eigenvector`,
`problem7_10a_scaled_product_complexEigenvalueModulusSet_isGreatest_of_positive_eigenvector`,
and
`problem7_10a_scaled_product_complexEigenvalueModulusSet_sSup_eq_of_positive_eigenvector`.
These theorems prove that any positive reciprocal two-sided scaling of the
Bauer product keeps the same local finite complex-eigenvalue radius and exact
eigenvalue-modulus `sSup = ρ`, under the already-supplied positive
Perron-vector certificate for `BC`.  This is genuine spectral dependency work;
it still does not prove Perron-Frobenius eigenpair existence from
irreducibility or identify the local finite modulus supremum with Mathlib's
Banach-algebra `spectralRadius`.  Previous delta: the Theorem 7.5
source-rank/min continuation adds
`theorem7_5_p1_column_equilibration_isLeast_right_scalings_of_penrose1_matrix_rank_eq_width`,
`theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings_of_penrose1_matrix_rank_eq_width`,
`theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_penrose1_matrix_rank_eq_width`,
`theorem7_5_lp_column_equilibration_le_card_rpow_sInf_right_scalings_of_penrose1_matrix_rank_eq_width`,
`theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings_of_penrose1_matrix_rank_eq_width`,
`theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings_of_penrose1_matrix_rank_eq_height`,
`theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings_of_penrose1_matrix_rank_eq_height`,
`theorem7_5_p2_row_equilibration_le_sqrt_card_sInf_left_scalings_of_penrose1_matrix_rank_eq_height`,
`theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_penrose1_matrix_rank_eq_height`,
and
`theorem7_5_pinf_row_equilibration_isLeast_left_scalings_of_penrose1_matrix_rank_eq_height`.
These proved adapters derive the one-sided inverse needed by the existing
endpoint least-element, non-endpoint `sInf`, and conditional source-`min`
wrappers from the first Penrose equation `AA⁺A=A` plus the printed matrix rank
hypothesis.  They do not prove the missing non-endpoint minimizer-existence
theorem and do not construct the Moore-Penrose inverse.  Previous delta: the
Theorem 7.5 Penrose-bridge continuation added
`theorem7_5_rect_left_inverse_of_penrose1_rectMatMulVec_injective`,
`theorem7_5_rect_right_inverse_of_penrose1_rectMatMulVec_surjective`,
`theorem7_5_rect_left_inverse_of_penrose1_matrix_rank_eq_width`,
`theorem7_5_rect_right_inverse_of_penrose1_matrix_rank_eq_height`, and the
source-facing symmetric-projection wrappers
`theorem7_5_rect_penrose_injective_symmetric_range_projection_op2Le_one`,
`theorem7_5_rect_penrose_surjective_symmetric_domain_projection_op2Le_one`,
`theorem7_5_rect_penrose_injective_symmetric_range_projection_residual_normSq_isLeast`,
`theorem7_5_rect_penrose_surjective_symmetric_domain_projection_residual_normSq_isLeast`,
`theorem7_5_rect_penrose_injective_symmetric_range_projection_residual_norm_isLeast`,
`theorem7_5_rect_penrose_surjective_symmetric_domain_projection_residual_norm_isLeast`,
`theorem7_5_rect_penrose_matrix_rank_eq_width_symmetric_range_projection_residual_normSq_isLeast`,
`theorem7_5_rect_penrose_matrix_rank_eq_height_symmetric_domain_projection_residual_normSq_isLeast`,
and the Penrose-equation package wrappers
`theorem7_5_rect_left_inverse_symmetric_penrose_equations`,
`theorem7_5_rect_right_inverse_symmetric_penrose_equations`,
`theorem7_5_rect_penrose_injective_symmetric_range_penrose_equations`,
`theorem7_5_rect_penrose_surjective_symmetric_domain_penrose_equations`,
`theorem7_5_rect_penrose_matrix_rank_eq_width_symmetric_range_penrose_equations`,
and
`theorem7_5_rect_penrose_matrix_rank_eq_height_symmetric_domain_penrose_equations`.
The bridge proves `A⁺A=I` from `AA⁺A=A` plus injectivity, and `AA⁺=I` from
`AA⁺A=A` plus surjectivity, so the existing symmetric projection contraction,
orthogonality, and least-residual theorems can now be used under Penrose
equation plus the printed rank hypotheses.  The new package theorems then prove
the second Penrose equation and the complementary product symmetry from the
derived one-sided inverse plus the relevant supplied projection symmetry.  This
is genuine proof work, but it does not construct a Moore-Penrose inverse or
derive the first Penrose equation/projection-symmetry witnesses from the source
rank assumptions.  Previous delta: the Bauer
spectral-radius continuation added local finite eigenvalue-modulus `sSup = ρ`
wrappers under a supplied positive Perron-vector certificate, while full PF
existence from irreducibility and the Mathlib `spectralRadius` bridge remain
open.  Earlier
delta: the Bauer spectral-radius bridge now also has nonzero-nonnegative
irreducible-eigenpair wrappers for the product, absolute product, scaled
product, and one-norm transpose product; full PF existence from irreducibility
and compatible common Bauer scaling remain open.  Earlier
delta: Appendix A.7.15's diagonal attainability sentence is now closed
for every nonsingular diagonal matrix by positive absolute-value scaling to
orthogonal sign-diagonal factors, with exact `sInf = 1` and `IsLeast 1`
theorems.  The previous projection-geometry delta also remains available: the
algebraic projection dependency inside the Theorem 7.5 Moore-Penrose route is
closed for idempotence and symmetric-idempotent operator-2 contraction from
explicit one-sided inverse and symmetry witnesses.  The percentages stay capped
because the source still requires completing actual general/non-endpoint
minimizer existence and closing the Perron-Frobenius existence plus common
Bauer-scaling row.

## GPT-5.5 Pro browser consultations

| Selected claim/blocker | Oracle session/model | Prompt summary | Key route suggested | Adopted/rejected steps | Lean validation | Status |
| --- | --- | --- | --- | --- | --- | --- |
| Theorem 7.8 / Problem 7.10 Perron-Frobenius, Mathlib `spectralRadius`, and compatible Bauer scaling-existence bridge | Intended OpenClaw `openai/gpt-5.5`, session slug `ch7-bauer-pf-oracle-20260625`; external call was not completed | Prepared reviewed math-only packet `chapter_splitting/proof_packets/ch7_bauer_pf_spectral.tex` covering the source statement, current certificate-level Lean surfaces, missing PF/spectral-radius foundations, source-statement audit questions, and requested Lean-friendly dependency order | None: the escalation reviewer rejected the attempted OpenClaw export as external transmission of project-derived packet contents | No advisory result adopted. Continued locally on non-PF theorem-equivalent dependencies: the strict-eigenvalue and irreducible-product `Cx > 0` transfers remain closed; local finite complex-eigenvalue-radius dominance/attainment, generic Split 1 maximum-modulus export, integrated Split 1 norm-existence reuse, and Mathlib `spectrum (Matrix.toLin' ...)` modulus `sSup = ρ` wrappers are now proved under supplied positive Perron-vector certificates for the unscaled, absolute-value, and scaled Bauer products | `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after the spectrum-interface edit; full lookup/build/axiom verification is recorded in the verification section | Superseded below for the conditional Mathlib `spectralRadius` bridge. The packet remains relevant for PF eigenpair existence from irreducibility and compatible common scaling for the Problem 7.10(e) op-2 row |

2026-06-25 local follow-up supersedes the old `spectralRadius` part of this
Oracle row: the Banach-algebra value representation is now closed under the
same supplied positive Perron-vector certificates by
`toLin_spectralRadius_eq_of_spectrum_modulusSet_isGreatest`,
`ch7_toLin_spectralRadius_eq_of_isComplexEigenvalueRadius`, and the Problem
7.10 product/absolute/scaled `...toLin_spectralRadius_eq...` wrappers.  The
current nonzero-nonnegative continuation adds the source-shaped irreducibility
surfaces
`problem7_10a_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector`,
`problem7_10b_abs_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector`,
`problem7_10a_scaled_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector`,
and
`problem7_10e_abs_transpose_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector`.
The Oracle packet remains relevant only for Perron-Frobenius eigenpair
existence from irreducibility and compatible common scaling for the Problem
7.10(e) op-2 row.

## Verification

Bauer spectrum-interface continuation verification:

- `lake build LeanFpAnalysis.FP.Analysis.Norms` passed with `2911` jobs after
  adding `complexMatrixEigenvalueModulusSet_eq_toLin_spectrum_modulusSet`.
- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed.
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3020`
  jobs after rebuilding the target containing the new Chapter 7 wrappers.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean >
  /tmp/ch7_spectrum_lookup.out` passed.
- `lake env lean --stdin` with `#print axioms` for
  `complexMatrixEigenvalueModulusSet_eq_toLin_spectrum_modulusSet`,
  `ch7_toLin_spectrum_modulusSet_sSup_eq_of_isComplexEigenvalueRadius`,
  `ch7_exists_mixedSubordinateMatrixNormValue_le_of_isComplexEigenvalueRadius`,
  `problem7_10a_product_toLin_spectrum_modulusSet_sSup_eq_of_positive_eigenvector`,
  `problem7_10b_abs_product_toLin_spectrum_modulusSet_sSup_eq_of_positive_eigenvector`,
  `problem7_10a_scaled_product_toLin_spectrum_modulusSet_sSup_eq_of_positive_eigenvector`,
  `problem7_10a_product_exists_mixedSubordinateMatrixNormValue_le_perron_add_delta`,
  `problem7_10b_abs_product_exists_mixedSubordinateMatrixNormValue_le_perron_add_delta`,
  and
  `problem7_10a_scaled_product_exists_mixedSubordinateMatrixNormValue_le_perron_add_delta`
  reported only the standard Lean foundations `propext`, `Classical.choice`,
  and `Quot.sound`.
- Focused leading-placeholder scan
  `rg -n "^\s*(sorry|admit|axiom|unsafe)\b|opaque\b"
  LeanFpAnalysis/FP/Analysis/Norms.lean
  LeanFpAnalysis/FP/Analysis/HighamChapter7.lean
  examples/LibraryLookup.lean` found no matches.
- Broader implementation/lookup placeholder scan over `Norms.lean`,
  `HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and
  `examples/LibraryLookup.lean` found no stale wait labels, TODOs, or local
  placeholders; it matched only pre-existing `False.elim` uses in `Norms.lean`,
  not the new declarations.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/Norms.lean
  LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md
  examples/LibraryLookup.lean
  chapter_splitting/reports/chapter7_formalization_report.md
  chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md`
  passed.
- Source re-audit used `pdftotext -layout` on
  `/home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.ch7.pdf`
  and
  `/home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.appa.pdf`.
  Focused searches confirmed the source statements for Theorem 7.8 and Problem
  7.10 still use a Perron vector, spectral radius, and Bauer diagonal scaling;
  the new Lean theorems close the certificate-to-spectrum-modulus bridge, not
  PF existence or Banach-algebra `spectralRadius`.
- `timeout 600s lake build` passed with `3502` jobs.  Warnings were only the
  pre-existing QR/Givens/FastMatMul linter warnings outside Chapter 7.

Initial Chapter 7 pass verification:

- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean LeanFpAnalysis/FP/Analysis.lean`
- `lake env lean examples/LibraryLookup.lean`
- Full `lake build` passed with 3472 jobs.
- `#print axioms` for the then-new final-facing theorems reported only standard
  Lean foundations: `propext`, `Classical.choice`, and `Quot.sound`.

Corollary 7.6 Cholesky-factor source-scale dependency verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean`
- `lake env lean --stdin` with `#print axioms` for the seven new
  `corollary7_6_cholesky_*` theorems reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Focused implementation/lookup scans over `HighamChapter7.lean`,
  `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no
  `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, stale wait labels,
  local placeholder labels, or `False.elim`.
- Broad report-inclusive scans only matched historical command strings and
  prose summarizing axiom checks, not Lean implementation or lookup code.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/HighamChapter7.lean
  docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean
  chapter_splitting/reports/chapter7_formalization_report.md
  chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md`
  passed.
- `timeout 600s lake build` passed with 3502 jobs; warnings were only the
  pre-existing QR/Givens/FastMatMul linter warnings outside Chapter 7.

Corollary 7.6 inverse-Gram/product-square bridge verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/Norms.lean`
- `lake build LeanFpAnalysis.FP.Analysis.Norms`
- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean`
- `lake env lean --stdin` with `#print axioms` for
  `complexMatrixOp2_adjoint_mul_self_eq_sq`,
  `complexMatrixOp2_mul_adjoint_self_eq_sq`,
  `complexMatrixOp2_realRectToCMatrix_transpose_mul_self_eq_sq`,
  `complexMatrixOp2_realRectToCMatrix_mul_transpose_self_eq_sq`,
  `corollary7_6_cholesky_scaled_cond_eq_factor_cond_sq`,
  `corollary7_6_cholesky_inverse_gram_isInverse`, and
  `corollary7_6_cholesky_scaled_inverse_gram_isInverse` reported only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Focused leading-placeholder scans over `Norms.lean`, `HighamChapter7.lean`,
  and `examples/LibraryLookup.lean` found no `sorry`, `admit`, `axiom`,
  `unsafe`, or `opaque` declarations.  Broad implementation/lookup/report
  scans matched only historical report command strings, axiom-summary prose,
  and pre-existing `False.elim` uses in `Norms.lean`, not the new declarations.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/Norms.lean
  LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md
  examples/LibraryLookup.lean
  chapter_splitting/reports/chapter7_formalization_report.md
  chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md`
  passed.
- `timeout 600s lake build` passed with 3502 jobs; warnings were only the
  pre-existing QR/Givens/FastMatMul linter warnings outside Chapter 7.

Proof-completion update verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean > /tmp/higham_library_lookup_ch7_completion.out`
- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
  found no matches.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/HighamChapter7.lean examples/LibraryLookup.lean docs/LIBRARY_LOOKUP.md chapter_splitting/reports/chapter7_formalization_report.md`
- `lake env lean /tmp/ch7_axioms_check.lean` reported only standard Lean
  foundations for the four new Problem 7.7 theorems: `propext`,
  `Classical.choice`, and `Quot.sound`.
- Full `lake build` passed with 3476 jobs. The warnings were pre-existing
  QR/FastMatMul linter warnings outside Chapter 7.

Local-infrastructure update verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean > /tmp/higham_library_lookup_ch7_local.out`
- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
  found no matches.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/HighamChapter7.lean examples/LibraryLookup.lean docs/LIBRARY_LOOKUP.md chapter_splitting/reports/chapter7_formalization_report.md`
- `lake env lean /tmp/ch7_axioms_local_update.lean` reported only standard
  Lean foundations for the new final-facing Problem 7.1 and Problem 7.8
  theorems: `propext`, `Classical.choice`, and `Quot.sound`.
- Full `lake build` passed with 3476 jobs. The warnings were pre-existing
  QR/FastMatMul linter warnings outside Chapter 7.

Exact-resolvent update verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean > /tmp/higham_library_lookup_ch7_exact_resolvent.out`
- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
  found no matches.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/HighamChapter7.lean examples/LibraryLookup.lean docs/LIBRARY_LOOKUP.md chapter_splitting/reports/chapter7_formalization_report.md`
- `lake env lean /tmp/ch7_axioms_exact_resolvent.lean` reported only standard
  Lean foundations for the exact Problem 7.1 resolvent theorems: `propext`,
  `Classical.choice`, and `Quot.sound`.
- Full `lake build` passed with 3476 jobs. The warnings were pre-existing
  QR/FastMatMul linter warnings outside Chapter 7.

Computed-residual re-audit verification:

- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean`
- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean`
  found no matches.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter7_formalization_report.md`
- `#print axioms` for `eq_7_30_conventional_residual_error`,
  `eq_7_31_componentwise_bound`, and `eq_7_31_relative_infNorm_bound`
  reported only `propext`, `Classical.choice`, and `Quot.sound`.
- Full `lake build` passed with 3498 jobs. The warnings were pre-existing
  `QR/Givens` and `FastMatMul` linter warnings outside Chapter 7.

Arbitrary-subordinate-norm wrapper update verification:

- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean`
- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean`
  found no matches.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter7_formalization_report.md`
- `lake env lean /tmp/ch7_axioms_subordinate_update.lean` reported only
  `propext`, `Classical.choice`, and `Quot.sound` for
  `problem7_2_subordinate_scaled_upper` and
  `theorem7_2_subordinate_forward_error_bound`.
- `rg -n "TODO|WAIT-PREVIOUS-SPLIT|WAIT-SPLIT1" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean`
  found no matches.
- Incremental full `lake build` passed with 3498 jobs. The warnings were the
  same pre-existing `QR/Givens`, `GivensQR`, and `FastMatMul` linter warnings
  outside Chapter 7.

Arbitrary-subordinate-norm Rigal-Gaches update verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/Norms.lean`
- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake env lean -o .lake/build/lib/lean/LeanFpAnalysis/FP/Analysis/Norms.olean -i .lake/build/lib/lean/LeanFpAnalysis/FP/Analysis/Norms.ilean LeanFpAnalysis/FP/Analysis/Norms.lean`
- `lake env lean -o .lake/build/lib/lean/LeanFpAnalysis/FP/Analysis/HighamChapter7.olean -i .lake/build/lib/lean/LeanFpAnalysis/FP/Analysis/HighamChapter7.ilean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake env lean examples/LibraryLookup.lean`
- `lake env lean /tmp/ch7_axioms_rigal_subordinate.lean`
- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean`
  found no matches.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/Norms.lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter7_formalization_report.md`
- `#print axioms` for `theorem7_1_subordinate` and
  `eq_7_3_subordinate_attaining_perturbations` reported only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Incremental full `lake build` passed with 3498 jobs. The warnings were the
  same pre-existing `QR/Givens`, `GivensQR`, and `FastMatMul` linter warnings
  outside Chapter 7.

Arbitrary-absolute-norm Theorem 7.4 update verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/Norms.lean`
- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake env lean -o .lake/build/lib/lean/LeanFpAnalysis/FP/Analysis/Norms.olean -i .lake/build/lib/lean/LeanFpAnalysis/FP/Analysis/Norms.ilean LeanFpAnalysis/FP/Analysis/Norms.lean`
- `lake env lean -o .lake/build/lib/lean/LeanFpAnalysis/FP/Analysis/HighamChapter7.olean -i .lake/build/lib/lean/LeanFpAnalysis/FP/Analysis/HighamChapter7.ilean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake env lean examples/LibraryLookup.lean`
- `lake env lean /tmp/ch7_axioms_absolute_norm.lean`
- `rg -n "^\s*(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/Norms.lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
  found no matches.
- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean`
  found no matches.
- `rg -n "TODO|WAIT-PREVIOUS-SPLIT|WAIT-SPLIT1" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean`
  found no matches.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/Norms.lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter7_formalization_report.md`
- A first `timeout 180s lake build` timed out at job `3493/3498` while
  rebuilding cached `LeanFpAnalysis.FP.Analysis.Norms`; rerunning the same
  command then completed successfully with `3498` jobs. The only warnings were
  the same pre-existing `QR/Givens`, `GivensQR`, and `FastMatMul` linter
  warnings outside Chapter 7.

Generic normwise condition-number `(7.5)` update verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean`
- `lake env lean /tmp/ch7_eq75_axioms.lean`
- `rg -n "^\s*(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter7_formalization_report.md`
  found no leading placeholder declarations.
- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean`
  found no matches.
- `rg -n "TODO|WAIT-PREVIOUS-SPLIT|WAIT-SPLIT1" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean`
  found no matches.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter7_formalization_report.md chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md`
- `lake env lean /tmp/ch7_eq75_axioms.lean` reported only the standard Lean
  foundations `propext`, `Classical.choice`, and `Quot.sound` for
  `eq_7_5_subordinate_conditionNumberRadiusLimitValue_of_positive_radii` and
  `eq_7_5_subordinate_conditionNumber_of_positive_radii`.
- The focused file check, targeted Chapter 7 module build (`3006` jobs), and
  lookup check all passed.
- Full `timeout 180s lake build` passed with `3498` jobs. The warnings were
  the same pre-existing `QR/Givens`, `GivensQR`, and `FastMatMul` linter
  warnings outside Chapter 7.

Sparse residual Problem 7.13 update verification:

- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean`
- `lake env lean /tmp/ch7_problem713_axioms.lean`
- `rg -n "^\s*(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter7_formalization_report.md`
  found no leading placeholder declarations.
- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean`
  found no matches.
- `rg -n "TODO|WAIT-PREVIOUS-SPLIT|WAIT-SPLIT1" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean`
  found no matches.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter7_formalization_report.md chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md`
- `lake env lean /tmp/ch7_problem713_axioms.lean` reported only the standard
  Lean foundations `propext`, `Classical.choice`, and `Quot.sound` for
  `problem7_13_sparse_residual_error` and
  `problem7_13_relative_infNorm_bound`.
- Incremental full `timeout 180s lake build` passed with `3498` jobs. The
  warnings were the same pre-existing `QR/Givens`, `GivensQR`, and
  `FastMatMul` linter warnings outside Chapter 7.

Columnwise data-condition Problem 7.6(b) update verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean` passed after the targeted
  Chapter 7 build refreshed the olean containing
  `problem7_6b_columnwise_data_condition_bounds`.
- `lake env lean /tmp/ch7_problem76b_axioms.lean`
- `rg -n "^\s*(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter7_formalization_report.md`
  found no leading placeholder declarations.
- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean`
  found no matches.
- `rg -n "TODO|WAIT-PREVIOUS-SPLIT|WAIT-SPLIT1" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean`
  found no matches.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter7_formalization_report.md chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md`
  passed.
- `#print axioms` for `problem7_6b_columnwise_data_condition_bounds` reported
  only the standard Lean foundations `propext`, `Classical.choice`, and
  `Quot.sound`.
- Incremental full `timeout 180s lake build` passed with `3498` jobs. The
  warnings were the same pre-existing `QR/Givens`, `GivensQR`, and
  `FastMatMul` linter warnings outside Chapter 7.

Problem 7.9 finite scalar-output formula verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean` passed after the targeted
  Chapter 7 build refreshed the olean containing
  `problem7_9_linearized_componentwise_functional_formula` and the two
  finite `χ >= 1` specializations, and later refreshed the olean containing
  `problem7_9_linearized_normwise_functional_formula`.
- `lake env lean /tmp/ch7_problem79_axioms.lean`
- `#print axioms` for `ch7Problem79_firstOrder_abs_le`,
  `ch7Problem79_linearizedRelativeChange_le`,
  `ch7Problem79_attaining_firstOrder_eq`, and
  `problem7_9_linearized_componentwise_functional_formula`,
  `ch7Problem79_linearFunctional_eq_adjointWeight_mul_Ax`,
  `ch7Problem79ComponentwiseSensitivity_ge_abs_functional_of_abs_matrix`,
  `ch7Problem79ComponentwiseSensitivity_ge_abs_functional_of_abs_rhs`,
  `problem7_9_linearized_componentwise_functional_ge_one_of_abs_matrix`, and
  `problem7_9_linearized_componentwise_functional_ge_one_of_abs_rhs`,
  `ch7Problem79_normwise_firstOrder_abs_le`,
  `ch7Problem79_normwiseLinearizedRelativeChange_le`,
  `ch7Problem79_normwiseAttainingDeltaA_bound`,
  `ch7Problem79_normwiseAttainingDeltaB_bound`,
  `ch7Problem79_normwise_attaining_firstOrder_eq`, and
  `problem7_9_linearized_normwise_functional_formula`
  reported only the standard Lean foundations `propext`, `Classical.choice`,
  and `Quot.sound`.
- Incremental full `timeout 180s lake build` passed with `3498` jobs. The
  warnings were the same pre-existing `QR/Givens`, `GivensQR`, and
  `FastMatMul` linter warnings outside Chapter 7.

Problem 7.11 first-order inverse componentwise update verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean` passed after the targeted
  Chapter 7 build refreshed the olean containing
  `problem7_11_linearized_inverse_componentwise_formula`.
- `lake env lean /tmp/ch7_problem711_axioms.lean`
- `rg -n "^\s*(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter7_formalization_report.md chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md`
  found no leading placeholder declarations.
- `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean`
  found no matches.
- `rg -n "TODO|WAIT-PREVIOUS-SPLIT|WAIT-SPLIT1" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean`
  found no matches.
- `git diff --check -- LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter7_formalization_report.md chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md`
  passed.
- `#print axioms` for
  `problem7_11_linearized_inverse_componentwise_upper_and_sign_attainment` and
  `problem7_11_linearized_inverse_componentwise_formula` reported only the
  standard Lean foundations `propext`, `Classical.choice`, and `Quot.sound`.
- Incremental full `timeout 180s lake build` passed with `3498` jobs. The
  warnings were the same pre-existing `QR/Givens`, `GivensQR`, and
  `FastMatMul` linter warnings outside Chapter 7.

Problem 7.11 exact quadratic-remainder upper-envelope verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean`
- `lake env lean /tmp/ch7_problem711_remainder_axioms.lean`
- Focused placeholder scans over the Chapter 7 implementation, lookup files,
  and Chapter 7/Split 2 reports found no implementation placeholders.
- `git diff --check` passed over the touched Chapter 7 implementation, lookup,
  example, and report files.
- Incremental full `timeout 180s lake build` passed with only the known
  pre-existing QR/Givens/FastMatMul warnings outside Chapter 7.

Problem 7.11 finite-radius, lower-envelope/lower-witness, and conditional asymptotic verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean`
- `lake env lean /tmp/ch7_problem711_radius_axioms.lean`
- The axiom audit file checks `ch7InverseQuadraticRemainderRelativeMax_nonneg`,
  `problem7_11_exact_inverse_relative_change_max_le_condition_plus_radius_bound`,
  `problem7_11_quadratic_remainder_relative_scaled_tendsto_zero_of_eventually_bounded`,
  `problem7_11_exact_inverse_relative_entry_ge_linearized_minus_quadratic`,
  `problem7_11_exact_inverse_relative_change_max_ge_linearized_entry_minus_quadratic`,
  and
  `problem7_11_exact_inverse_relative_change_max_ge_condition_minus_quadratic_of_linearized_attainer`,
  plus `problem7_11_exists_exact_inverse_relative_change_max_lower_witness`.
- Focused placeholder scans over the Chapter 7 implementation, lookup files,
  and Chapter 7/Split 2 reports found no implementation placeholders.
- `git diff --check` passed over the touched Chapter 7 implementation, lookup,
  example, and report files.
- Incremental full `timeout 180s lake build` passed with only the known
  pre-existing QR/Givens/FastMatMul warnings outside Chapter 7.
- The FLARE dev-log directory is not a git repository; direct trailing-
  whitespace and conflict-marker scans over `dev-logs/CURRENT.md` found no
  matches.

Problem 7.11 exact-to-linearized asymptotic bridge verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean`
- `lake env lean /tmp/ch7_problem711_asymptotic_bridge_axioms.lean`
- The axiom audit file checks
  `problem7_11_exact_inverse_relative_change_max_le_linearized_max_plus_quadratic`,
  `problem7_11_exact_inverse_relative_change_max_ge_linearized_max_minus_quadratic`,
  and
  `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_quadratic_bound`.
- Focused placeholder scans over the Chapter 7 implementation, lookup files,
  and Chapter 7/Split 2 reports found no implementation placeholders.
- `git diff --check` passed over the touched Chapter 7 implementation, lookup,
  example, and report files.
- Incremental full `timeout 180s lake build` passed with only the known
  pre-existing QR/Givens/FastMatMul warnings outside Chapter 7.
- Direct trailing-whitespace and conflict-marker scans over
  `/home/mymel/flare-bundle/dev-logs/CURRENT.md` found no matches.

Problem 7.11 entrywise inverse-bound bridge verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean`
- `lake env lean /tmp/ch7_problem711_entry_bound_axioms.lean`
- The axiom audit file checks
  `ch7InverseQuadraticRemainderRelativeMaxEntryBound_nonneg`,
  `ch7InverseQuadraticRemainderRelativeMax_abs_le_of_entry_bound`, and
  `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_eventually_entry_bound`.
- Focused placeholder scans over the Chapter 7 implementation, lookup files,
  and Chapter 7/Split 2 reports found no implementation placeholders.
- `git diff --check` passed over the touched Chapter 7 implementation, lookup,
  example, and report files.
- Incremental full `timeout 180s lake build` passed with only the known
  pre-existing QR/Givens/FastMatMul warnings outside Chapter 7.

Problem 7.11 infinity-norm inverse-bound bridge verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean`
- `lake env lean /tmp/ch7_problem711_infNorm_bound_axioms.lean`
- The axiom audit file checks `ch7_abs_entry_le_infNorm`,
  `ch7InverseQuadraticRemainderRelativeMax_le_of_infNorm_bound`,
  `ch7InverseQuadraticRemainderRelativeMax_abs_le_of_infNorm_bound`, and
  `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_eventually_infNorm_bound`.
- Focused placeholder scans over the Chapter 7 implementation, lookup files,
  and Chapter 7/Split 2 reports found no implementation placeholders.
- `git diff --check` passed over the touched Chapter 7 implementation, lookup,
  example, and report files.
- Incremental full `timeout 180s lake build` passed with only the known
  pre-existing QR/Givens/FastMatMul warnings outside Chapter 7.

Problem 7.11 local inverse-family and componentwise `ε → 0` bridge verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean`
- `lake env lean /tmp/ch7_problem711_local_inverse_axioms.lean`
- The axiom audit file checks `ch7MatAddId`,
  `ch7_isRightInverse_of_isLeftInverse`,
  `ch7_matAdd_id_abs_solution_bound_of_abs_infNorm_bound`,
  `ch7_matAdd_id_det_ne_zero_of_abs_infNorm_bound`,
  `ch7_nonsingInv_matAdd_id_entry_abs_le_of_abs_infNorm_bound`,
  `ch7_nonsingInv_matAdd_id_infNorm_le_of_abs_infNorm_bound`,
  `ch7Problem711PerturbedInverseCandidate`,
  `problem7_11_perturbed_inverse_candidate_right_inverse_of_abs_left_product_bound`,
  `problem7_11_perturbed_inverse_candidate_infNorm_bound_of_abs_left_product_bound`,
  `ch7_abs_left_product_infNorm_le_of_componentwise_bound`,
  `problem7_11_eventually_abs_left_product_infNormBound_half_of_componentwise_tendsto_zero`,
  `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_eventually_abs_left_product_bound`,
  and
  `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_componentwise_tendsto_zero`.
- Focused placeholder scans over the Chapter 7 implementation, lookup files,
  and Chapter 7/Split 2 reports found no implementation placeholders.
- `git diff --check` passed over the touched Chapter 7 implementation, lookup,
  example, and report files.
- Incremental full `timeout 180s lake build` passed with only the known
  pre-existing QR/Givens/FastMatMul warnings outside Chapter 7.

Problem 7.4 PSD scaled-factor condition-bound verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean`
- `lake env lean /tmp/ch7_problem74_axioms.lean`
- The axiom audit file checks
  `problem7_4_abs_entry_le_one_of_finitePSD_diag_one`,
  `problem7_4_unitDiagonal_entryBound_condition_bounds`, and
  `problem7_4_unitDiagonal_finitePSD_condition_bounds`; all report only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Focused placeholder and stale-wait scans over the Chapter 7 implementation,
  lookup files, examples, and reports found no implementation placeholders.
- `git diff --check` passed over the touched Chapter 7 implementation, lookup,
  example, and report files.
- Incremental full `timeout 180s lake build` passed with `3498` jobs and only
  the known pre-existing QR/Givens/FastMatMul warnings outside Chapter 7.
- Direct tab/conflict-marker scans passed for the new Chapter 7 Problem 7.4
  dev log plus `/home/mymel/flare-bundle/dev-logs/CURRENT.md` and `INDEX.md`.

Equation `(7.20)`-`(7.21)` Euclidean column-equilibration dependency verification:

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`
- `lake env lean examples/LibraryLookup.lean`
- `lake env lean /tmp/ch7_eq720_eq721_axioms.lean`
- Post-implementation source audit re-read the Theorem 7.5 passage and confirmed
  this pass matches only the closed `p = 2` column-equilibration content of
  `(7.20)`-`(7.21)`, the `p = 1` pairwise column-scaling specialization, and
  the `p = ∞` pairwise row-scaling specialization of `(7.19)`, not the full
  `(7.18)`-`(7.22)` minimization theorem.
- Focused placeholder scans over the Chapter 7 implementation, lookup files,
  examples, and reports found no implementation placeholders.
- `git diff --check` passed over the touched Chapter 7 implementation, lookup,
  example, and report files.
- Incremental full `timeout 180s lake build` passed with only the known
  pre-existing QR/Givens/FastMatMul warnings outside Chapter 7.

## Primary Label Inventory

Latest inventory update after the Theorem 7.5 Moore-Penrose construction pass:
the printed-rank Moore-Penrose construction subrow is `CLOSED` for both
full-column rank and full-row rank.  The closed declarations are
`theorem7_5_exists_rect_left_inverse_symmetric_range_of_rectMatMulVec_injective`,
`theorem7_5_exists_rect_left_inverse_symmetric_range_of_matrix_rank_eq_width`,
`theorem7_5_exists_rect_right_inverse_symmetric_domain_of_matrix_rank_eq_height`,
`theorem7_5_exists_rect_penrose_equations_of_rectMatMulVec_injective`,
`theorem7_5_exists_rect_penrose_equations_of_matrix_rank_eq_width`,
`theorem7_5_exists_rect_penrose_equations_of_matrix_rank_eq_height`,
`theorem7_5_p1_column_equilibration_exists_penrose_of_matrix_rank_eq_width`,
`theorem7_5_p2_column_equilibration_exists_penrose_of_matrix_rank_eq_width`,
`theorem7_5_lp_column_equilibration_exists_penrose_of_matrix_rank_eq_width`,
`theorem7_5_lp_dual_row_equilibration_exists_penrose_of_matrix_rank_eq_height`,
`theorem7_5_p2_row_equilibration_exists_penrose_of_matrix_rank_eq_height`, and
`theorem7_5_pinf_row_equilibration_exists_penrose_of_matrix_rank_eq_height`.
These theorems construct the normal-equations candidates
`A⁺ = (AᵀA)⁻¹Aᵀ` and `A⁺ = Aᵀ(AAᵀ)⁻¹`, prove the relevant one-sided
inverse and projection symmetry witness, prove all four Penrose
equations/symmetry conditions, and attach the endpoint or `sInf` scaling
conclusion to the same constructed `A⁺`.  This is genuine mathematical proof
work using Mathlib `Matrix.PosDef`, nonsingular inverse, Hermitian congruence,
rank-transpose, and the repository's existing rectangular scaling/projection
theorems; it is not an assumption, axiom, certificate field, or vacuous
definition.

Latest inventory update after the same-`A⁺` conditional source-`min`
continuation: the constructed Moore-Penrose inverse is now also connected to
the existing non-endpoint source-minimum inequalities by
`theorem7_5_p2_column_equilibration_exists_penrose_min_imp_of_matrix_rank_eq_width`,
`theorem7_5_lp_column_equilibration_exists_penrose_min_imp_of_matrix_rank_eq_width`,
`theorem7_5_lp_dual_row_equilibration_exists_penrose_min_imp_of_matrix_rank_eq_height`,
and
`theorem7_5_p2_row_equilibration_exists_penrose_min_imp_of_matrix_rank_eq_height`.
Each wrapper existentially returns the normal-equations Moore-Penrose candidate,
proves the Penrose-equation/symmetry package for that same `A⁺`, and then
applies the source `min` inequality for any supplied `IsLeast` certificate.
These are genuine proof wrappers over the constructed `A⁺`; they do not assert
that non-endpoint diagonal-scaling minimizers exist.  At this point the
remaining Theorem 7.5 rows were printed row-scale notation reconciliation and
actual non-endpoint minimizer existence; the row-scale source audit immediately
below supersedes that first item.  There is no previous-split dependency for
these remaining Theorem 7.5 rows.

Latest inventory update after the literal row-`∞` source-audit continuation:
`theorem7_5_literal_printed_row_inf_scale_counterexample` proves that the
printed row-scale notation in Theorem 7.5 cannot be read literally at `p = ∞`
as scaling by reciprocal maximum absolute row entries.  The counterexample
matrix has row max-entry norm one in every row, so the literal scale is the
identity, has a proved inverse-side witness, and has condition product `40/9`;
a reciprocal alternative row scale has condition product `31/9`.  Therefore the
literal printed row-`∞` minimizer row is refuted by Lean proof, and the formal
Theorem 7.5 row route is the already proved conjugate-row/row-`1` route from
the source proof.  This closes the row-scale reconciliation as a source-audit
decision; it does not prove existence of general/non-endpoint diagonal-scaling
minimizers.  There is no previous-split dependency for this audit theorem or
for the remaining non-endpoint minimizer-existence target.

Latest inventory update after the `p = 2` normalized least-certificate transfer:
the normalized right/left value-set equality dependencies now also carry
`IsLeast` certificates between the unrestricted reciprocal value set and the
`∑ |d_i| = 1` normalized slice, through
`ch7Op2RightScaledCondSet_isLeast_iff_sum_abs_normalized` and
`ch7Op2LeftScaledCondSet_isLeast_iff_sum_abs_normalized`.  The conditional
source-`min` adapters
`theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_normalized`,
`theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_rect_left_inverse_of_normalized`,
`theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_normalized`,
and
`theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_rect_right_inverse_of_normalized`
then consume normalized-slice least certificates directly.  The printed-rank
wrappers
`theorem7_5_p2_column_equilibration_exists_penrose_min_normalized_imp_of_matrix_rank_eq_width`
and
`theorem7_5_p2_row_equilibration_exists_penrose_min_normalized_imp_of_matrix_rank_eq_height`
combine the already-proved normal-equations Moore-Penrose construction with
those normalized-slice certificates.  This is genuine proof plumbing for the
remaining compact-slice path; it still does not prove that the normalized slice
has a least value.  There is no previous-split dependency for the remaining
attainment target.

| Source item | Classification | Lean entry points or decision |
| --- | --- | --- |
| Theorem 7.1, Rigal-Gaches backward error | `CLOSED` | `rigal_gaches_necessary`, `rigal_gaches_sufficient`, `rigal_gaches`, `theorem7_1_subordinate_necessary`, `eq_7_3_subordinate_attaining_perturbations`, `theorem7_1_subordinate_sufficient`, `theorem7_1_subordinate` |
| Theorem 7.2, normwise forward error | `CLOSED` | `normwise_perturbation_bound`, `normwise_forward_error_exact`, `normwise_forward_error_exact_relative_infNorm`, `theorem7_2_subordinate_forward_error_bound` |
| Theorem 7.3, Oettli-Prager | `CLOSED` | `oettli_prager_necessary`, `oettli_prager_sufficient`, `oettli_prager` |
| Theorem 7.4, componentwise forward error | `CLOSED` | `componentwise_forward_error`, `componentwise_forward_error_exact`, `componentwise_forward_error_exact_relative_infNorm`, `theorem7_4_absolute_forward_error_bound`, `ch7CondEFAtSolutionInf` |
| Theorem 7.5, van der Sluis diagonal scaling | `PROVE-NOW-SPLIT2`; `CLOSED` for finite-real `p` pairwise/`sInf` column scaling, finite-real conjugate-row pairwise/`sInf` scaling for `(7.19)`, finite-real right/left value-set nonempty/bounded-below/nonnegative-infimum infrastructure, `p = 2` right/left global-rescaling normalization invariance, absolute-sum-one normalized witnesses, equality of the unrestricted p=2 value sets with the normalized slices, normalized reciprocal one-diagonal image-set equivalences, reciprocal product continuity, finite positive lower-bound/coercivity estimates for normalized reciprocal sublevels, and normalized `IsLeast` transfer/wrapper plumbing for the value-set minimizer path, conditional source-`min` adapters under supplied `IsLeast` certificates, one-sided-inverse rank/positivity wrappers, injective/surjective and printed-Matrix-rank forms, Penrose1-to-one-sided-inverse bridges, Penrose-equation packages, normal-equations Moore-Penrose construction for full column/row rank, endpoint least-element same-`A⁺` wrappers, non-endpoint `sInf` same-`A⁺` wrappers, same-`A⁺` conditional source-`min` wrappers, normalized-slice same-`A⁺` printed-rank conditional source-`min` wrappers, and the literal printed row-`∞` source-audit counterexample | Integrated branch supplies rectangular `p`-norm, rank, SVD, and Frobenius foundations.  Key source-facing declarations include `continuous_complexMatrixOp2`, `ch7Op2RightScaledCondNormalizedSet`, `ch7Op2RightScaledCondReciprocalNormalizedSet`, `ch7Op2RightScaledCond_global_scale`, `ch7Op2RightScaledCond_mem_set_global_scale`, `ch7_sum_abs_pos_of_reciprocal`, `ch7_exists_inv_card_le_abs_of_sum_abs_eq_one`, `ch7_exists_pos_le_all_fin`, `ch7Op2RightScaledCond_sum_abs_normalized_witness`, `ch7Op2RightScaledCondSet_eq_sum_abs_normalized`, `ch7Op2RightScaledCondSet_isLeast_iff_sum_abs_normalized`, `ch7Op2RightScaledCondNormalizedSet_eq_reciprocal_normalized`, `ch7Op2RightScaledCondNormalizedSet_isLeast_iff_reciprocal_normalized`, `continuousOn_ch7Op2RightScaledCond_reciprocal`, `ch7RectColumnNorm2_le_complexMatrixOp2_realRectToCMatrix`, `ch7_exists_pos_le_all_inv_card_mul_column_norm2`, `ch7RectRightScale_column_norm_le_complexMatrixOp2`, `ch7Op2RightScaledCond_reciprocal_lower_bound`, `ch7Op2RightScaledCond_reciprocal_normalized_lower_exists`, `ch7Op2RightScaledCond_reciprocal_normalized_inv_abs_le_of_le`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_normalized`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_rect_left_inverse_of_normalized`, `ch7Op2LeftScaledCondNormalizedSet`, `ch7Op2LeftScaledCondReciprocalNormalizedSet`, `ch7Op2LeftScaledCond_global_scale`, `ch7Op2LeftScaledCond_mem_set_global_scale`, `ch7Op2LeftScaledCond_sum_abs_normalized_witness`, `ch7Op2LeftScaledCondSet_eq_sum_abs_normalized`, `ch7Op2LeftScaledCondSet_isLeast_iff_sum_abs_normalized`, `ch7Op2LeftScaledCondNormalizedSet_eq_reciprocal_normalized`, `ch7Op2LeftScaledCondNormalizedSet_isLeast_iff_reciprocal_normalized`, `continuousOn_ch7Op2LeftScaledCond_reciprocal`, `ch7RectRowNorm2_le_complexMatrixOp2_realRectToCMatrix`, `ch7_exists_pos_le_all_inv_card_mul_row_norm2`, `ch7RectLeftScale_row_norm_le_complexMatrixOp2`, `ch7Op2LeftScaledCond_reciprocal_lower_bound`, `ch7Op2LeftScaledCond_reciprocal_normalized_lower_exists`, `ch7Op2LeftScaledCond_reciprocal_normalized_inv_abs_le_of_le`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_normalized`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_rect_right_inverse_of_normalized`, `theorem7_5_exists_rect_penrose_equations_of_matrix_rank_eq_width`, `theorem7_5_exists_rect_penrose_equations_of_matrix_rank_eq_height`, `theorem7_5_p1_column_equilibration_exists_penrose_of_matrix_rank_eq_width`, `theorem7_5_p2_column_equilibration_exists_penrose_of_matrix_rank_eq_width`, `theorem7_5_lp_column_equilibration_exists_penrose_of_matrix_rank_eq_width`, `theorem7_5_lp_dual_row_equilibration_exists_penrose_of_matrix_rank_eq_height`, `theorem7_5_p2_row_equilibration_exists_penrose_of_matrix_rank_eq_height`, `theorem7_5_pinf_row_equilibration_exists_penrose_of_matrix_rank_eq_height`, `theorem7_5_p2_column_equilibration_exists_penrose_min_imp_of_matrix_rank_eq_width`, `theorem7_5_lp_column_equilibration_exists_penrose_min_imp_of_matrix_rank_eq_width`, `theorem7_5_lp_dual_row_equilibration_exists_penrose_min_imp_of_matrix_rank_eq_height`, `theorem7_5_p2_row_equilibration_exists_penrose_min_imp_of_matrix_rank_eq_height`, `theorem7_5_p2_column_equilibration_exists_penrose_min_normalized_imp_of_matrix_rank_eq_width`, `theorem7_5_p2_row_equilibration_exists_penrose_min_normalized_imp_of_matrix_rank_eq_height`, and `theorem7_5_literal_printed_row_inf_scale_counterexample`.  The printed row-`∞` literal max-entry interpretation is now refuted by exact Lean arithmetic (`40/9` versus `31/9`), so the formal row route remains the conjugate-row/row-`1` route dictated by the source proof.  The remaining target is proof of actual minimizer existence for the general/non-endpoint source `min` statements; the new reciprocal-domain continuity and coercivity estimates close the main local analytic dependencies but do not yet package a closed compact sublevel or extract the `IsLeast` value.  No previous-split dependency remains for this target |
| Theorem 7.5 Moore-Penrose projection dependency | `CLOSED` for algebraic idempotence, range/domain fixing, residual orthogonality, squared-/ordinary-norm best approximation, symmetric-idempotent operator-2 contraction, Penrose1/rank wrappers, Penrose-equation packages, and normal-equations Moore-Penrose construction/projection-symmetry witnesses from the printed rank hypotheses | Reusable rectangular algebra is closed by `rectMatMul_id_left`, `rectMatMul_id_right`, `rectMatMul_assoc`, `rectMatMul_rangeProjection_idempotent_of_left_inverse`, and `rectMatMul_domainProjection_idempotent_of_right_inverse` in `MatrixAlgebra.lean`.  Source-facing declarations include the projection wrappers `theorem7_5_rect_penrose_injective_symmetric_range_projection_op2Le_one`, `theorem7_5_rect_penrose_surjective_symmetric_domain_projection_op2Le_one`, residual-minimizer wrappers, Penrose-equation wrappers, and the constructed existence wrappers `theorem7_5_exists_rect_left_inverse_symmetric_range_of_matrix_rank_eq_width`, `theorem7_5_exists_rect_right_inverse_symmetric_domain_of_matrix_rank_eq_height`, `theorem7_5_exists_rect_penrose_equations_of_matrix_rank_eq_width`, and `theorem7_5_exists_rect_penrose_equations_of_matrix_rank_eq_height`.  These declarations use proved normal-equations candidates, not hidden assumptions, orphan classes, certificate fields, or vacuous definitions |
| Corollary 7.6, SPD diagonal scaling | `CLOSED` in the repository's explicit inverse-Gram and `sInf` model; no minimizer-attainment theorem is asserted | `ch7SymmetricDiagEquilibratingScale2`, `ch7SymmetricDiagEquilibratingInvScale2`, `corollary7_6_cholesky_diag_eq_column_norm_sq`, `corollary7_6_cholesky_diag_invScale_eq_column_norm`, `corollary7_6_cholesky_diag_scale_eq_column_equilibrating`, `corollary7_6_cholesky_column_norm_pos`, `corollary7_6_cholesky_factor_column_equilibrated`, `corollary7_6_cholesky_factor_op2Le_sqrt_card`, `corollary7_6_cholesky_factor_column_scaling_le_sqrt_card_sInf_right_scalings`, `ch7SymmetricOp2ScaledCond`, `ch7SymmetricOp2ScaledCondSet`, `ch7SymmetricOp2ScaledCond_mem_set`, `ch7SymmetricOp2ScaledCondSet_nonempty`, `ch7SymmetricOp2ScaledCond_nonneg`, `ch7SymmetricOp2ScaledCondSet_bddBelow`, `ch7SymmetricOp2ScaledCondSet_sInf_nonneg`, `ch7CholeskyInverseGram`, `corollary7_6_cholesky_scaled_gram_eq`, `corollary7_6_cholesky_scaled_inverse_gram_eq`, `corollary7_6_cholesky_scaled_cond_eq_factor_cond_sq`, `ch7Op2RightScaledCondSet_sInf_nonneg`, `corollary7_6_cholesky_scaled_cond_le_card_sInf_right_scalings_sq`, `corollary7_6_cholesky_right_sInf_sq_le_symmetric_sInf`, `corollary7_6_cholesky_scaled_cond_le_card_sInf_symmetric_scalings`, `corollary7_6_cholesky_inverse_gram_isInverse`, and `corollary7_6_cholesky_scaled_inverse_gram_isInverse` prove that `D* = diag(a_jj^{-1/2})` is the `p = 2` column-equilibrating scale for a Cholesky factor `R`, prove `Rinv Rinvᵀ` is the inverse-side witness for `RᵀR`, transport it to `DAD`, prove the corresponding operator-2 condition product is `κ₂(RD)^2`, combine it with the factor `sInf` bound to obtain the explicit `n * (sInf factor-values)^2` inequality, and transfer the factor infimum square to the two-sided SPD scaling infimum. The final theorem proves `κ₂(D*AD*) <= n * sInf {κ₂(DAD)}` over reciprocal diagonal two-sided scalings, which is the source `(7.23)` minimization statement modeled as an infimum rather than as an attained minimum |
| Theorem 7.7, Stewart-Sun Frobenius scaling | `CLOSED` | `theorem7_7_stewart_sun_frobenius_scaling_of_left_inverse`, with supporting definitions and lower-bound/attainment lemmas `ch7StewartSunFrobeniusValue`, `ch7FrobeniusRightScaledCond`, `theorem7_7_frobenius_right_scaling_lower_bound`, and `theorem7_7_stewart_sun_frobenius_scaling` |
| Theorem 7.8, Bauer two-sided scaling | `PROVE-NOW-SPLIT2`; `CLOSED` for the Problem 7.10(a) algebraic lower-bound/attainment core, the scaled-inverse `kappaInf` transport, the Problem 7.10(b) `B = |A|`, `C = |A⁻¹|` absolute-value instantiation under an explicit positive Perron-vector certificate, the positive-entry-to-irreducibility adapter, the Problem 7.10(c) `CB(Cx)` eigenvector algebra, the Problem 7.10(d) source-shaped irreducible-product `Cx > 0` transfer under a supplied positive eigenvector certificate, the Problem 7.10(e) one-norm transpose-certificate branch and original-product irreducibility bridge, the fixed-scaling 2-norm interpolation step, the conditional `sInf` upper-bound packaging, the one-/infinity-/op-2 value-set bounded-below/nonnegative-infimum infrastructure, the certificate-level `sInf = ρ` equalities plus `IsLeast` minimum-attainment wrappers for Problem 7.10(a)/(b)/(e) one-norm, and the positive-scaling local finite eigenvalue-radius/greatest-value/`sSup`, generic Split 1 maximum-modulus export, integrated norm-existence reuse, Mathlib spectrum-modulus `sSup`, and Mathlib `spectralRadius` wrappers for the Bauer products, including the source-shaped irreducible/nonzero-nonnegative eigenpair interfaces | `problem7_10a_scaled_infCond_ge_perron_of_positive_eigenvector` and `problem7_10a_canonical_scaled_infCond_eq_perron_of_positive_eigenvector` prove the two-sided diagonal scaling algebra without assuming the minimization conclusion, and `problem7_10a_scaledInfCondSet_sInf_eq_perron_of_positive_eigenvector` plus `problem7_10a_scaledInfCondSet_isLeast_perron_of_positive_eigenvector` package the positive reciprocal scaling values as exact `sInf = ρ` and least-value theorems under the same certificate; `problem7_10a_scaled_product_isComplexEigenvalueRadius_of_positive_eigenvector`, `problem7_10a_scaled_product_complexEigenvalueModulusSet_isGreatest_of_positive_eigenvector`, and `problem7_10a_scaled_product_complexEigenvalueModulusSet_sSup_eq_of_positive_eigenvector` prove that every positive reciprocal two-sided scaling has the same attained local complex-eigenvalue radius and exact eigenvalue-modulus `sSup = ρ` under that certificate; `ch7_isMaxComplexMatrixEigenvalueModulus_of_isComplexEigenvalueRadius`, `ch7_exists_mixedSubordinateMatrixNormValue_le_of_isComplexEigenvalueRadius`, `complexMatrixEigenvalueModulusSet_eq_toLin_spectrum_modulusSet`, and the Problem 7.10 product/absolute/scaled `...toLin_spectrum_modulusSet_sSup_eq...` wrappers export the same certificates to the integrated Split 1 maximum-modulus/norm-existence APIs and to Mathlib spectrum-modulus `sSup = ρ`; `problem7_10a_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector`, `problem7_10b_abs_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector`, `problem7_10a_scaled_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector`, and `problem7_10e_abs_transpose_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector` identify the corresponding Mathlib Banach-algebra `spectralRadius` values after deriving strict vector positivity from source-shaped irreducibility and a supplied nonzero nonnegative eigenpair; `ch7TwoSidedScaledInfCondSet_sInf_nonneg`, `ch7TwoSidedScale_isInverse`, and `ch7TwoSidedScaledInfKappa_eq_kappaInf_of_inverse` prove that the infinity-product value-set infimum is nonnegative, that the inverse-scaled partner is a genuine inverse of `D₁AD₂`, and that `ch7TwoSidedScaledInfKappa` is the repository `kappaInf` value; `ch7TwoSidedScaledInfKappa_eq_abs_scaledInfCond`, `ch7TwoSidedScaledInfKappaSet_sInf_nonneg`, `problem7_10b_scaled_infKappa_ge_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_canonical_scaled_infKappa_eq_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_scaledInfKappaSet_sInf_eq_perron_of_abs_inverse_positive_eigenvector`, and `problem7_10b_scaledInfKappaSet_isLeast_perron_of_abs_inverse_positive_eigenvector` prove the source `|A|`, `|A⁻¹|` reduction, scaled-`κ∞` nonnegative infimum, canonical scaling, exact `sInf = ρ`, and least-value statement under the same certificate; `ch7_bauer_Cx_eigenvector_CB` proves that `Cx` is a right eigenvector of `CB` whenever `x` is a right eigenvector of `BC`, `ch7_perronScalar_pos_of_nonneg_irreducible_eigenvector` derives the positive-eigenvalue side condition from irreducible nonnegative `BC`, and `problem7_10d_Cx_pos_of_irreducible_BC_CB` plus `problem7_10d_abs_inverse_Cx_pos_of_irreducible_products` prove the source irreducible-product `Cx > 0` transfer and its `|A|`, `|A⁻¹|` specialization; `ch7_bauer_positive_products_irreducible` and `problem7_10b_positive_abs_entries_products_irreducible` prove that positive-entry hypotheses imply the two product irreducibility side conditions; `ch7TwoSidedScaledOneCond_eq_transpose_infCond`, `problem7_10e_scaled_oneCond_ge_perron_of_transpose_positive_eigenvector`, `problem7_10e_canonical_scaled_oneCond_eq_perron_of_transpose_positive_eigenvector`, `ch7TwoSidedScaledOneKappa_eq_abs_scaledOneCond`, `ch7TwoSidedScaledOneKappaSet_sInf_nonneg`, `problem7_10e_scaled_oneKappa_ge_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_canonical_scaled_oneKappa_eq_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_scaledOneKappaSet_sInf_eq_perron_of_abs_inverse_transpose_positive_eigenvector`, and `problem7_10e_scaledOneKappaSet_isLeast_perron_of_abs_inverse_transpose_positive_eigenvector` prove the source one-norm transpose reduction, scaled-`κ₁` nonnegative infimum, exact `sInf = ρ`, and least-value statement under the matching explicit certificate; `ch7_matrix_of_matTranspose`, `ch7_irreducible_matTranspose`, `ch7_irreducible_transpose_product_of_irreducible_product`, `problem7_10e_irreducible_products_canonical_scaled_oneCond_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_products_canonical_scaled_oneKappa_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_products_scaledOneKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector`, and `problem7_10e_irreducible_products_scaledOneKappaSet_isLeast_perron_of_nonzero_nonneg_eigenvector` derive the needed one-norm transpose-product irreducibility from the original source products `BC` and `CB`; `problem7_10e_complexMatrixOp2_realRectToCMatrix_le_sqrt_one_mul_inf`, `problem7_10e_scaled_op2Kappa_le_sqrt_oneKappa_mul_infKappa`, and `problem7_10e_scaled_op2Kappa_le_of_one_inf_bounds` prove the source 2-norm interpolation step for any fixed scaling with matching one- and infinity-product bounds, while `ch7TwoSidedScaledOp2Kappa_mem_set`, `ch7TwoSidedScaledOp2KappaSet_bddBelow`, `ch7TwoSidedScaledOp2KappaSet_sInf_nonneg`, and `problem7_10e_twoSidedScaledOp2Kappa_sInf_le_of_one_inf_bounds` package that fixed-scaling result into an `sInf` upper bound from a supplied admissible common scaling; full Theorem 7.8 still needs Perron-Frobenius existence of the required eigenvector/eigenvalue from irreducibility and proof that the compatible common scaling exists at the source spectral-radius value |
| Lemma 7.9, practical error bound | `CLOSED` for the infinity-norm practical bound and equality case | `lemma7_9_componentwise_bound`, `lemma7_9_relative_infNorm_bound`, `lemma7_9_exact_for_residual_multiple` |

## Numbered Equation Ledger

| Equation | Classification | Lean entry points or decision |
| --- | --- | --- |
| (7.1) | `CLOSED` | `theorem7_1_subordinate_sufficient`, `theorem7_1_subordinate` |
| (7.2) | `CLOSED` | `theorem7_1_subordinate_necessary`, `theorem7_1_subordinate` |
| (7.3) | `CLOSED` | `eq_7_3_subordinate_attaining_perturbations` |
| (7.4) | `CLOSED` | `normwise_forward_error_exact`, `normwise_forward_error_exact_relative_infNorm`, `theorem7_2_subordinate_forward_error_bound` |
| (7.5) | `CLOSED` | `Ch7NormwiseCondEFRadiusSet`, `ch7NormwiseCondEFRadiusSup`, `IsCh7NormwiseCondEFRadiusLimitValue`, `IsCh7NormwiseCondEFValue`, `eq_7_5_subordinate_conditionNumberRadiusLimitValue_of_positive_radii`, `eq_7_5_subordinate_conditionNumber_of_positive_radii` |
| (7.6) | `SKIP` | MATLAB/numerical illustration |
| (7.7) | `CLOSED` | `oettli_prager` feasibility surface |
| (7.8) | `CLOSED` | `oettli_prager` |
| (7.9) | `CLOSED` | `oettli_prager_sufficient` construction |
| (7.10) | `CLOSED` | `componentwise_forward_error_exact_relative_infNorm`, `theorem7_4_absolute_forward_error_bound` |
| (7.11) | `CLOSED` for infinity norm | `ch7CondEFAtSolutionInf` |
| (7.12) | `CLOSED` for the Skeel infinity-norm specialization | `ch7CondEFGlobalInf`, `ch7SkeelGlobalCondInf`, `ch7SkeelCondAtSolutionInf_le_condSkeel`, `eq_7_12_skeel_global_conditionNumber_eq_condSkeel`; the fixed-`f` diagnostic `exists_ch7CondEFAtSolutionInf_gt_of_positive_fixed_rhs_term` remains documented to avoid the false unbounded model |
| (7.13) | `CLOSED` for infinity norm | `ch7SkeelCondAtSolutionInf` |
| (7.14) | `CLOSED` for infinity norm | `condSkeel`, `ch7SkeelCondAtOnes_eq_condSkeel`, `condSkeel_le_kappaInf` |
| Prose after (7.14), factor-2 comparison with `f = |b| = |Ax|` | `CLOSED` for the infinity-norm source specialization | `ch7ComponentwiseDataCondAtSolutionInf`, `ch7SkeelCondAtSolutionInf_le_componentwiseDataCondAtSolutionInf`, `ch7ComponentwiseDataCondAtSolutionInf_le_two_mul_skeelCondAtSolutionInf` |
| (7.15) | `CLOSED` for positive row scalings as an infimum under right-invertibility | `ch7PositiveRowScaledKappaInfSet`, `ch7_condSkeel_le_kappaInf_rowScale`, `ch7RowEquilibratingScale`, `ch7RowsEquilibratedInf_rowEquilibratingScale_of_right_inverse`, `eq_7_15_positive_rowScaling_sInf_eq_condSkeel_of_right_inverse`; modeling note: Lean uses `sInf` over positive diagonal row scalings, which is the source-relevant row-equilibrating scaling class |
| (7.16) | `CLOSED` for a positive row-equilibrating diagonal scaling | `problem7_3_rowEquilibrated_lower_bound`, `eq_7_16_rowEquilibrated_bounds`, plus `condSkeel_le_kappaInf` for the upper inequality |
| (7.17) | `DEFER-LATER-CHAPTER` | Kahan symbolic example should follow the scaling block |
| (7.18) | `PROVE-NOW-SPLIT2`; `CLOSED` for the finite-real `p` and `p = 2` pairwise/`sInf` column-scaling explicit-`Aplus` specializations, conditional finite-real and `p = 2` source-`min` adapters from supplied `IsLeast` certificates, finite-real `p` right-value-set lower-bound infrastructure, the `p = 2` right value-set global-rescaling, absolute-sum-one normalized-witness, normalized-slice equality, normalized `IsLeast` transfer, and normalized conditional source-`min` dependencies, the `p = 1` pairwise/`sInf`/least-element explicit-`Aplus` specialization, the explicit-left-inverse rank side-condition wrappers, the injective rank-form existential wrappers, the real Matrix-rank source wrappers for `rank(A)=n`, and the Penrose1/normal-equations-plus-matrix-rank explicit-`Aplus` endpoint, `sInf`, conditional-`min`, and normalized conditional-`min` wrappers | `ch7LpRightScaledCondSetOfReal_bddBelow`, `ch7LpRightScaledCondSetOfReal_sInf_nonneg`, `ch7Op2RightScaledCondNormalizedSet`, `ch7_sum_abs_pos_of_reciprocal`, `ch7Op2RightScaledCond_global_scale`, `ch7Op2RightScaledCond_mem_set_global_scale`, `ch7Op2RightScaledCond_sum_abs_normalized_witness`, `ch7Op2RightScaledCondSet_eq_sum_abs_normalized`, `ch7Op2RightScaledCondSet_isLeast_iff_sum_abs_normalized`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_normalized`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_rect_left_inverse_of_normalized`, `theorem7_5_lp_column_equilibration_le_card_rpow_right_scaling`, `theorem7_5_lp_column_equilibration_le_card_rpow_sInf_right_scalings`, `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings`, `theorem7_5_lp_column_equilibration_le_card_rpow_sInf_right_scalings_of_rect_left_inverse`, `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings_of_rect_left_inverse`, `theorem7_5_lp_column_equilibration_exists_left_inverse_of_rectMatMulVec_injective`, `theorem7_5_lp_column_equilibration_exists_left_inverse_of_matrix_rank_eq_width`, `theorem7_5_lp_column_equilibration_le_card_rpow_sInf_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_p1_column_equilibration_le_right_scaling`, `theorem7_5_p1_column_equilibration_sInf_eq_right_scalings`, `theorem7_5_p1_column_equilibration_isLeast_right_scalings`, `theorem7_5_p1_column_equilibration_isLeast_right_scalings_of_rect_left_inverse`, `theorem7_5_p1_column_equilibration_isLeast_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_p1_column_equilibration_exists_left_inverse_of_rectMatMulVec_injective`, `theorem7_5_p1_column_equilibration_exists_left_inverse_of_matrix_rank_eq_width`, `theorem7_5_p2_column_equilibration_le_sqrt_card_right_scaling`, `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings`, `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings_of_rect_left_inverse`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_rect_left_inverse`, `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_p2_column_equilibration_exists_left_inverse_of_rectMatMulVec_injective`, `theorem7_5_p2_column_equilibration_exists_left_inverse_of_matrix_rank_eq_width`, and `theorem7_5_p2_column_equilibration_exists_penrose_min_normalized_imp_of_matrix_rank_eq_width`; full source `min` statement still depends on proof of general/non-endpoint minimizer existence |
| (7.19) | `PROVE-NOW-SPLIT2`; `CLOSED` for the conjugate-row finite-real `p` pairwise and `sInf` proof-route specialization, conditional finite-real and `p = 2` source-`min` adapters from supplied `IsLeast` certificates, finite-real `p` left-value-set lower-bound infrastructure, the `p = 2` pairwise and `sInf` row-scaling condition-product explicit-`Aplus` specialization, the `p = 2` left value-set global-rescaling, absolute-sum-one normalized-witness, normalized-slice equality, normalized `IsLeast` transfer, and normalized conditional source-`min` dependencies, the `p = ∞` pairwise/`sInf`/least-element row-scaling explicit-`Aplus` specialization, the explicit-right-inverse rank side-condition wrappers, the surjective rank-form existential wrappers, the real Matrix-rank source wrappers for `rank(A)=m`, and the Penrose1/normal-equations-plus-matrix-rank row-side `sInf`, conditional-`min`, endpoint least-element, and normalized conditional-`min` wrappers | `eq_7_19_matrixLpNormOfReal_dual_row_equilibrated`, `eq_7_19_matrixLpNormOfReal_dual_row_inverseSide_bound`, `ch7LpLeftScaledCondSetOfReal_bddBelow`, `ch7LpLeftScaledCondSetOfReal_sInf_nonneg`, `ch7Op2LeftScaledCondNormalizedSet`, `ch7Op2LeftScaledCond_global_scale`, `ch7Op2LeftScaledCond_mem_set_global_scale`, `ch7Op2LeftScaledCond_sum_abs_normalized_witness`, `ch7Op2LeftScaledCondSet_eq_sum_abs_normalized`, `ch7Op2LeftScaledCondSet_isLeast_iff_sum_abs_normalized`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_normalized`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_rect_right_inverse_of_normalized`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_left_scaling`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings_of_rect_right_inverse`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings_of_rect_right_inverse`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings_of_penrose1_matrix_rank_eq_height`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings_of_penrose1_matrix_rank_eq_height`, `theorem7_5_lp_dual_row_equilibration_exists_right_inverse_of_rectMatMulVec_surjective`, `theorem7_5_lp_dual_row_equilibration_exists_right_inverse_of_matrix_rank_eq_height`, `ch7Op2LeftScaledCondSet_sInf_nonneg`, `theorem7_5_p2_row_equilibration_le_sqrt_card_left_scaling`, `theorem7_5_p2_row_equilibration_le_sqrt_card_sInf_left_scalings`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings`, `theorem7_5_p2_row_equilibration_le_sqrt_card_sInf_left_scalings_of_rect_right_inverse`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_rect_right_inverse`, `theorem7_5_p2_row_equilibration_le_sqrt_card_sInf_left_scalings_of_penrose1_matrix_rank_eq_height`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_penrose1_matrix_rank_eq_height`, `theorem7_5_p2_row_equilibration_exists_right_inverse_of_rectMatMulVec_surjective`, `theorem7_5_p2_row_equilibration_exists_right_inverse_of_matrix_rank_eq_height`, `theorem7_5_p2_row_equilibration_exists_penrose_min_normalized_imp_of_matrix_rank_eq_height`, `theorem7_5_pinf_row_equilibration_le_left_scaling`, `theorem7_5_pinf_row_equilibration_sInf_eq_left_scalings`, `theorem7_5_pinf_row_equilibration_isLeast_left_scalings`, `theorem7_5_pinf_row_equilibration_isLeast_left_scalings_of_rect_right_inverse`, `theorem7_5_pinf_row_equilibration_isLeast_left_scalings_of_penrose1_matrix_rank_eq_height`, `theorem7_5_pinf_row_equilibration_exists_right_inverse_of_rectMatMulVec_surjective`, and `theorem7_5_pinf_row_equilibration_exists_right_inverse_of_matrix_rank_eq_height`; full source statement still depends on proof of general/non-endpoint minimizer existence for the conjugate-row proof route from `(6.21)` |
| (7.20) | `CLOSED` for finite-real `p` and for the `p = 2` operator-certificate/Frobenius dependency | `eq_7_20_column_lpNorm_le_matrixLpNormOfReal`, `ch7_complexVecLpNorm_realRect_matVec_le_sum_column_lpNorm`, `eq_7_20_matrixLpNormOfReal_le_card_rpow_mul_column_bound`, `eq_7_20_column_norm_le_of_rectOpNorm2Le`, `ch7RectColumnNorm2_le_frobNormRect`, `ch7_frobNormRect_le_sqrt_card_mul_column_bound`, and `eq_7_20_rectOpNorm2Le_of_column_bound` |
| (7.21) | `CLOSED` for finite-real `p`, the `p = 2` operator-certificate/Frobenius dependency, and the `p = 1` 1-norm column-equilibration specialization | `eq_7_21_matrixLpNormOfReal_column_equilibrated`, `eq_7_21_rectOpNorm2Le_column_equilibrated`, and `eq_7_21_oneNormRect_column_equilibrated` |
| (7.22) | `PROVE-NOW-SPLIT2`; `CLOSED` for the finite-real `p`, `p = 1`, and `p = 2` inverse-side inequalities with explicit inverse-side matrix | `eq_7_22_matrixLpNormOfReal_inverseSide_bound`, `eq_7_22_oneNormRect_inverseSide_bound`, and `eq_7_22_op2_inverseSide_bound`; full source theorem still needs the Moore-Penrose construction/projection wrapper and general minimizer-existence package |
| (7.23) | `CLOSED` in the repository's explicit inverse-Gram and `sInf` model; no minimizer-attainment theorem is asserted | `corollary7_6_cholesky_factor_column_scaling_le_sqrt_card_sInf_right_scalings` instantiates the p=2 Theorem 7.5 `sInf` wrapper for a factor `R` with `A = RᵀR` on diagonal entries and source scale `D* = diag(a_jj^{-1/2})`; `ch7SymmetricOp2ScaledCondSet_sInf_nonneg` records the nonnegative infimum for the symmetric two-sided value set, `corollary7_6_cholesky_inverse_gram_isInverse` and `corollary7_6_cholesky_scaled_inverse_gram_isInverse` prove the inverse-side witness, `corollary7_6_cholesky_scaled_cond_eq_factor_cond_sq` proves the explicit operator-2 product-square bridge, `corollary7_6_cholesky_scaled_cond_le_card_sInf_right_scalings_sq` proves the resulting `n * (sInf factor-values)^2` bound, and `corollary7_6_cholesky_right_sInf_sq_le_symmetric_sInf` transfers the factor infimum square to the two-sided SPD scaling infimum. The final source-facing theorem `corollary7_6_cholesky_scaled_cond_le_card_sInf_symmetric_scalings` proves `κ₂(D*AD*) <= n * sInf {κ₂(DAD)}` over reciprocal diagonal two-sided scalings |
| (7.24) | `PROVE-NOW-SPLIT2`; `CLOSED` for the positive-Perron-certificate algebraic core, the scaled-inverse `kappaInf` transport, the `B = |A|`, `C = |A⁻¹|` absolute-value instantiation, positive-entry product irreducibility, certificate-level `sInf = ρ` equalities and `IsLeast` minimum-attainment wrappers for the infinity-norm Bauer product, scaled `κ∞`, and scaled `κ₁` transpose branch, the local finite eigenvalue-radius/greatest-value/`sSup`, generic Split 1 maximum-modulus/norm-existence, Mathlib spectrum-modulus `sSup`, and Mathlib `spectralRadius` wrappers for both the unscaled and positive-reciprocally scaled Bauer products including source-shaped irreducible/nonzero-nonnegative eigenpair surfaces, the `CB(Cx)` eigenvector algebra, the source-shaped irreducible-product `Cx > 0` transfer under a supplied positive eigenvector certificate, the one-norm transpose-certificate analogue and original-product irreducibility bridge, the fixed-scaling 2-norm interpolation step, one-/infinity-/op-2 value-set lower-bound infrastructure, and the conditional `sInf` upper-bound packaging | `problem7_10a_positive_entries_canonical_scaled_infCond_eq_perron` proves the equality for positive-entry `B,C` once `BCx = ρx` with `x > 0` is supplied, `problem7_10a_positive_entries_scaledInfCondSet_sInf_eq_perron` proves the exact `sInf = ρ` value-set form, and `problem7_10a_positive_entries_scaledInfCondSet_isLeast_perron` proves the corresponding least-value statement; `problem7_10a_scaled_product_isComplexEigenvalueRadius_of_positive_eigenvector`, `problem7_10a_scaled_product_complexEigenvalueModulusSet_isGreatest_of_positive_eigenvector`, and `problem7_10a_scaled_product_complexEigenvalueModulusSet_sSup_eq_of_positive_eigenvector` prove the local finite eigenvalue-radius, greatest-value, and exact `sSup = ρ` statements for every positive reciprocal two-sided scaling of the Bauer product under the same certificate, while `ch7_isMaxComplexMatrixEigenvalueModulus_of_isComplexEigenvalueRadius`, `ch7_exists_mixedSubordinateMatrixNormValue_le_of_isComplexEigenvalueRadius`, `complexMatrixEigenvalueModulusSet_eq_toLin_spectrum_modulusSet`, and the Problem 7.10 product/absolute/scaled Mathlib-spectrum wrappers export the same certificate to integrated Split 1 norm APIs and to `spectrum (Matrix.toLin' ...)` modulus `sSup = ρ`; `problem7_10a_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector`, `problem7_10b_abs_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector`, `problem7_10a_scaled_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector`, and `problem7_10e_abs_transpose_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector` close the corresponding Mathlib `spectralRadius` theorem surfaces after deriving strict positivity from irreducibility plus a supplied nonzero nonnegative eigenpair; `ch7TwoSidedScaledInfCondSet_sInf_nonneg` proves the corresponding Bauer product value-set infimum is nonnegative; `ch7_bauer_Cx_eigenvector_CB` proves the source part (c) algebra that `Cx` is a right eigenvector of `CB`, while `ch7_perronScalar_pos_of_nonneg_irreducible_eigenvector`, `problem7_10d_Cx_pos_of_irreducible_BC_CB`, and `problem7_10d_abs_inverse_Cx_pos_of_irreducible_products` prove the source part (d) positivity-transfer step for `Cx` under irreducible `BC` and `CB`, nonnegative factors, and the same supplied `BCx = ρx`, `x > 0` certificate; `ch7TwoSidedScaledInfKappa_eq_kappaInf_of_inverse` proves that the scaled `κ∞` product is the repository `kappaInf` of the two-sided scaled matrix under an inverse certificate, and `ch7TwoSidedScaledInfKappaSet_sInf_nonneg` proves this scaled-`κ∞` value-set infimum is nonnegative; `problem7_10b_positive_abs_entries_canonical_scaled_infKappa_eq_perron` proves the corresponding scaled `κ∞` statement for `|A|`, `|A⁻¹|`, `problem7_10b_positive_abs_entries_scaledInfKappaSet_sInf_eq_perron` proves the exact scaled-`κ∞` `sInf = ρ` value-set form, and `problem7_10b_positive_abs_entries_scaledInfKappaSet_isLeast_perron` proves the least-value statement; `problem7_10b_positive_abs_entries_products_irreducible` proves that positive `|A|` and `|A⁻¹|` imply irreducibility of both `|A||A⁻¹|` and `|A⁻¹||A|`; `problem7_10e_positive_entries_canonical_scaled_oneCond_eq_perron_of_transpose` and `problem7_10e_positive_abs_entries_canonical_scaled_oneKappa_eq_perron_of_transpose` prove the 1-norm transpose analogue under the explicit transpose-side Perron-vector certificate, `ch7TwoSidedScaledOneKappaSet_sInf_nonneg` proves the scaled-`κ₁` value-set infimum is nonnegative, `problem7_10e_positive_abs_entries_scaledOneKappaSet_sInf_eq_perron_of_transpose` proves the exact scaled-`κ₁` `sInf = ρ` value-set form, and `problem7_10e_positive_abs_entries_scaledOneKappaSet_isLeast_perron_of_transpose` proves the least-value statement; `ch7_matrix_of_matTranspose`, `ch7_irreducible_matTranspose`, `ch7_irreducible_transpose_product_of_irreducible_product`, `problem7_10e_irreducible_products_canonical_scaled_oneCond_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_products_canonical_scaled_oneKappa_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_products_scaledOneKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector`, and `problem7_10e_irreducible_products_scaledOneKappaSet_isLeast_perron_of_nonzero_nonneg_eigenvector` transport source-product irreducibility for `BC` and `CB` to the transpose products required by the one-norm reduction; `problem7_10e_complexMatrixOp2_realRectToCMatrix_le_sqrt_one_mul_inf`, `ch7TwoSidedScaledOp2Kappa`, `problem7_10e_scaled_op2Kappa_le_sqrt_oneKappa_mul_infKappa`, `problem7_10e_scaled_op2Kappa_le_of_one_inf_bounds`, `ch7TwoSidedScaledOp2Kappa_mem_set`, `ch7TwoSidedScaledOp2KappaSet_bddBelow`, `ch7TwoSidedScaledOp2KappaSet_sInf_nonneg`, and `problem7_10e_twoSidedScaledOp2Kappa_sInf_le_of_one_inf_bounds` prove the source 2-norm interpolation and `sInf` upper-bound packaging for any supplied common scaling with matching one- and infinity-product bounds; the full source row still depends on Perron-Frobenius eigenvector/eigenvalue existence and proof that the compatible common scaling exists at the source spectral-radius value |
| (7.25) | `CLOSED` for the componentwise source-radius `sSup` model | Linearized finite-max core closed by `problem7_11_linearized_inverse_componentwise_formula`; exact inverse perturbation algebraic bridge closed by `problem7_11_exact_inverse_firstOrder_remainder_identity`; exact componentwise quadratic-remainder bound, finite max upper/lower envelopes, finite lower-witness perturbation, finite-radius reduction, conditional `εR → 0` dependency, exact-to-linearized quotient convergence, entrywise-/infinity-norm inverse-bound discharges, and constructed local inverse-family bridge closed by the `ch7InverseQuadraticRemainder*`, `problem7_11_exact_inverse_relative_change_max_*`, `ch7MatAddId`, `ch7Problem711PerturbedInverseCandidate`, and `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_componentwise_tendsto_zero` family; the source-radius feasible set and shrinking-radius supremum limit are closed by `Ch7InverseComponentwiseRadiusSet`, `ch7InverseComponentwiseRadiusSup`, `IsCh7InverseComponentwiseRadiusLimitValue`, `IsCh7InverseComponentwiseCondValue`, `ch7InverseComponentwiseRadiusSet_value_le`, `exists_ch7InverseComponentwiseRadiusSet_lower_witness`, `problem7_11_inverse_componentwise_radiusSup_tendsto_linearized`, and `problem7_11_inverse_componentwise_condition_of_positive_radii` |
| (7.26) | `CLOSED` | `eq_7_26_relative_distance_to_singularity_eq_inv_condition_number` |
| (7.27) | `CLOSED` for repository backward-error surfaces | `rigal_gaches`, `oettli_prager` |
| (7.28) | `CLOSED` for infinity norm | `ch7ForwardBoundEF`, `ch7CondEFAtSolutionInf` |
| (7.29) | `CLOSED` for infinity norm | `lemma7_9_relative_infNorm_bound` |
| (7.30) | `CLOSED` | `eq_7_30_conventional_residual_error` |
| (7.31) | `CLOSED` | `ch7ComputedResidualSafetyTerm`, `ch7ComputedResidualImage`, `eq_7_31_componentwise_bound`, `eq_7_31_relative_infNorm_bound` |
| (7.32) | `DEFER-LATER-CHAPTER` | Calculus perturbation estimate should follow the generic norm/asymptotic interface |
| (7.33) | `CLOSED` | `IsStochasticMatrix`, `stochasticMatrix_mul_ones` |

## Problem Inventory

The Split 2 contract ledger lists Problems 7.1-7.6 and 7.10-7.14. The skill
policy also requires reading and classifying the remaining Chapter 7 problems
and the Appendix A solutions; therefore Problems 7.7-7.9 and 7.15 are listed
explicitly below.

| Problem | Classification | Lean entry points or decision |
| --- | --- | --- |
| 7.1 | `CLOSED` for the scalar Neumann contraction form and the exact matrix-valued resolvent form under the local row-sum contraction hypothesis | `ch7Problem71ContractionMatrix`, `problem7_1_componentwise_contraction_ineq`, `problem7_1_componentwise_neumann_scalar_bound`, `ch7NonnegativeResolvent`, `problem7_1_resolvent_componentwise_inequality_bound`, `ch7NonnegativeResolvent_nonsingInv_of_infNormBound`, `problem7_1_componentwise_resolvent_bound`, `problem7_1_componentwise_nonsingInv_resolvent_bound` |
| 7.2 | `CLOSED` | `problem7_2_infNorm_residual_lower`, `problem7_2_infNorm_residual_upper`, `problem7_2_infNorm_scaled_lower`, `problem7_2_infNorm_scaled_upper`, `problem7_2_subordinate_residual_lower`, `problem7_2_subordinate_residual_upper`, `problem7_2_subordinate_scaled_lower`, `problem7_2_subordinate_scaled_upper` |
| 7.3 | `CLOSED` for the positive-row-scaling/infinity-norm formulation | Appendix A.3 row-equilibrated equality, the positive-row-scaling `(7.15)` infimum, and `(7.16)` inequalities are closed by `problem7_3_rowEquilibrated_scaling_condition_eq`, `eq_7_15_positive_rowScaling_sInf_eq_condSkeel_of_right_inverse`, and `eq_7_16_rowEquilibrated_bounds` |
| 7.4 | `CLOSED` for the unit-diagonal symmetric PSD scaled-factor form | `problem7_4_abs_entry_le_one_of_finitePSD_diag_one`, `problem7_4_unitDiagonal_entryBound_condition_bounds`, and `problem7_4_unitDiagonal_finitePSD_condition_bounds`; positivity on `e_i ± e_j` derives `|H_ij| ≤ 1`, then finite row-sum comparisons prove `cond(H) ≤ κ∞(H) ≤ n cond(H)` |
| 7.5 | `PROVE-NOW-SPLIT2` | Depends on source-facing SVD/projection/pseudoinverse wrappers over integrated rank/SVD foundations |
| 7.6(a), row-wise condition-number comparison | `CLOSED` for the infinity-norm source specialization | `ch7RowwiseRelativeToleranceMatrix`, `ch7RowwiseDataCondAtSolutionInf`, `ch7_rowwiseDataForwardBound_lower`, `ch7_rowwiseDataForwardBound_upper`, `problem7_6a_rowwise_data_condition_bounds` |
| 7.6(b), columnwise condition-number comparison | `CLOSED` for the infinity-norm source specialization | `ch7ColumnwiseRelativeToleranceMatrix`, `ch7AbsMatrixAbsVecOneNorm`, `ch7ColumnwiseDataCondAtSolutionInf`, `ch7_columnwiseDataForwardBound_lower`, `ch7_columnwiseDataForwardBound_upper`, `problem7_6b_columnwise_data_condition_bounds` |
| 7.7 | `CLOSED` | `problem7_7_subordinate_abs_rhs_feasible_of_zero_rhs_feasible`, `problem7_7_subordinate_abs_rhs_to_zero_rhs_residual_bound`, `problem7_7_subordinate_zero_rhs_feasible_of_abs_rhs_feasible`, `problem7_7_componentwise_abs_rhs_to_zero_rhs_residual_bound`, `problem7_7_componentwise_zero_rhs_feasible_of_abs_rhs_feasible`, `problem7_7_normwise_inf_residual_bound`, `problem7_7_normwise_zero_rhs_feasible_of_abs_rhs_feasible` |
| 7.8 | `CLOSED` | `ch7Problem78Feasible`, `ch7Problem78AugMatrix`, `ch7Problem78AugVector`, `problem7_8_frobenius_lower_bound_pos`, `problem7_8_rankOne_attains_pos`, `problem7_8_frobenius_characterization_pos`, `problem7_8_zero_parameter_attains`, `problem7_8_source_value_eq_augmented_value` |
| 7.9, finite first-order componentwise scalar-output formula, `χ ≥ 1` lower-bound specializations, finite first-order normwise formula, and first-order radius-sup packages | `CLOSED` under nonnegative tolerances, nonzero `c^T x`, a left-inverse certificate for the lower-bound rows, and nonzero `x`/adjoint-weight vector for the normwise attaining witness | `ch7LinearFunctional`, `ch7Problem79AdjointWeight`, `ch7Problem79FirstOrderChange`, `ch7Problem79ComponentwiseSensitivity`, `ch7Problem79LinearizedCond`, `ch7Problem79LinearizedRelativeChange`, `ch7Problem79AttainingDeltaA`, `ch7Problem79AttainingDeltaB`, `problem7_9_linearized_componentwise_functional_formula`, `ch7Problem79_adjointWeight_mul_vec_eq_linearFunctional_matMulVec`, `ch7Problem79_linearFunctional_eq_adjointWeight_mul_Ax`, `ch7Problem79ComponentwiseSensitivity_ge_abs_functional_of_abs_matrix`, `ch7Problem79ComponentwiseSensitivity_ge_abs_functional_of_abs_rhs`, `problem7_9_linearized_componentwise_functional_ge_one_of_abs_matrix`, `problem7_9_linearized_componentwise_functional_ge_one_of_abs_rhs`, `ch7Problem79NormwiseSensitivity`, `ch7Problem79NormwiseLinearizedCond`, `ch7Problem79_normwise_firstOrder_abs_le`, `ch7Problem79_normwiseLinearizedRelativeChange_le`, `ch7Problem79NormwiseAttainingDeltaA`, `ch7Problem79NormwiseAttainingDeltaB`, `problem7_9_linearized_normwise_functional_formula`, `problem7_9_componentwise_linearized_radiusSup_tendsto_formula`, `problem7_9_normwise_linearized_radiusSup_tendsto_formula` |
| 7.9, nonlinear source-radius wrapper for componentwise `χ` | `CLOSED` for the exact perturbed-solution `sSup` model under nonnegative `E,f`, nonzero `c^T x`, `0 < n`, and a left-inverse certificate for `A` | `ch7Problem79PerturbedSolutionWithInverse`, `ch7Problem79ExactScalarRelativeChange`, `ch7Problem79ComponentwiseExactRemainderBound`, `problem7_9_exact_componentwise_relative_change_le_linearized_plus_quadratic`, `problem7_9_exact_componentwise_relative_change_ge_linearized_minus_quadratic`, `Ch7Problem79ComponentwiseExactRadiusSet`, `ch7Problem79ComponentwiseExactRadiusSup`, `ch7Problem79ComponentwiseExactRadiusSet_value_le`, `exists_ch7Problem79ComponentwiseExactRadiusSet_lower_witness`, `problem7_9_componentwise_exact_radiusSup_tendsto_linearized`, `problem7_9_componentwise_exact_condition_of_positive_radii` |
| 7.9, nonlinear source-radius wrapper for normwise `ψ` | `CLOSED` for the exact perturbed-solution `sSup` model under nonnegative `‖E‖₂, ‖f‖₂`, nonzero `c^T x`, nonzero `x`/adjoint-weight vector for the lower witness, `0 < n`, and a left-inverse certificate for `A` | `ch7Problem79NormwiseConstantEnvelopeMatrix`, `ch7Problem79_normwise_deltaA_componentwise_bound`, `ch7Problem79_normwise_deltaB_componentwise_bound`, `ch7Problem79NormwiseExactRemainderBound`, `problem7_9_exact_normwise_relative_change_le_linearized_plus_quadratic`, `problem7_9_exact_normwise_relative_change_ge_linearized_minus_quadratic`, `Ch7Problem79NormwiseExactRadiusSet`, `ch7Problem79NormwiseExactRadiusSup`, `ch7Problem79NormwiseExactRadiusSet_value_le`, `exists_ch7Problem79NormwiseExactRadiusSet_lower_witness`, `problem7_9_normwise_exact_radiusSup_tendsto_linearized`, `problem7_9_normwise_exact_condition_of_positive_radii` |
| 7.10 | `PROVE-NOW-SPLIT2`; `CLOSED` for part (a)'s algebraic lower-bound/attainment core, nonnegative infinity-product infimum, and exact `sInf = ρ` value-set wrapper, the scaled-inverse `kappaInf` transport, part (b)'s absolute-value scaled-`κ∞` instantiation, nonnegative scaled-`κ∞` infimum, and exact `sInf = ρ` value-set wrapper under a positive Perron-vector certificate, part (c)'s `CB(Cx)` eigenvector algebra, part (d)'s source-shaped irreducible-product `Cx > 0` transfer under a supplied positive eigenvector certificate, the positive-entry-to-irreducibility side condition used by part (d), part (e)'s one-norm transpose-certificate branch plus original-product irreducibility bridge, nonnegative scaled-`κ₁` infimum, and exact scaled-`κ₁` `sInf = ρ` value-set wrapper, part (e)'s fixed-scaling 2-norm interpolation step, part (e)'s op-2 value-set lower-bound infrastructure, and part (e)'s conditional `sInf` upper-bound packaging | `ch7TwoSidedScale`, `ch7TwoSidedScaledInfCond`, `ch7TwoSidedScaledInfCondSet`, `ch7TwoSidedScaledInfCond_mem_set`, `ch7TwoSidedScaledInfCondSet_nonempty`, `ch7TwoSidedScaledInfCondSet_bddBelow`, `ch7TwoSidedScaledInfCondSet_sInf_nonneg`, `ch7_infNorm_ge_of_nonneg_right_eigenvector`, `problem7_10a_scaled_infCond_ge_perron_of_positive_eigenvector`, `ch7_bauer_Cx_eigenvector_CB`, `ch7_matrix_mulVec_eq_matMulVec`, `ch7_matrix_pow_mulVec_eigen`, `ch7_perronScalar_pos_of_nonneg_irreducible_eigenvector`, `ch7_nonneg_irreducible_right_eigenvector_pos`, `problem7_10d_Cx_pos_of_irreducible_CB`, `problem7_10d_Cx_pos_of_irreducible_BC_CB`, `ch7_matrix_isPrimitive_of_pos_entries`, `ch7_matrix_isIrreducible_of_pos_entries`, `ch7_matMul_pos_of_pos`, `ch7_bauer_positive_products_irreducible`, `problem7_10a_canonical_scaled_infCond_eq_perron_of_positive_eigenvector`, `problem7_10a_positive_entries_canonical_scaled_infCond_eq_perron`, `problem7_10a_scaledInfCondSet_sInf_eq_perron_of_positive_eigenvector`, `problem7_10a_positive_entries_scaledInfCondSet_sInf_eq_perron`, `ch7TwoSidedScale_isLeftInverse`, `ch7TwoSidedScale_isRightInverse`, `ch7TwoSidedScale_isInverse`, `ch7TwoSidedScaledInfKappa`, `ch7TwoSidedScaledInfKappaSet`, `ch7TwoSidedScaledInfKappa_mem_set`, `ch7TwoSidedScaledInfKappaSet_nonempty`, `ch7TwoSidedScaledInfKappaSet_bddBelow`, `ch7TwoSidedScaledInfKappaSet_sInf_nonneg`, `ch7TwoSidedScaledInfKappa_eq_kappaInf_of_inverse`, `ch7TwoSidedScaledInfKappa_eq_abs_scaledInfCond`, `problem7_10b_scaled_infKappa_ge_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_canonical_scaled_infKappa_eq_perron_of_abs_inverse_positive_eigenvector`, `problem7_10d_abs_inverse_Cx_pos_of_irreducible_products`, `problem7_10b_positive_abs_entries_canonical_scaled_infKappa_eq_perron`, `problem7_10b_scaledInfKappaSet_sInf_eq_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_positive_abs_entries_scaledInfKappaSet_sInf_eq_perron`, `problem7_10b_positive_abs_entries_products_irreducible`, `ch7TwoSidedScaledOneCond_eq_transpose_infCond`, `problem7_10e_scaled_oneCond_ge_perron_of_transpose_positive_eigenvector`, `problem7_10e_canonical_scaled_oneCond_eq_perron_of_transpose_positive_eigenvector`, `problem7_10e_positive_entries_canonical_scaled_oneCond_eq_perron_of_transpose`, `ch7TwoSidedScaledOneKappa`, `ch7TwoSidedScaledOneKappaSet`, `ch7TwoSidedScaledOneKappa_mem_set`, `ch7TwoSidedScaledOneKappaSet_nonempty`, `ch7TwoSidedScaledOneKappaSet_bddBelow`, `ch7TwoSidedScaledOneKappaSet_sInf_nonneg`, `ch7TwoSidedScaledOneKappa_eq_abs_scaledOneCond`, `problem7_10e_scaled_oneKappa_ge_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_canonical_scaled_oneKappa_eq_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_positive_abs_entries_canonical_scaled_oneKappa_eq_perron_of_transpose`, `problem7_10e_scaledOneKappaSet_sInf_eq_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_positive_abs_entries_scaledOneKappaSet_sInf_eq_perron_of_transpose`, `ch7_matrix_of_matTranspose`, `ch7_irreducible_matTranspose`, `ch7_irreducible_transpose_product_of_irreducible_product`, `problem7_10e_irreducible_products_canonical_scaled_oneCond_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_products_canonical_scaled_oneKappa_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_products_scaledOneKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_complexMatrixOp2_realRectToCMatrix_le_sqrt_one_mul_inf`, `ch7TwoSidedScaledOp2Kappa`, `problem7_10e_scaled_op2Kappa_le_sqrt_oneKappa_mul_infKappa`, `problem7_10e_scaled_op2Kappa_le_of_one_inf_bounds`, `ch7TwoSidedScaledOp2Kappa_mem_set`, `ch7TwoSidedScaledOp2KappaSet_bddBelow`, `ch7TwoSidedScaledOp2KappaSet_sInf_nonneg`, and `problem7_10e_twoSidedScaledOp2Kappa_sInf_le_of_one_inf_bounds`; parts (c)-(d) still require spectral-radius/Perron-Frobenius source wrappers beyond the supplied positive eigenvector and irreducible-product positivity transfer, and part (e)'s full global `inf κ₂ <= ρ(|A||A⁻¹|)` bound still needs proof that the compatible Bauer scaling exists at the source spectral-radius value |
| 7.11, Appendix A.11 first-order inverse componentwise formula | `CLOSED` for the finite linearized max under nonnegative `E` and nonzero inverse entries | `ch7InverseLinearizedEntry`, `ch7InverseCompSensitivityEntry`, `ch7InverseCompSensitivityRatio`, `ch7InverseComponentwiseLinearizedCond`, `ch7InverseLinearizedRelativeChangeMax`, `ch7Problem711AttainingDelta`, `problem7_11_linearized_inverse_componentwise_upper_and_sign_attainment`, `problem7_11_linearized_inverse_componentwise_formula` |
| 7.11, exact inverse perturbation first-order/remainder identity | `CLOSED` under left/right inverse certificates | `ch7InverseQuadraticRemainderEntry`, `ch7_inversePerturbation_decomposition`, `problem7_11_exact_inverse_firstOrder_remainder_identity` |
| 7.11, exact quadratic-remainder relative upper/lower envelopes, finite lower witness, finite-radius reduction, conditional asymptotic vanishing, exact-to-linearized filter bridge, entrywise-/infinity-norm inverse-bound discharges, and constructed local inverse-family bridge | `CLOSED` for finite perturbations under left/right inverse certificates, nonnegative `E`, nonzero inverse entries, an explicit bounded-remainder radius premise, an eventual boundedness premise for the filter-level `εR → 0` dependency, exact quotient convergence under explicit eventual admissibility/right-inverse/bounded-remainder hypotheses, boundedness discharged from entrywise or infinity-norm bounds, and the same exact quotient convergence for the constructed perturbed inverse family under componentwise admissibility and `ε → 0` | `ch7InverseFirstProductSensitivity`, `ch7InverseQuadraticRemainderSensitivityEntry`, `ch7InverseExactRelativeChangeMax`, `ch7InverseQuadraticRemainderRelativeMax`, `ch7InverseQuadraticRemainderRelativeMax_nonneg`, `ch7InverseQuadraticRemainderRelativeMaxEntryBound`, `ch7InverseQuadraticRemainderRelativeMaxEntryBound_nonneg`, `ch7InverseQuadraticRemainderSensitivityEntry_le_of_entry_bound`, `ch7InverseQuadraticRemainderRelativeMax_le_of_entry_bound`, `ch7InverseQuadraticRemainderRelativeMax_abs_le_of_entry_bound`, `ch7_abs_entry_le_infNorm`, `ch7InverseQuadraticRemainderRelativeMax_le_of_infNorm_bound`, `ch7InverseQuadraticRemainderRelativeMax_abs_le_of_infNorm_bound`, `ch7MatAddId`, `ch7_isRightInverse_of_isLeftInverse`, `ch7_matAdd_id_abs_solution_bound_of_abs_infNorm_bound`, `ch7_matAdd_id_det_ne_zero_of_abs_infNorm_bound`, `ch7_nonsingInv_matAdd_id_entry_abs_le_of_abs_infNorm_bound`, `ch7_nonsingInv_matAdd_id_infNorm_le_of_abs_infNorm_bound`, `ch7Problem711PerturbedInverseCandidate`, `problem7_11_perturbed_inverse_candidate_right_inverse_of_abs_left_product_bound`, `problem7_11_perturbed_inverse_candidate_infNorm_bound_of_abs_left_product_bound`, `ch7_abs_left_product_infNorm_le_of_componentwise_bound`, `problem7_11_eventually_abs_left_product_infNormBound_half_of_componentwise_tendsto_zero`, `ch7InverseQuadraticRemainderEntry_abs_le`, `problem7_11_exact_inverse_relative_entry_le_linearized_plus_quadratic`, `problem7_11_exact_inverse_relative_entry_ge_linearized_minus_quadratic`, `problem7_11_exact_inverse_relative_change_max_ge_linearized_entry_minus_quadratic`, `problem7_11_exact_inverse_relative_change_max_le_condition_plus_quadratic`, `problem7_11_exact_inverse_relative_change_max_le_linearized_max_plus_quadratic`, `problem7_11_exact_inverse_relative_change_max_ge_linearized_max_minus_quadratic`, `problem7_11_exact_inverse_relative_change_max_le_condition_plus_radius_bound`, `problem7_11_exact_inverse_relative_change_max_ge_condition_minus_quadratic_of_linearized_attainer`, `problem7_11_exists_exact_inverse_relative_change_max_lower_witness`, `problem7_11_quadratic_remainder_relative_scaled_tendsto_zero_of_eventually_bounded`, `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_quadratic_bound`, `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_eventually_entry_bound`, `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_eventually_infNorm_bound`, `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_eventually_abs_left_product_bound`, `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_componentwise_tendsto_zero` |
| 7.11, nonlinear source `lim sup` wrapper for `µ'_E(A)` | `CLOSED` for the componentwise source-radius `sSup` model | Exact algebraic bridge, quadratic finite upper/lower envelopes, lower-witness perturbation, finite-radius bounded-remainder reduction, conditional `εR → 0` dependency, exact-to-linearized quotient convergence, bounded-remainder discharge from eventual entrywise or infinity-norm inverse boundedness, local inverse-family existence/boundedness for componentwise-admissible perturbations with `ε → 0`, and checked first-order formula are closed; `Ch7InverseComponentwiseRadiusSet`, `ch7InverseComponentwiseRadiusSup`, `ch7InverseComponentwiseRadiusSet_value_le`, `exists_ch7InverseComponentwiseRadiusSet_lower_witness`, `problem7_11_inverse_componentwise_radiusSup_tendsto_linearized`, and `problem7_11_inverse_componentwise_condition_of_positive_radii` close the source-radius supremum/linearized-limit package without assuming a nonlinear condition-number theorem |
| 7.12 | `DEFER-LATER-SPLIT` | Symmetry-preserving backward error requires QR/Householder plus SPD construction integration |
| 7.13 | `CLOSED` | `ch7SparseResidual`, `ch7SparseComputedResidualSafetyTerm`, `ch7SparseComputedResidualImage`, `problem7_13_sparse_residual_error`, `problem7_13_componentwise_bound`, `problem7_13_relative_infNorm_bound` |
| 7.14 | `DEFER-LATER-SPLIT` | Probabilistic expected condition-number result needs probability/distribution infrastructure |
| 7.15 | `CLOSED` for the exact op-2 lower-bound package, conditional equality/least-value attainability certificates, and Appendix A.7.15 nonsingular diagonal attainability case | `ch7HadamardProduct`, `ch7_matTranspose_twoSidedScale`, `ch7HadamardProduct_twoSidedScale_transpose_inverse_eq`, `problem7_15_twoSidedScale_hadamard_transpose_inverse_invariant`, `opNorm2Le_transpose`, `problem7_15_transpose_inverse_partner_opNorm2Le`, `frobNormRect_diagMatrix`, `vecNorm2_diagonal_le_frobNormRect`, `matMulVec_hadamard_eq_diag_rectMatMul_diag_transpose`, `opNorm2Le_hadamard`, `complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le`, `opNorm2Le_complexMatrixOp2_realRectToCMatrix`, `problem7_15_hornJohnson_hadamard_opNorm2Le`, `problem7_15_scaled_inverse_hadamard_opNorm2Le`, `ch7TwoSidedScaledOp2KappaSet`, `ch7TwoSidedScaledOp2KappaSet_nonempty`, `problem7_15_hadamard_op2_le_twoSidedScaledOp2Kappa_mem`, `problem7_15_twoSidedScaledOp2Kappa_sInf_ge_hadamard_op2`, `problem7_15_twoSidedScaledOp2Kappa_sInf_ge_hadamard_op2_of_inverse`, `problem7_15_twoSidedScaledOp2Kappa_sInf_eq_hadamard_op2_of_mem`, `problem7_15_twoSidedScaledOp2Kappa_isLeast_hadamard_op2_of_mem`, `problem7_15_twoSidedScaledOp2Kappa_sInf_eq_hadamard_op2_of_attaining_scaling`, `problem7_15_twoSidedScaledOp2Kappa_isLeast_hadamard_op2_of_attaining_scaling`, `problem7_15_complexMatrixOp2_realRectToCMatrix_orthogonal_eq_one`, `problem7_15_ch7TwoSidedScale_diagMatrix_eq`, `problem7_15_hadamard_diag_inverse_transpose_eq_idMatrix`, `problem7_15_diagonal_hadamard_op2_eq_one`, `problem7_15_diagonal_attaining_scaling_eq_hadamard_op2`, `problem7_15_diagonal_twoSidedScaledOp2Kappa_sInf_eq_one`, and `problem7_15_diagonal_twoSidedScaledOp2Kappa_isLeast_one` prove that the Hadamard product with the transpose inverse is unchanged by compatible reciprocal two-sided diagonal scaling, that the inverse partner's operator-2 bound is preserved by transpose, that the Horn-Johnson Schur-product operator-2 certificate applies to the scaled pair, and that the exact `complexMatrixOp2` Hadamard lower-bound value is below the `sInf` of positive two-sided scaled op-2 condition values; if the lower-bound value is realized by a positive reciprocal scaling, the `sInf` equals it and the value is a least element of the set.  For nonsingular diagonal `A = diag(a)`, the positive scaling `diag(|a_i|^{-1})` realizes equality and gives `sInf = 1` plus `IsLeast 1` |

## Proof Integrity

- The newly added Problem 7.1 theorems prove the local contraction inequality,
  scalar Neumann consequence, and exact nonnegative resolvent/nonsingular-
  inverse entrywise bound from Theorem 7.4 plus the existing nonnegative
  infinity-norm contraction infrastructure.
- The newly added Problem 7.8 theorems prove the augmented rectangular
  Frobenius lower bound and construct the rank-one attaining perturbation,
  including the `theta = 0` degenerate case.
- The newly added computed-residual theorems reuse the repository's
  `IterativeRefinement.conventional_residual_error` result to close the exact
  Chapter 7 dense residual model `(7.30)` and the practical forward bound
  `(7.31)` without introducing any new theorem-equivalent assumptions.
- The new arbitrary-subordinate-norm wrappers close the generic Problem 7.2
  residual/error sandwich, the source-shaped arbitrary subordinate-norm form of
  Theorem 7.2/(7.4), and the source-shaped arbitrary subordinate-norm
  Rigal-Gaches block `(7.1)`-`(7.3)` by reusing the integrated Split 1 mixed-
  subordinate, dual-functional, rank-one, and matrix-inverse APIs directly,
  with no local axioms or placeholder interfaces.
- The Problem 7.7 theorems, including the new arbitrary subordinate-norm eta
  comparison, are genuine Lean proofs over the existing Oettli-Prager and
  Rigal-Gaches equivalences; they do not introduce theorem-equivalent
  assumptions or wrapper-only placeholders.
- The new equation `(7.5)` declarations model the source `lim sup` over
  shrinking perturbation radii, prove the sharp Theorem 7.2 upper envelope,
  and construct an exact rank-one lower witness using the integrated
  dual-functional and norm-attainment APIs.  The final equality is a genuine
  proof, not a definition-only restatement.
- The new Problem 7.13 declarations do not weaken the source row to the dense
  `γ_(n+1)` model: they compress each row to its structural support via
  `ch7RowSupport`, run `fl_dotProduct` only on that support, prove the
  Appendix A.12 row-wise `γ_(w_i+1)` residual bound, and lift it to
  componentwise and relative-infinity-norm forward-error wrappers.
- The new diagnostic theorem
  `exists_ch7CondEFAtSolutionInf_gt_of_positive_fixed_rhs_term` proves that the
  direct fixed-`f` reading of equation `(7.12)` is scale-unbounded whenever the
  `x = 0` contribution from `f` is already positive.  This prevents an
  over-strong bogus closure and justifies the source-faithful global
  supremum model now used for the closed Skeel specialization of `(7.12)`.
- The new `(7.12)` declarations prove that the global nonzero-solution
  supremum of `cond(A,x)` equals Higham's `cond(A)`, with the all-ones vector
  attaining the supremum.  The adjacent factor-2 prose claim is formalized by
  comparing the `f = |b| = |Ax|` componentwise-data condition against
  `cond(A,x)` in both directions.
- The new Appendix A.3 / `(7.16)` declarations prove diagonal row-scaling
  invariance of `cond(A)`, prove `cond(B)=κ∞(B)` when the scaled matrix
  satisfies `|B|e=e`, and derive
  `κ∞(A)/κ∞(D_R) ≤ cond(A) ≤ κ∞(A)` for a positive row-equilibrating scaling.
  The new `(7.15)` declarations model the source minimum as an `sInf` over
  positive diagonal row scalings and prove that value is `cond(A)` when `A`
  has a right inverse, using reciprocal row one-norms to construct `D_R`.
- The new Problem 7.4 declarations close the unit-diagonal symmetric PSD
  scaled-factor form.  Positivity of the finite quadratic form on
  `e_i + e_j` and `e_i - e_j` proves `|H_ij| ≤ 1`; the final theorem then
  proves `cond(H) ≤ κ∞(H) ≤ n cond(H)` by bounding `‖H‖∞ ≤ n` and
  `‖H⁻¹‖∞ ≤ cond(H)` from the row-sum definition, without assuming the
  condition-number comparison.
- The new Problem 7.6(a) declarations prove the row-wise relative-data
  condition bound by expanding `|A⁻¹|(E|x|+|Ax|)`, proving
  `E|x| = |A|e ‖x‖₁` for the row-wise tolerance model, bounding
  `|Ax| ≤ |A||x| ≤ |A|e ‖x‖₁`, and comparing finite suprema against
  `cond(A)`.  The result is a theorem, not a restated assumption.
- The new Problem 7.6(b) declarations prove the columnwise relative-data
  condition bound by expanding the source tolerance `E = e e^T |A|`, proving
  `E|x|` has every component equal to `‖ |A| |x| ‖₁`, bounding
  `‖Ax‖₁ ≤ ‖ |A| |x| ‖₁`, and comparing finite row sums against
  `‖A⁻¹‖∞`.  The result is a theorem, not a restated assumption.
- The new Problem 7.9 declarations prove the finite first-order scalar-output
  componentwise formula:
  `|c^T A⁻¹(Δb - ΔA x)| / |c^T x|` is bounded by
  `ε |c^T A⁻¹|(E|x|+f)/|c^T x|`, and a sign perturbation for both `ΔA` and
  `Δb` attains the numerator.  The follow-up Problem 7.9 declarations prove
  `χ ≥ 1` for the finite linearized condition when `E = |A|` or `f = |b|`.
  The latest Problem 7.9 declarations then prove the exact nonlinear
  componentwise source-radius wrapper: the constructed local inverse candidate
  solves the perturbed system for small componentwise radii, the exact scalar
  change is squeezed between the finite linearized value and a proved
  quadratic remainder, and the shrinking-radius supremum tends to the finite
  componentwise formula.  The latest Problem 7.9 declarations also prove the
  exact nonlinear normwise `ψ` source-radius wrapper: `opNorm2Le` is tested on
  finite basis vectors to obtain the constant componentwise envelope needed by
  the local inverse candidate, the right-hand-side vector norm gives coordinate
  bounds, and a separate normwise quadratic squeeze proves convergence to
  `‖c^T A⁻¹‖₂(‖f‖₂+‖E‖₂‖x‖₂)/|c^T x|` without assuming the nonlinear
  condition-number theorem.
- The new Problem 7.11 declarations prove the finite first-order inverse
  componentwise max formula from Appendix A.11: the upper bound follows from
  two finite triangle inequalities and `|ΔA| ≤ εE`, while the lower witness is
  the source sign perturbation `ΔA = εD₁ED₂`.  The theorem assumes
  nonnegative `E` and nonzero inverse entries exactly where the source ratio
  divides by `|(A⁻¹)ᵢⱼ|`; it does not claim the nonlinear `lim sup` bridge.
- The new exact Problem 7.11 algebraic identity proves
  `(A + ΔA)⁻¹ - A⁻¹ = -A⁻¹ΔAA⁻¹ + A⁻¹ΔAA⁻¹ΔA(A + ΔA)⁻¹` entrywise from
  left/right inverse certificates.  This closes the finite exact
  perturbation-to-first-order decomposition used by the later source-radius
  asymptotic wrapper.
- The new Problem 7.11 quadratic-remainder declarations prove a componentwise
  finite-sum upper bound for
  `A⁻¹ΔAA⁻¹ΔA(A + ΔA)⁻¹`, then lift it to the exact relative finite maximum
  estimate
  `max |(A + ΔA)⁻¹ - A⁻¹|/|A⁻¹| ≤ ε µ'_lin + ε² R`.  This dependency is
  consumed by the source-radius `sSup` theorem below; it does not assume the
  nonlinear condition-number formula.
- The new finite-radius Problem 7.11 declarations prove `R ≥ 0` for the
  relative quadratic-remainder coefficient and derive
  `max |(A + ΔA)⁻¹ - A⁻¹|/|A⁻¹| ≤ ε(µ'_lin + δC)` from the already proved
  finite envelope plus explicit premises `ε ≤ δ` and `R ≤ C`.  This is a
  genuine dependency used by the `lim sup` bridge; local boundedness of the
  concrete inverse family is proved separately by the local-inverse package.
- The new conditional asymptotic Problem 7.11 declaration proves the precise
  vanishing step `εR → 0` from `ε → 0`, `0 ≤ C`, and eventual boundedness
  `|R| ≤ C`, reusing the repository's existing bounded-factor convergence
  lemma.  It keeps the local inverse-boundedness obligation explicit instead
  of converting it into a theorem-equivalent hypothesis hidden inside the
  source statement.
- The new lower-envelope Problem 7.11 declarations prove the reverse finite
  estimate needed for the source `lim sup` lower route:
  exact nonlinear relative change is at least a selected linearized entry
  minus the quadratic remainder, and any entry attaining `εµ'_lin` yields
  `εµ'_lin - ε²R ≤ max |(A + ΔA)⁻¹ - A⁻¹|/|A⁻¹|`.  This is proved from the
  same exact inverse identity and remainder bound; it does not assume the
  existence of a nonlinear inverse family or the later `lim sup` equality.
- The new lower-witness Problem 7.11 declaration packages that lower route
  with an actual admissible perturbation from the finite linearized formula.
  It then chooses a finite entry attaining the resulting linearized maximum
  and proves the exact lower envelope for every certified right inverse of
  `A + ΔA`.  The later local-inverse package supplies those certificates along
  a shrinking perturbation family.
- The new exact-to-linearized Problem 7.11 bridge proves that
  `max |(A + ΔA)⁻¹ - A⁻¹|/(ε|A⁻¹|)` converges to the same filter limit as the
  linearized finite maximum divided by `ε`, provided `ε > 0` eventually,
  `ε → 0`, the perturbations satisfy `|ΔA| ≤ εE` eventually, certified right
  inverses of `A + ΔA` are available eventually, and the quadratic coefficient
  is eventually bounded.  This closes the squeeze argument from the two-sided
  finite envelopes; the later local-inverse package discharges the source-local
  inverse-family existence and boundedness route.
- The new entry-bound Problem 7.11 bridge proves the bounded quadratic-
  coefficient hypothesis from an eventual entrywise bound on the certified
  right inverses `B(t) = (A + ΔA(t))⁻¹`.  This is a finite matrix-product
  monotonicity proof over `|A⁻¹|E`, not a hidden assumption of the source
  `lim sup`; the small-perturbation inverse-family existence and boundedness
  package is proved by the later local-inverse bridge.
- The new infinity-norm Problem 7.11 bridge proves that an eventual
  `infNorm (B t) ≤ C_B` bound on certified right inverses is sufficient for
  the entrywise-bounded exact-to-linearized theorem.  It uses the local
  `|B_ij| ≤ ‖B‖∞` adapter and feeds the local inverse existence/boundedness
  theorem rather than replacing it with an assumption.
- The new local-inverse Problem 7.11 bridge constructs
  `ch7Problem711PerturbedInverseCandidate`, proves it is a certified right
  inverse of `A + ΔA` under `‖ |A⁻¹ΔA| ‖∞ ≤ c < 1`, proves an explicit
  candidate `∞`-norm bound, derives eventual half-contraction from
  componentwise admissibility and `ε → 0`, and proves the exact-to-linearized
  quotient convergence for this constructed inverse family.
- The new Problem 7.11 radius-supremum declarations model the source nonlinear
  `lim sup` as an `sSup` over exact inverse relative changes with shrinking
  componentwise perturbation radius, prove upper and lower envelopes
  `µ'_lin ± ρC`, and show that the radius supremum tends to the finite
  linearized condition number via
  `problem7_11_inverse_componentwise_radiusSup_tendsto_linearized` and
  `problem7_11_inverse_componentwise_condition_of_positive_radii`.
- No local placeholders were introduced for open `PROVE-NOW-SPLIT2`, `DEFER-LATER-SPLIT`,
  `DEFER-LATER-CHAPTER`, or `SKIP` rows.
- The lookup files name every source-facing Chapter 7 declaration:
  `docs/LIBRARY_LOOKUP.md` and `examples/LibraryLookup.lean`.

## Open Current-Split Targets After Previous-Split Re-Audit

The remaining Chapter 7 rows are open current-branch targets rather than
external Split 1 blockers:

- Generic vector norms and arbitrary subordinate matrix norms: integrated
  Split 1 supplies `IsComplexVectorNorm`, `IsMixedSubordinateNormValue`,
  `IsMixedSubordinateMatrixNormValue`, `IsComplexMatrixLpNormValue`,
  `complexMatrixLpNormOfReal`, and condition-product/radius wrappers.  The
  generic normwise condition-number row `(7.5)` is closed, equation
  `(7.12)` is now closed for the Skeel infinity-norm source specialization,
  equations `(7.15)`-`(7.16)` are now closed for the positive
  row-scaling/infinity-norm formulation, and Problem 7.6(a)-(b) is closed for
  the row-wise and columnwise relative-data infinity-norm formulations.  The
  Problem 7.11 Appendix A.11 first-order finite-max formula and exact
  first-order/remainder identity, finite quadratic upper/lower envelopes,
  lower-witness perturbation, finite-radius bounded-remainder reduction, plus
  the conditional `εR → 0` asymptotic dependency, constructed local
  inverse-family bridge, and nonlinear source-radius `sSup`/`lim sup` wrapper
  are also closed.  The
  fixed-`f` diagnostic remains in the library to document why the naive
  fixed right-hand-side maximization is not the source-faithful finite model.
- Pseudoinverse, projection, and remaining van der Sluis diagonal scaling
  minimization: integrated
  Split 1 supplies substantial rank/SVD/Frobenius facts such as
  `complexMatrixRank`, `complexMatrixRank_eq_card_nonzero_singularValue`,
  `exists_complexMatrixSVDUnitary_diagonal_eq`, and
  `complexMatrixFrobenius`.  The row-equilibrated equality, positive-scaling
  infimum, inequality package behind Appendix A.3, Theorem 7.5's `p = 1`
  pairwise column-scaling algebraic specialization, `p = 2` pairwise
  column-scaling condition-product specialization, and `p = ∞` pairwise
  row-scaling algebraic specialization, and Stewart-Sun Frobenius right-scaling
  minimizer in Theorem 7.7 are now closed, but the current branch search finds
  only certificate-style Moore-Penrose surfaces elsewhere, not a reusable
  Chapter 7 pseudoinverse/projection theorem for the full Theorem 7.5 source
  statement.  The next target is to expose or prove a source-facing wrapper,
  not to leave an external Split 1 blocker.
- Perron-Frobenius/Bauer scaling: the branch has spectral-radius carrier
  machinery and now has the Problem 7.10(a) two-sided diagonal-scaling algebra
  proved under an explicit positive Perron-vector certificate plus the
  Problem 7.10(b) `B = |A|`, `C = |A⁻¹|` absolute-value scaled-`κ∞`
  instantiation under the same certificate, the Problem 7.10(e) one-norm
  transpose branch under the corresponding certificate for `BᵀCᵀ` and
  `|A|ᵀ|A⁻¹|ᵀ`, and the fixed-scaling 2-norm interpolation theorem for the
  last clause of Problem 7.10(e).  It also has exact `sInf = ρ` wrappers for
  the Problem 7.10(a) infinity-norm Bauer value set, the Problem 7.10(b)
  scaled-`κ∞` value set, and the one-norm scaled-`κ₁` transpose value set under
  those explicit certificates.  The current branch now exports the same
  supplied certificates to the generic Split 1
  `IsMaxComplexMatrixEigenvalueModulus` interface, reuses the integrated Split
  1 norm-existence theorem to obtain consistent norms with value `≤ ρ + δ`,
  and proves real `sSup = ρ` statements for moduli of Mathlib
  `spectrum (Matrix.toLin' ...)` elements of the complexified Bauer products.
  It also has the positive-entry adapter proving irreducibility of `BC`/`CB`
  and `|A||A⁻¹|`/`|A⁻¹||A|`, and the source-shaped irreducible-product proof
  that this supplied positive eigenvector certificate gives `Cx > 0`; it still
  lacks a source-facing Perron-Frobenius positive-eigenvector theorem from
  irreducibility, the value-representation bridge from the proved real
  spectrum-modulus supremum to Mathlib's Banach-algebra `spectralRadius`, and
  the global compatible Bauer minimization package needed for
  `inf κ₂ <= ρ(|A||A⁻¹|)`.  Problem 7.15 now
  has the reciprocal two-sided scaling invariance of `A ∘ A^{-T}`, the
  transpose/operator-2 certificate side condition for inverse partners, the
  Horn-Johnson operator-2 Hadamard certificate route, the exact op-2 `sInf`
  lower-bound package, and the conditional attainability certificate closed.
  Theorem 7.8 and the remaining Perron-Frobenius/spectral-radius/global
  Bauer-minimization parts of Problem 7.10 remain current proof/API targets.
- Probability/distribution infrastructure for Problem 7.14.

## Current Pass Close-Out

The full item-by-item Chapter 7 ledger remains the three inventories above.
This close-out section records the current-pass deltas and the verification
facts explicitly required by the proof-completion prompt.

### 1. Formalized End-To-End Without Unresolved Previous-Split Blocking

| Source label/name | Lean declaration(s) | File path | Newly proved or reused | Proof chain |
| --- | --- | --- | --- | --- |
| Equation (7.12), Skeel infinity-norm global condition number | `ch7CondEFGlobalInf`, `ch7SkeelGlobalCondInf`, `ch7SkeelCondAtSolutionInf_le_condSkeel`, `eq_7_12_skeel_global_conditionNumber_eq_condSkeel` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proofs; the global nonzero-solution supremum is bounded above by `cond(A)` and attained by the all-ones vector, while the fixed-`f` unboundedness diagnostic remains separate |
| Prose after (7.14), factor-2 comparison for `f = |b| = |Ax|` | `ch7ComponentwiseDataCondAtSolutionInf`, `ch7SkeelCondAtSolutionInf_le_componentwiseDataCondAtSolutionInf`, `ch7ComponentwiseDataCondAtSolutionInf_le_two_mul_skeelCondAtSolutionInf` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proofs; the lower bound is monotonicity of the `f` term and the upper bound uses `|Ax| ≤ |A||x|` to prove the source factor `2` |
| Appendix A.3 / equations (7.15)-(7.16), row-equilibrated scaling package | `ch7RowScale`, `ch7InverseRowScale`, `ch7RowsEquilibratedInf`, `ch7_condSkeel_rowScale_eq`, `ch7_condSkeel_eq_kappaInf_of_rowsEquilibratedInf`, `problem7_3_rowEquilibrated_scaling_condition_eq`, `problem7_3_rowEquilibrated_lower_bound`, `eq_7_16_rowEquilibrated_bounds`, `ch7PositiveRowScaledKappaInfSet`, `ch7RowEquilibratingScale`, `ch7RowsEquilibratedInf_rowEquilibratingScale_of_right_inverse`, `eq_7_15_positive_rowScaling_sInf_eq_condSkeel_of_right_inverse` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proofs; diagonal row-scaling invariance, `cond(B)=κ∞(B)` under `|B|e=e`, both inequalities in `(7.16)`, and the positive-row-scaling `sInf` form of `(7.15)` are proved without assuming the minimization conclusion |
| Problem 7.4, unit-diagonal symmetric PSD scaled-factor condition bounds | `problem7_4_abs_entry_le_one_of_finitePSD_diag_one`, `problem7_4_unitDiagonal_entryBound_condition_bounds`, `problem7_4_unitDiagonal_finitePSD_condition_bounds` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; finite quadratic-form positivity on `e_i ± e_j` proves the SPD entry bound, and finite row-sum/`infNorm` comparisons prove `cond(H) ≤ κ∞(H) ≤ n cond(H)` without a theorem-equivalent hypothesis |
| Theorem 7.5 rank/one-sided-inverse side-condition bridges | `ch7RectColumnLpNormOfReal_pos_of_rect_left_inverse`, `ch7RectColumnNorm2_pos_of_rect_left_inverse`, `ch7RectColumnNorm1_pos_of_rect_left_inverse`, `ch7RectRowDualLpNormOfReal_pos_of_rect_right_inverse`, `ch7RectRowNorm2_pos_of_rect_right_inverse`, `ch7RectRowNorm1_pos_of_rect_right_inverse`, `theorem7_5_lp_column_equilibration_le_card_rpow_sInf_right_scalings_of_rect_left_inverse`, `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings_of_rect_left_inverse`, `theorem7_5_p1_column_equilibration_isLeast_right_scalings_of_rect_left_inverse`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings_of_rect_right_inverse`, `theorem7_5_p2_row_equilibration_le_sqrt_card_sInf_left_scalings_of_rect_right_inverse`, `theorem7_5_pinf_row_equilibration_isLeast_left_scalings_of_rect_right_inverse` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; zero column/row norm would make the diagonal entry of `Aplus A = I` or `A Aplus = I` equal both `0` and `1`, so the existing equilibrating-scale theorems can be applied with source-shaped rectangular rank witnesses. These wrappers do not assert Moore-Penrose existence or the full source diagonal-minimum theorem |
| Theorem 7.5 linear-map rank-form bridge | `ch7RectMatMulVecLinearMap`, `ch7_exists_rect_left_inverse_of_linear_left_inverse`, `ch7_exists_rect_right_inverse_of_linear_right_inverse`, `ch7_exists_rect_left_inverse_of_rectMatMulVec_injective`, `ch7_exists_rect_right_inverse_of_rectMatMulVec_surjective`, `theorem7_5_lp_column_equilibration_exists_left_inverse_of_rectMatMulVec_injective`, `theorem7_5_p2_column_equilibration_exists_left_inverse_of_rectMatMulVec_injective`, `theorem7_5_p1_column_equilibration_exists_left_inverse_of_rectMatMulVec_injective`, `theorem7_5_lp_dual_row_equilibration_exists_right_inverse_of_rectMatMulVec_surjective`, `theorem7_5_p2_row_equilibration_exists_right_inverse_of_rectMatMulVec_surjective`, `theorem7_5_pinf_row_equilibration_exists_right_inverse_of_rectMatMulVec_surjective` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; Mathlib's linear-map left-inverse theorem and finite-function splitting theorem construct linear retractions from injectivity/surjectivity of `x ↦ A*x`, and the proof extracts concrete matrix entries by expanding a linear map on standard coordinates. The resulting existential wrappers use those proved matrices to instantiate the existing explicit-`Aplus` Theorem 7.5 specializations; no theorem-equivalent hypothesis, Moore-Penrose construction, or minimizer-attainment statement is hidden |
| Theorem 7.5 Matrix-rank source-rank bridge | `ch7_rectMatMulVec_injective_of_matrix_rank_eq_width`, `ch7_rectMatMulVec_surjective_of_matrix_rank_eq_height`, `theorem7_5_lp_column_equilibration_exists_left_inverse_of_matrix_rank_eq_width`, `theorem7_5_p2_column_equilibration_exists_left_inverse_of_matrix_rank_eq_width`, `theorem7_5_p1_column_equilibration_exists_left_inverse_of_matrix_rank_eq_width`, `theorem7_5_lp_dual_row_equilibration_exists_right_inverse_of_matrix_rank_eq_height`, `theorem7_5_p2_row_equilibration_exists_right_inverse_of_matrix_rank_eq_height`, `theorem7_5_pinf_row_equilibration_exists_right_inverse_of_matrix_rank_eq_height` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; Mathlib defines `Matrix.rank` as the finite-dimensional rank of `mulVecLin`. Rank-nullity proves full-column rank gives injectivity and full-row rank gives surjectivity, and the wrappers instantiate the existing injective/surjective Theorem 7.5 specializations. This closes the printed `rank(A)=n/m` side-condition bridge for the existing explicit-`Aplus` models, without constructing a Moore-Penrose pseudoinverse or asserting the remaining general source `min` theorem |
| Theorem 7.5 Penrose1-to-projection bridge | `theorem7_5_rect_left_inverse_of_penrose1_rectMatMulVec_injective`, `theorem7_5_rect_right_inverse_of_penrose1_rectMatMulVec_surjective`, `theorem7_5_rect_left_inverse_of_penrose1_matrix_rank_eq_width`, `theorem7_5_rect_right_inverse_of_penrose1_matrix_rank_eq_height`, `theorem7_5_rect_penrose_injective_symmetric_range_projection_op2Le_one`, `theorem7_5_rect_penrose_surjective_symmetric_domain_projection_op2Le_one`, `theorem7_5_rect_penrose_injective_symmetric_range_projection_residual_orthogonal_range`, `theorem7_5_rect_penrose_surjective_symmetric_domain_projection_residual_orthogonal_range`, `theorem7_5_rect_penrose_injective_symmetric_range_projection_residual_normSq_isLeast`, `theorem7_5_rect_penrose_surjective_symmetric_domain_projection_residual_normSq_isLeast`, `theorem7_5_rect_penrose_injective_symmetric_range_projection_residual_norm_isLeast`, `theorem7_5_rect_penrose_surjective_symmetric_domain_projection_residual_norm_isLeast`, `theorem7_5_rect_penrose_matrix_rank_eq_width_symmetric_range_projection_residual_normSq_isLeast`, `theorem7_5_rect_penrose_matrix_rank_eq_height_symmetric_domain_projection_residual_normSq_isLeast` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; applying the first Penrose equation to basis vectors and using injectivity proves `Aplus A = I`, while surjectivity rewrites every target vector as `Ax` and proves `A Aplus = I`. The wrappers then reuse the previously proved symmetric projection contraction, orthogonality, and least-residual theorems under Penrose equation plus injectivity/surjectivity or the printed rank equalities. This does not construct a Moore-Penrose inverse or derive Penrose symmetry from rank hypotheses |
| Theorem 7.5 Penrose-equation package | `theorem7_5_rect_left_inverse_symmetric_penrose_equations`, `theorem7_5_rect_right_inverse_symmetric_penrose_equations`, `theorem7_5_rect_penrose_injective_symmetric_range_penrose_equations`, `theorem7_5_rect_penrose_surjective_symmetric_domain_penrose_equations`, `theorem7_5_rect_penrose_matrix_rank_eq_width_symmetric_range_penrose_equations`, `theorem7_5_rect_penrose_matrix_rank_eq_height_symmetric_domain_penrose_equations` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; `Aplus A = I` rewrites `A Aplus A` and `Aplus A Aplus`, while identity symmetry supplies symmetry of `Aplus A`; the right-inverse branch symmetrically rewrites `A Aplus = I` and proves symmetry of `A Aplus`.  The rank/injective/surjective wrappers first derive the relevant one-sided inverse from the first Penrose equation, then package all four Penrose equation/symmetry conditions under the supplied range/domain projection symmetry.  This still does not construct `Aplus` or prove the first Penrose equation/projection symmetry from the rank hypotheses |
| Theorem 7.5 Penrose1-plus-rank source `sInf`/`min` adapters | `theorem7_5_p1_column_equilibration_isLeast_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_lp_column_equilibration_le_card_rpow_sInf_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings_of_penrose1_matrix_rank_eq_height`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings_of_penrose1_matrix_rank_eq_height`, `theorem7_5_p2_row_equilibration_le_sqrt_card_sInf_left_scalings_of_penrose1_matrix_rank_eq_height`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_penrose1_matrix_rank_eq_height`, `theorem7_5_pinf_row_equilibration_isLeast_left_scalings_of_penrose1_matrix_rank_eq_height` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; each wrapper first derives `Aplus A = I` or `A Aplus = I` from `AAplusA = A` plus the printed matrix rank hypothesis using the already proved Penrose1/rank bridge, then applies the corresponding endpoint least-element, non-endpoint `sInf`, or conditional source-`min` theorem.  These proofs do not introduce a new minimizer-existence assumption beyond the explicit `IsLeast` certificate already present in the non-endpoint source-`min` adapters, and they do not construct the Moore-Penrose inverse |
| Theorem 7.5 Moore-Penrose projection dependency | `rectMatMul_id_left`, `rectMatMul_id_right`, `rectMatMul_assoc`, `rectMatMul_rangeProjection_idempotent_of_left_inverse`, `rectMatMul_domainProjection_idempotent_of_right_inverse`, `rectOpNorm2Le_rangeProjection_of_symmetric_left_inverse`, `rectOpNorm2Le_domainProjection_of_symmetric_right_inverse`, `finiteMatVec_projection_residual_eq_zero_of_idempotent`, `finiteVecInnerProduct_projection_residual_range_eq_zero`, `finiteVecNorm2Sq_add_of_inner_eq_zero`, `finiteVecNorm2Sq_projection_residual_le_residual_to_range_of_symmetric_idempotent`, `finiteVecNorm2_projection_residual_le_residual_to_range_of_symmetric_idempotent`, `rectMatMulVec_idMatrix`, `rectMatMulVec_rangeProjection_apply_range_of_left_inverse`, `rectMatMulVec_domainProjection_apply_range_of_right_inverse`, `rectMatMulVec_rangeProjection_residual_orthogonal_range_of_symmetric_left_inverse`, `rectMatMulVec_domainProjection_residual_orthogonal_range_of_symmetric_right_inverse`, `rectMatMulVec_rangeProjection_residual_normSq_le_range_residual_of_symmetric_left_inverse`, `rectMatMulVec_domainProjection_residual_normSq_le_range_residual_of_symmetric_right_inverse`, `rectMatMulVec_rangeProjection_residual_norm_le_range_residual_of_symmetric_left_inverse`, `rectMatMulVec_domainProjection_residual_norm_le_range_residual_of_symmetric_right_inverse`, `theorem7_5_rect_left_inverse_range_projection_idempotent`, `theorem7_5_rect_right_inverse_domain_projection_idempotent`, `theorem7_5_rect_left_inverse_symmetric_range_projection_op2Le_one`, `theorem7_5_rect_right_inverse_symmetric_domain_projection_op2Le_one`, `theorem7_5_rect_left_inverse_range_projection_fixes_range`, `theorem7_5_rect_right_inverse_domain_projection_fixes_range`, `theorem7_5_rect_left_inverse_symmetric_range_projection_residual_orthogonal_range`, `theorem7_5_rect_right_inverse_symmetric_domain_projection_residual_orthogonal_range`, `theorem7_5_rect_left_inverse_symmetric_range_projection_residual_normSq_le_range_residual`, `theorem7_5_rect_right_inverse_symmetric_domain_projection_residual_normSq_le_range_residual`, `theorem7_5_rect_left_inverse_symmetric_range_projection_residual_norm_le_range_residual`, `theorem7_5_rect_right_inverse_symmetric_domain_projection_residual_norm_le_range_residual` | `LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean`; `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; finite rectangular associativity and identity laws prove that `A Aplus` is idempotent from `Aplus A = I` and that `Aplus A` is idempotent from `A Aplus = I`.  The symmetric variants reuse the existing finite symmetric-idempotent Euclidean contraction theorem to prove operator-2 norm at most one.  The new finite residual lemma proves `P(x-Px)=0` for an idempotent `P`, moves a symmetric `P` across the finite inner product, and therefore proves `x-Px` is orthogonal to every `Py`; the Pythagorean lemma then proves the squared-norm best-approximation inequality against every range vector, and the norm-form theorem follows by monotonicity of square root.  The rectangular wrappers instantiate this for `AAplus` and `AplusA`, prove they fix the ranges of `A` and `Aplus`, and expose source-facing range/domain least-squares-style inequalities.  These close algebraic, symmetric-idempotent contraction, residual-orthogonality, and squared-/ordinary-norm best-approximation projection dependencies only; Moore-Penrose inverse existence and the Penrose symmetry conditions remain open source-facing work |
| Equations (7.20)-(7.21), Euclidean column-equilibration dependency | `ch7RectColumnNorm2`, `ch7RectRightScale`, `ch7ColumnEquilibratingScale2`, `eq_7_20_column_norm_le_of_rectOpNorm2Le`, `ch7RectColumnNorm2_le_frobNormRect`, `ch7_frobNormRect_le_sqrt_card_mul_column_bound`, `eq_7_20_rectOpNorm2Le_of_column_bound`, `eq_7_21_rectOpNorm2Le_column_equilibrated` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; testing the operator certificate on a basis vector proves the column lower bound, finite Frobenius/cardinality summation proves the upper bound, and reciprocal nonzero-column scaling gives the `sqrt(n)` operator bound. This closes only the `p = 2` dependency, not the full Theorem 7.5 source theorem |
| Theorem 7.5 / equations (7.18), (7.21), and (7.22), `p = 1` column-scaling specialization | `ch7RectColumnNorm1`, `ch7RectLeftScale`, `ch7ColumnEquilibratingScale1`, `eq_7_21_oneNormRect_column_equilibrated`, `ch7OneNormRightScaledCond`, `ch7OneNormRightScaledCondSet`, `eq_7_22_oneNormRect_inverseSide_bound`, `theorem7_5_p1_column_equilibration_le_right_scaling`, `theorem7_5_p1_column_equilibration_sInf_eq_right_scalings` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; finite column-sum algebra proves the equilibrated 1-norm bound, the inverse diagonal relation proves the `(7.22)` inverse-side inequality for an explicit inverse-side matrix, the pairwise condition-product inequality follows, and the value-set/`sInf` wrapper proves exact infimum attainment for the specialized explicit-`Aplus` model without assuming Moore-Penrose existence or the full source minimization conclusion |
| Theorem 7.5 / equations (7.18), (7.21), and (7.22), `p = 2` column-scaling specialization | `ch7_vecNorm2_mul_le_of_abs_le`, `ch7RectLeftScale_rectOpNorm2Le_of_abs_le`, `ch7Op2RightScaledCond`, `ch7Op2RightScaledCondSet`, `ch7Op2RightScaledCondSet_nonempty`, `ch7Op2RightScaledCondSet_bddBelow`, `eq_7_22_op2_inverseSide_bound`, `theorem7_5_p2_column_equilibration_le_sqrt_card_right_scaling`, `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; coordinatewise Euclidean scaling bounds the inverse-side operator certificate, the diagonal inverse relation proves the p=2 `(7.22)` analogue for an explicit inverse-side matrix, multiplying with the existing `(7.21)` operator certificate proves `κ₂(AD_C) <= sqrt(n) κ₂(AD)` pairwise, and `le_csInf` packages that result as `κ₂(AD_C) <= sqrt(n) inf_D ‖AD‖₂‖D⁻¹Aplus‖₂` for the specialized explicit-`Aplus` model |
| Theorem 7.5 / equations (7.18), (7.21), and (7.22), finite-real `p` column-scaling specialization | `complexMatrixLpNormOfReal_mul_le`, `ch7_complexMatrixLpNormOfReal_nonneg`, `ch7_complexVecLpNormOfReal_diagScale_le_of_norm_le`, `eq_7_22_matrixLpNormOfReal_inverseSide_bound`, `ch7LpRightScaledCondOfReal`, `ch7LpRightScaledCondSetOfReal`, `ch7LpRightScaledCondOfReal_nonneg`, `ch7LpRightScaledCondOfReal_mem_set`, `ch7LpRightScaledCondSetOfReal_nonempty`, `theorem7_5_lp_column_equilibration_le_card_rpow_right_scaling`, `theorem7_5_lp_column_equilibration_le_card_rpow_sInf_right_scalings` | `LeanFpAnalysis/FP/Analysis/Norms.lean`; `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; the reusable finite-real matrix `p`-norm multiplication wrapper proves subordinate composition, the Chapter 7 diagonal-vector multiplier lemma proves bounded coordinatewise scaling in finite `Lp`, `(7.22)` follows from `(7.20)` applied to `AD` and the reciprocal diagonal relation, and the pairwise plus `sInf` wrappers prove `‖AD_C‖_p‖D_C⁻¹Aplus‖_p <= n^(1-1/p) * inf_D ‖AD‖_p‖D⁻¹Aplus‖_p` in the explicit-`Aplus` model without assuming Moore-Penrose existence or source minimizer attainment |
| Theorem 7.5 / equation (7.19), finite-real conjugate-row `p` proof-route specialization | `ch7RectRowDualLpNormOfReal`, `ch7RowDualEquilibratingScaleLpOfReal`, `eq_7_19_matrixLpNormOfReal_dual_row_equilibrated`, `eq_7_19_matrixLpNormOfReal_dual_row_inverseSide_bound`, `ch7LpLeftScaledCondOfReal`, `ch7LpLeftScaledCondSetOfReal`, `ch7LpLeftScaledCondOfReal_nonneg`, `ch7LpLeftScaledCondOfReal_mem_set`, `ch7LpLeftScaledCondSetOfReal_nonempty`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_left_scaling`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; the row-dual max bounds from the finite `Lp` API prove `‖D_R A‖_p <= m^(1/p)` for the reciprocal `q`-row scale dictated by the source proof's transpose identity `(6.21)`, the explicit inverse-side matrix `Aplus D_R^{-1}` is bounded by `‖DA‖_p‖Aplus D^{-1}‖_p` through a proved coordinatewise diagonal multiplier argument, and pairwise plus `sInf` wrappers close this conjugate-row proof-route model without assuming Moore-Penrose existence, minimizer attainment, or the full printed row-scale statement |
| Theorem 7.5 non-endpoint source `min` adapters for explicit-`Aplus` value sets | `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_rect_left_inverse`, `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings`, `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings_of_rect_left_inverse`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings_of_rect_right_inverse`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_rect_right_inverse` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; each theorem rewrites an already proved `sInf` bound through Mathlib's `IsLeast.csInf_eq`, and the one-sided-inverse variants reuse the proved source-rank positivity bridges. These are conditional adapters from a supplied least-value certificate to the book's `min` notation; they do not prove minimizer existence, assert a Moore-Penrose construction, or close the full general Theorem 7.5 source theorem |
| Theorem 7.5 / equation (7.19), `p = ∞` row-scaling specialization | `ch7RectRowNorm1`, `ch7RowEquilibratingScale1Rect`, `eq_7_19_infNormRect_row_equilibrated`, `ch7InfNormLeftScaledCond`, `ch7InfNormLeftScaledCondSet`, `eq_7_19_infNormRect_inverseSide_bound`, `theorem7_5_pinf_row_equilibration_le_left_scaling`, `theorem7_5_pinf_row_equilibration_sInf_eq_left_scalings` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; finite row-sum algebra proves the row-equilibrated infinity-norm bound, the inverse diagonal relation proves the `(7.19)` inverse-side inequality for an explicit inverse-side matrix, the pairwise condition-product inequality follows, and the value-set/`sInf` wrapper proves exact infimum attainment for the specialized explicit-`Aplus` model |
| Corollary 7.6 / equation (7.23), SPD diagonal scaling in the explicit inverse-Gram `sInf` model | `ch7SymmetricDiagEquilibratingScale2`, `ch7SymmetricDiagEquilibratingInvScale2`, `corollary7_6_cholesky_diag_eq_column_norm_sq`, `corollary7_6_cholesky_diag_invScale_eq_column_norm`, `corollary7_6_cholesky_diag_scale_eq_column_equilibrating`, `corollary7_6_cholesky_column_norm_pos`, `corollary7_6_cholesky_factor_column_equilibrated`, `corollary7_6_cholesky_factor_op2Le_sqrt_card`, `corollary7_6_cholesky_factor_column_scaling_le_sqrt_card_sInf_right_scalings`, `ch7SymmetricOp2ScaledCond`, `ch7SymmetricOp2ScaledCondSet`, `ch7SymmetricOp2ScaledCond_mem_set`, `ch7SymmetricOp2ScaledCondSet_nonempty`, `ch7SymmetricOp2ScaledCond_nonneg`, `ch7SymmetricOp2ScaledCondSet_bddBelow`, `ch7CholeskyInverseGram`, `corollary7_6_cholesky_scaled_gram_eq`, `corollary7_6_cholesky_scaled_inverse_gram_eq`, `corollary7_6_cholesky_scaled_cond_eq_factor_cond_sq`, `corollary7_6_cholesky_scaled_cond_le_card_sInf_right_scalings_sq`, `corollary7_6_cholesky_right_sInf_sq_le_symmetric_sInf`, `corollary7_6_cholesky_scaled_cond_le_card_sInf_symmetric_scalings`, `corollary7_6_cholesky_inverse_gram_isInverse`, `corollary7_6_cholesky_scaled_inverse_gram_isInverse` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; the diagonal Gram identity gives `a_jj = ‖R(:,j)‖₂²`, positivity identifies `sqrt(a_jj)` with the column norm, the source scale `D* = diag(a_jj^{-1/2})` is proved equal to the column-equilibrating scale for `R`, and the closed p=2 Theorem 7.5 `sInf` wrapper is instantiated for `R`. The inverse-side lemmas prove `Rinv Rinvᵀ` inverts `RᵀR` and that `D⁻¹(Rinv Rinvᵀ)D⁻¹` inverts `DAD`; the product-square lemma proves the corresponding complexified operator-2 condition product is the square of the right-scaled Cholesky-factor product. The new symmetric value-set transfer proves `(sInf factor-values)^2 <= sInf {κ₂(DAD)}`, yielding the final source-scale bound `κ₂(D*AD*) <= n * sInf {κ₂(DAD)}` without assuming the Corollary 7.6 conclusion or asserting minimizer attainment |
| Theorem 7.7, Stewart-Sun Frobenius right-scaling minimizer | `ch7StewartSunFrobeniusValue`, `ch7FrobeniusRightScaledCond`, `ch7StewartSunScale`, `ch7StewartSunInvScale`, `theorem7_7_frobenius_right_scaling_lower_bound`, `theorem7_7_stewart_sun_frobenius_scaling`, `theorem7_7_stewart_sun_frobenius_scaling_of_left_inverse` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; Frobenius norms of right/left diagonal scalings are reduced to Euclidean column/row norm vectors, Cauchy's inequality proves the universal lower bound, the Stewart-Sun square-root scaling attains it, and the public wrapper derives the nonzero column/inverse-row norm side conditions from `A_inv * A = I` |
| Problem 7.10(a), Bauer two-sided scaling algebra under a positive Perron-vector certificate | `ch7TwoSidedScale`, `ch7TwoSidedScaledInfCond`, `ch7_infNorm_ge_of_nonneg_right_eigenvector`, `problem7_10a_scaled_infCond_ge_perron_of_positive_eigenvector`, `problem7_10a_canonical_scaled_infCond_eq_perron_of_positive_eigenvector`, `problem7_10a_positive_entries_canonical_scaled_infCond_eq_perron` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; finite infinity-norm submultiplicativity and row-sum algebra prove the lower bound for every positive inverse diagonal pair and prove the source canonical scaling `D₁ = diag(x)⁻¹`, `D₂ = diag(Cx)` attains the certified eigenvalue. The theorem surface keeps Perron-vector/spectral-radius existence explicit and does not assume the Bauer minimization theorem |
| Problem 7.10(a), Bauer infinity-norm `sInf = ρ` minimization under a positive Perron-vector certificate | `ch7TwoSidedScaledInfCondSet`, `ch7TwoSidedScaledInfCond_mem_set`, `ch7TwoSidedScaledInfCondSet_nonempty`, `ch7TwoSidedScaledInfCondSet_bddBelow`, `problem7_10a_scaledInfCondSet_sInf_eq_perron_of_positive_eigenvector`, `problem7_10a_positive_entries_scaledInfCondSet_sInf_eq_perron` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; the value set ranges over positive reciprocal two-sided diagonal scalings, `le_csInf` uses the already proved Bauer lower bound for every member, `csInf_le` uses the canonical source scaling as a member, and `le_antisymm` proves exact `sInf = ρ` without assuming Perron-Frobenius existence or spectral-radius identification |
| Problem 7.10(a)/(b), finite complex eigenvalue-radius dominance and attainment under a positive Perron-vector certificate | `ch7IsComplexEigenvalueRadius`, `ch7_complex_eigenvalue_norm_le_of_positive_real_eigenvector`, `ch7_real_positive_eigenvector_complexified`, `ch7_isComplexEigenvalueRadius_of_positive_real_eigenvector`, `problem7_10a_product_isComplexEigenvalueRadius_of_positive_eigenvector`, `problem7_10b_abs_product_isComplexEigenvalueRadius_of_positive_eigenvector` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; a finite maximizer of `‖z_i‖ / x_i`, triangle inequality, nonnegative row-sum comparison, and cancellation prove every complex eigenvalue certificate has modulus at most `ρ`, while the positive real eigenvector supplies an attained complexified eigenvalue. This is a local finite-dimensional eigenvalue-radius predicate, not Perron-Frobenius existence from irreducibility and not an identification with Mathlib's Banach-algebra `spectralRadius` |
| Problem 7.10(a)/(b), local finite eigenvalue-modulus maximum and `sSup = ρ` spectral-radius surrogate under a positive Perron-vector certificate | `ch7ComplexEigenvalueModulusSet`, `ch7_complexEigenvalueModulusSet_isGreatest_of_isComplexEigenvalueRadius`, `ch7_complexEigenvalueModulusSet_sSup_eq_of_isComplexEigenvalueRadius`, `problem7_10a_product_complexEigenvalueModulusSet_isGreatest_of_positive_eigenvector`, `problem7_10a_product_complexEigenvalueModulusSet_sSup_eq_of_positive_eigenvector`, `problem7_10b_abs_product_complexEigenvalueModulusSet_isGreatest_of_positive_eigenvector`, `problem7_10b_abs_product_complexEigenvalueModulusSet_sSup_eq_of_positive_eigenvector` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; the local radius predicate gives an actual member at `ρ` and an upper bound for every eigenvalue modulus, so `IsGreatest` and `sSup = ρ` follow by `csSup_le`/`le_csSup`. This closes the local finite-dimensional `sSup`/maximum half of the spectral-radius wording, but still does not prove Perron-Frobenius existence from irreducibility or identify this local set supremum with Mathlib's Banach-algebra `spectralRadius` |
| Problem 7.10(a), scaled Bauer product local eigenvalue-modulus maximum and `sSup = ρ` | `problem7_10a_scaled_product_isComplexEigenvalueRadius_of_positive_eigenvector`, `problem7_10a_scaled_product_complexEigenvalueModulusSet_isGreatest_of_positive_eigenvector`, `problem7_10a_scaled_product_complexEigenvalueModulusSet_sSup_eq_of_positive_eigenvector` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; the existing scaled-product eigenvector identity transports the supplied positive Perron-vector certificate through any positive reciprocal two-sided scaling, nonnegativity of the scaled factors is proved entrywise, and the local radius predicate then gives an attained greatest eigenvalue modulus and real `sSup = ρ`. This still does not prove Perron-Frobenius existence or identify the local supremum with Mathlib's Banach-algebra `spectralRadius` |
| Problem 7.10(a)/(b), Mathlib spectrum-modulus `sSup = ρ` bridge under a positive Perron-vector certificate | `complexMatrixEigenvalueModulusSet_eq_toLin_spectrum_modulusSet`, `ch7_complexEigenvalueModulusSet_eq_complexMatrixEigenvalueModulusSet`, `ch7_complexEigenvalueModulusSet_eq_toLin_spectrum_modulusSet`, `ch7_toLin_spectrum_modulusSet_isGreatest_of_isComplexEigenvalueRadius`, `ch7_toLin_spectrum_modulusSet_sSup_eq_of_isComplexEigenvalueRadius`, `problem7_10a_product_toLin_spectrum_modulusSet_sSup_eq_of_positive_eigenvector`, `problem7_10b_abs_product_toLin_spectrum_modulusSet_sSup_eq_of_positive_eigenvector`, `problem7_10a_scaled_product_toLin_spectrum_modulusSet_sSup_eq_of_positive_eigenvector` | `LeanFpAnalysis/FP/Analysis/Norms.lean`; `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; local eigenvector witnesses are converted to and from `Module.End.HasEigenvalue`/Mathlib `spectrum` membership for `Matrix.toLin'`, then the established Chapter 7 radius certificate yields a greatest element and real `sSup = ρ` for the Mathlib spectrum-modulus set. This closes the spectrum-set bridge and feeds the `spectralRadius` equality row below |
| Problem 7.10(a)/(b), Mathlib Banach-algebra `spectralRadius = ENNReal.ofReal ρ` bridge under a positive Perron-vector certificate | `toLin_spectralRadius_eq_of_spectrum_modulusSet_isGreatest`, `toLin_spectralRadius_toReal_eq_of_spectrum_modulusSet_isGreatest`, `complexMatrix_toLin_spectralRadius_eq_of_isMaxComplexMatrixEigenvalueModulus`, `ch7_toLin_spectralRadius_eq_of_isComplexEigenvalueRadius`, `ch7_toLin_spectralRadius_toReal_eq_of_isComplexEigenvalueRadius`, `problem7_10a_product_toLin_spectralRadius_eq_of_positive_eigenvector`, `problem7_10b_abs_product_toLin_spectralRadius_eq_of_positive_eigenvector`, `problem7_10a_scaled_product_toLin_spectralRadius_eq_of_positive_eigenvector` | `LeanFpAnalysis/FP/Analysis/Norms.lean`; `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; unfolding Mathlib `spectralRadius`, the upper bound follows from the proved greatest spectrum modulus and monotonicity of `ENNReal.ofReal`, while the lower bound uses the attained spectral point. This closes the previous Banach-algebra value-representation gap for supplied positive Perron-vector certificates; it does not prove PF existence from irreducibility |
| Problem 7.10(a), Bauer infinity-norm least-value/minimum-attainment wrapper | `problem7_10a_scaledInfCondSet_isLeast_perron_of_positive_eigenvector`, `problem7_10a_positive_entries_scaledInfCondSet_isLeast_perron`, `problem7_10a_irreducible_products_scaledInfCondSet_isLeast_perron_of_nonzero_nonneg_eigenvector` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; the canonical source scaling is proved to be a member of the positive reciprocal value set, and the already proved pointwise lower bound makes `ρ` an `IsLeast` value. The irreducible-product wrapper first derives strict positivity from a supplied nonzero nonnegative eigenpair and Mathlib irreducibility, but still keeps PF eigenpair existence and spectral-radius identification open |
| Problem 7.10(b), Bauer `B = |A|`, `C = |A⁻¹|` absolute-value scaled-`κ∞` instantiation under a positive Perron-vector certificate | `ch7TwoSidedScale_absMatrix_eq`, `ch7_infNorm_twoSidedScale_absMatrix_eq`, `ch7TwoSidedScaledInfKappa`, `ch7TwoSidedScale_isLeftInverse`, `ch7TwoSidedScale_isRightInverse`, `ch7TwoSidedScale_isInverse`, `ch7TwoSidedScaledInfKappa_eq_kappaInf_of_inverse`, `ch7TwoSidedScaledInfKappa_eq_abs_scaledInfCond`, `problem7_10b_scaled_infKappa_ge_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_canonical_scaled_infKappa_eq_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_positive_abs_entries_canonical_scaled_infKappa_eq_perron` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; diagonal-scaling algebra transports a two-sided inverse certificate to `D₁AD₂`, the scaled product is proved equal to the repository `kappaInf` value for that scaled matrix, componentwise absolute values commute with nonnegative two-sided diagonal scaling, `infNorm_absMatrix` turns the actual scaled `κ∞` product into the Problem 7.10(a) product for `|A|` and `|A⁻¹|`, and the positive-Perron-certificate lower-bound/canonical-attainment theorems are reused without assuming Perron-Frobenius existence or spectral-radius identification |
| Problem 7.10(b), scaled `κ∞` `sInf = ρ` minimization under a positive Perron-vector certificate for `|A||A⁻¹|` | `ch7TwoSidedScaledInfKappaSet`, `ch7TwoSidedScaledInfKappa_mem_set`, `ch7TwoSidedScaledInfKappaSet_nonempty`, `ch7TwoSidedScaledInfKappaSet_bddBelow`, `problem7_10b_scaledInfKappaSet_sInf_eq_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_positive_abs_entries_scaledInfKappaSet_sInf_eq_perron` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; the value set ranges over the actual scaled `κ∞` products for inverse-compatible reciprocal scalings, the lower bound reduces every member to the absolute-value Bauer product, and the canonical scaling gives the matching upper bound. The proof uses only proved inverse transport and norm/absolute-value algebra, not a hidden spectral-radius theorem |
| Problem 7.10(b), scaled `κ∞` least-value/minimum-attainment wrapper | `problem7_10b_scaledInfKappaSet_isLeast_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_irreducible_products_scaledInfKappaSet_isLeast_perron`, `problem7_10b_irreducible_products_scaledInfKappaSet_isLeast_perron_of_nonzero_nonneg_eigenvector`, `problem7_10b_positive_abs_entries_scaledInfKappaSet_isLeast_perron` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; the lower-bound theorem applies to every inverse-compatible reciprocal scaling and the canonical absolute-value Bauer scaling supplies membership at `ρ`. The irreducible and positive-entry variants discharge the strict-positive side conditions through previously proved local irreducibility/positivity bridges, not through a hidden PF theorem |
| Problem 7.10(b)/(d), irreducible-products canonical scaled-`κ∞` and exact `sInf = ρ` wrappers | `problem7_10b_irreducible_products_canonical_scaled_infKappa_eq_perron`, `problem7_10b_irreducible_products_scaledInfKappaSet_sInf_eq_perron` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this continuation | Genuine Lean proof; the new wrappers compose `problem7_10d_abs_inverse_Cx_pos_of_irreducible_products` with the existing canonical and value-set Bauer theorems, so `|A⁻¹|x > 0` is proved from irreducibility of both `|A||A⁻¹|` and `|A⁻¹||A|` rather than assumed. The positive Perron-vector/eigenvalue certificate remains explicit, so this does not assert Perron-Frobenius existence or spectral-radius identification |
| Problem 7.10(a)/(b), irreducible-product Bauer wrappers from a nonzero nonnegative eigenvector certificate | `ch7_perronScalar_nonneg_of_nonzero_nonneg_eigenvector`, `ch7_perronScalar_pos_of_nonzero_nonneg_irreducible_eigenvector`, `ch7_nonzero_nonneg_irreducible_right_eigenvector_pos`, `problem7_10a_irreducible_products_canonical_scaled_infCond_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10a_irreducible_products_scaledInfCondSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10b_irreducible_products_canonical_scaled_infKappa_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10b_irreducible_products_scaledInfKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this continuation | Genuine Lean proof; a nonzero nonnegative eigenvector has a positive coordinate, nonnegative matrix-vector multiplication gives `ρ >= 0`, irreducibility supplies a positive matrix power and hence `ρ > 0`, and the existing support-propagation lemma proves `x > 0`. The Problem 7.10(a)/(b) wrappers then reuse the compiled positive-certificate Bauer lower-bound/canonical/`sInf` equalities. The remaining gap is only source-level existence of the eigenpair and spectral-radius identification, not vector positivity |
| Problem 7.10(b)/(d), positive-entry product irreducibility side condition | `ch7_matrix_isPrimitive_of_pos_entries`, `ch7_matrix_isIrreducible_of_pos_entries`, `ch7_matMul_pos_of_pos`, `ch7_bauer_positive_products_irreducible`, `problem7_10b_positive_abs_entries_products_irreducible` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; a strictly positive finite matrix is proved primitive and therefore irreducible in Mathlib, finite positivity of products is proved by `Finset.sum_pos`, and the source absolute-value hypotheses imply irreducibility of both `|A||A⁻¹|` and `|A⁻¹||A|`. This closes only the irreducibility side condition, not Perron-Frobenius existence or spectral-radius identification |
| Problem 7.10(d), strict-eigenvalue side condition and `Cx > 0` transfer from a positive `BC` entry | `ch7_perronScalar_pos_of_nonneg_eigenvector_entry_pos`, `problem7_10d_Cx_pos_of_irreducible_CB_of_positive_BC_entry` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; finite positivity of a row sum shows a nonnegative matrix with a positive entry and a strictly positive right eigenvector has positive eigenvalue, and the existing irreducible `CB` transfer then proves `Cx > 0`. The proof keeps the positive Perron-vector certificate explicit and does not assume Perron-Frobenius existence or spectral-radius identification |
| Problem 7.10(d), source-shaped irreducible-product `Cx > 0` transfer | `ch7_perronScalar_pos_of_nonneg_irreducible_eigenvector`, `problem7_10d_Cx_pos_of_irreducible_BC_CB`, `problem7_10d_abs_inverse_Cx_pos_of_irreducible_products` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; Mathlib irreducibility supplies a positive matrix power, the proved power-eigenvector lemma turns that into `ρ^k * x_i > 0`, nonnegativity gives `ρ > 0`, and the existing irreducible-`CB` positivity propagation proves `Cx > 0`. The abs-value specialization applies this directly to `B = |A|`, `C = |A⁻¹|`; it still assumes the positive Perron-vector certificate and does not prove PF existence or spectral-radius identification |
| Problem 7.10(e), one-norm Bauer transpose branch under a positive Perron-vector certificate | `ch7TwoSidedScaledOneCond`, `ch7TwoSidedScaledOneCond_eq_transpose_infCond`, `problem7_10e_scaled_oneCond_ge_perron_of_transpose_positive_eigenvector`, `problem7_10e_canonical_scaled_oneCond_eq_perron_of_transpose_positive_eigenvector`, `problem7_10e_positive_entries_canonical_scaled_oneCond_eq_perron_of_transpose`, `ch7TwoSidedScaledOneKappa`, `ch7TwoSidedScaledOneKappa_eq_abs_scaledOneCond`, `problem7_10e_scaled_oneKappa_ge_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_canonical_scaled_oneKappa_eq_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_positive_abs_entries_canonical_scaled_oneKappa_eq_perron_of_transpose` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; `‖M‖₁ = ‖Mᵀ‖∞` reduces the two-sided one-norm product to the proved infinity-norm Bauer core for `Bᵀ,Cᵀ`, and the actual scaled `κ₁` product is proved equal to the absolute-value one-norm product for `|A|, |A⁻¹|` under nonnegative reciprocal diagonal scalings. The theorem surface keeps the transpose-side Perron-vector certificate explicit and does not assume Perron-Frobenius existence or spectral-radius identification |
| Problem 7.10(e), one-norm scaled `κ₁` `sInf = ρ` minimization under a transpose-side positive Perron-vector certificate | `ch7TwoSidedScaledOneKappaSet`, `ch7TwoSidedScaledOneKappa_mem_set`, `ch7TwoSidedScaledOneKappaSet_nonempty`, `ch7TwoSidedScaledOneKappaSet_bddBelow`, `problem7_10e_scaledOneKappaSet_sInf_eq_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_positive_abs_entries_scaledOneKappaSet_sInf_eq_perron_of_transpose` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; transpose converts the one-norm scaled condition product to the infinity-norm Bauer product for transposed absolute-value factors, `le_csInf` supplies the universal lower bound, and the canonical transpose-side scaling supplies the matching `csInf_le` upper bound. The remaining 2-norm/global Bauer statement still requires PF/spectral scaling existence |
| Problem 7.10(e), one-norm scaled `κ₁` least-value/minimum-attainment wrapper | `problem7_10e_scaledOneKappaSet_isLeast_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_positive_abs_entries_scaledOneKappaSet_isLeast_perron_of_transpose`, `problem7_10e_irreducible_transpose_products_scaledOneKappaSet_isLeast_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_products_scaledOneKappaSet_isLeast_perron_of_nonzero_nonneg_eigenvector` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; the canonical transpose-side Bauer scaling is proved to attain the one-norm value set's least value under the explicit certificate. Source-product irreducibility is transported to transpose-product irreducibility before applying the compiled one-norm theorem, so the remaining blocker is only PF/spectral/common-scaling existence |
| Problem 7.10(e), irreducible transpose-product one-norm wrappers from a nonzero nonnegative eigenvector certificate | `problem7_10e_irreducible_transpose_products_canonical_scaled_oneCond_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_transpose_products_canonical_scaled_oneKappa_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_transpose_products_scaledOneKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this continuation | Genuine Lean proof; irreducibility of `BᵀCᵀ` turns the supplied nonzero nonnegative transpose-side eigenvector into a strictly positive vector, irreducibility of `CᵀBᵀ` and the existing Problem 7.10(d) transfer prove `Cᵀy > 0`, and the wrappers reuse the compiled positive-certificate one-norm canonical and `sInf = ρ` theorems. The remaining gap is PF eigenpair existence and spectral-radius identification, not the strict-positivity side conditions |
| Problem 7.10(e), one-norm wrappers from source-shaped original-product irreducibility | `ch7_matrix_of_matTranspose`, `ch7_irreducible_matTranspose`, `ch7_irreducible_transpose_product_of_irreducible_product`, `problem7_10e_irreducible_products_canonical_scaled_oneCond_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_products_canonical_scaled_oneKappa_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_products_scaledOneKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; the repository function-level transpose is identified with Mathlib `Matrix.transpose`, Mathlib's `Matrix.IsIrreducible.transpose` transports irreducibility, and `matTranspose_matMul` rewrites `(BC)ᵀ` as `CᵀBᵀ`. The final wrappers therefore consume the original source hypotheses `BC` and `CB` irreducible and derive the transpose-product hypotheses needed by the already proved one-norm branch. The remaining gap is still PF eigenpair existence and spectral-radius identification, not product-orientation irreducibility |
| Problem 7.10(c)/(e), `CB(Cx)` algebra plus fixed-scaling 2-norm interpolation and conditional `sInf` upper-bound packaging | `ch7_bauer_Cx_eigenvector_CB`, `ch7_complexMatrixOneNorm_realRectToCMatrix_le_oneNorm`, `ch7_complexMatrixInfNorm_realRectToCMatrix_le_infNorm`, `problem7_10e_complexMatrixOp2_realRectToCMatrix_le_sqrt_one_mul_inf`, `ch7TwoSidedScaledOp2Kappa`, `problem7_10e_scaled_op2Kappa_le_sqrt_oneKappa_mul_infKappa`, `problem7_10e_scaled_op2Kappa_le_of_one_inf_bounds`, `ch7TwoSidedScaledOp2Kappa_mem_set`, `problem7_10e_twoSidedScaledOp2Kappa_sInf_le_of_one_inf_bounds` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; `CB(Cx) = ρ(Cx)` follows by associativity of finite matrix-vector multiplication, the integrated finite complex `p`-norm interpolation theorem is specialized to `p = 2`, real row/column-sum bridges compare the complexified real matrix norms to repository `oneNorm`/`infNorm`, the fixed-scaling condition-product theorem proves `κ₂ <= sqrt(κ₁κ∞)` and then `κ₂ <= ρ` whenever the same scaling has both `κ₁` and `κ∞` products bounded by nonnegative `ρ`, and the value-set membership plus `csInf_le` package this as `sInf <= ρ` for any supplied admissible common scaling. The full source `inf κ₂ <= ρ(|A||A⁻¹|)` still needs a Perron-Frobenius/spectral-radius proof that such a compatible scaling exists at the source spectral-radius value |
| Problem 7.10(e), op-2 two-sided scaling value-set lower-bound infrastructure | `ch7TwoSidedScaledOp2KappaSet_bddBelow`, `ch7TwoSidedScaledOp2KappaSet_sInf_nonneg` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; every admissible op-2 two-sided scaling value is a product of exact complexified real operator norms, so zero is a lower bound and the `sInf` is nonnegative. This factors the lower-bound proof used by the conditional op-2 `sInf` theorem into reusable declarations and does not assert the missing Perron-Frobenius/spectral-radius common scaling |
| Theorem 7.5 / Corollary 7.6 / Problem 7.10, reusable scaling value-set nonnegative-infimum infrastructure | `ch7Op2LeftScaledCondSet_sInf_nonneg`, `ch7SymmetricOp2ScaledCondSet_sInf_nonneg`, `ch7TwoSidedScaledInfCondSet_sInf_nonneg`, `ch7TwoSidedScaledInfKappaSet_sInf_nonneg`, `ch7TwoSidedScaledOneKappaSet_sInf_nonneg` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved in this pass | Genuine Lean proof; each declaration combines the already proved identity-scaling nonempty witness with the fact that every admissible value is a product of matrix norms, then applies `le_csInf`. These lemmas close local lower-bound infrastructure for the p=2 left-scaling, symmetric two-sided op-2, Bauer infinity-product, scaled-`κ∞`, and scaled-`κ₁` value sets without adding any theorem-equivalent Perron-Frobenius, pseudoinverse, or minimizer-attainment assumption |
| Problem 7.15, reciprocal scaling invariance of `A ∘ A^{-T}`, Horn-Johnson operator-2 certificate, scaled inverse-partner bound, exact op-2 infimum lower bound, conditional equality/least-value attainability certificates, and nonsingular diagonal attainability | `ch7HadamardProduct`, `ch7_matTranspose_twoSidedScale`, `ch7HadamardProduct_twoSidedScale_transpose_inverse_eq`, `problem7_15_twoSidedScale_hadamard_transpose_inverse_invariant`, `opNorm2Le_transpose`, `problem7_15_transpose_inverse_partner_opNorm2Le`, `frobNormRect_diagMatrix`, `vecNorm2_diagonal_le_frobNormRect`, `matMulVec_hadamard_eq_diag_rectMatMul_diag_transpose`, `opNorm2Le_hadamard`, `complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le`, `opNorm2Le_complexMatrixOp2_realRectToCMatrix`, `problem7_15_hornJohnson_hadamard_opNorm2Le`, `problem7_15_scaled_inverse_hadamard_opNorm2Le`, `ch7TwoSidedScaledOp2KappaSet`, `ch7TwoSidedScaledOp2KappaSet_nonempty`, `problem7_15_hadamard_op2_le_twoSidedScaledOp2Kappa_mem`, `problem7_15_twoSidedScaledOp2Kappa_sInf_ge_hadamard_op2`, `problem7_15_twoSidedScaledOp2Kappa_sInf_ge_hadamard_op2_of_inverse`, `problem7_15_twoSidedScaledOp2Kappa_sInf_eq_hadamard_op2_of_mem`, `problem7_15_twoSidedScaledOp2Kappa_isLeast_hadamard_op2_of_mem`, `problem7_15_twoSidedScaledOp2Kappa_sInf_eq_hadamard_op2_of_attaining_scaling`, `problem7_15_twoSidedScaledOp2Kappa_isLeast_hadamard_op2_of_attaining_scaling`, `problem7_15_complexMatrixOp2_realRectToCMatrix_orthogonal_eq_one`, `problem7_15_ch7TwoSidedScale_diagMatrix_eq`, `problem7_15_hadamard_diag_inverse_transpose_eq_idMatrix`, `problem7_15_diagonal_hadamard_op2_eq_one`, `problem7_15_diagonal_attaining_scaling_eq_hadamard_op2`, `problem7_15_diagonal_twoSidedScaledOp2Kappa_sInf_eq_one`, `problem7_15_diagonal_twoSidedScaledOp2Kappa_isLeast_one` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean`, `LeanFpAnalysis/FP/Analysis/Norms.lean` | Newly proved in this pass and earlier Problem 7.15 continuations | Genuine Lean proof; entrywise algebra shows `(D₁AD₂) ∘ (D₂⁻¹A_invD₁⁻¹)^T = A ∘ A_inv^T` for reciprocal diagonal pairs, Cauchy-duality proves that real Euclidean operator-2 certificates are preserved by transpose, the Horn-Johnson inequality is proved by rewriting `(A ∘ B)x` as the diagonal of `A * diag(x) * B^T`, and the exact `complexMatrixOp2` bridge turns the certificate bound into the source `sInf` lower bound over positive two-sided scalings. The attainability statement is formalized conditionally, and the Appendix A.7.15 nonsingular diagonal case is now closed unconditionally by scaling to orthogonal sign-diagonal factors, proving `||A ∘ A^{-T}||₂ = 1`, `sInf = 1`, and `IsLeast 1` |
| Problem 7.6(a), row-wise relative-data condition comparison | `ch7RowwiseRelativeToleranceMatrix`, `ch7RowwiseDataCondAtSolutionInf`, `ch7_rowwiseDataForwardBound_lower`, `ch7_rowwiseDataForwardBound_upper`, `problem7_6a_rowwise_data_condition_bounds` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; the row-wise tolerance model is expanded directly and bounded using `|Ax| ≤ |A||x|`, vector 1-norm domination, finite-sup comparison, and the existing `condSkeel` definition |
| Problem 7.6(b), columnwise relative-data condition comparison | `ch7ColumnwiseRelativeToleranceMatrix`, `ch7AbsMatrixAbsVecOneNorm`, `ch7ColumnwiseDataCondAtSolutionInf`, `ch7_columnwiseDataForwardBound_lower`, `ch7_columnwiseDataForwardBound_upper`, `problem7_6b_columnwise_data_condition_bounds` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; the columnwise tolerance model is expanded directly and bounded using `‖Ax‖₁ ≤ ‖ |A| |x| ‖₁`, finite row-sum comparison with `‖A⁻¹‖∞`, and the existing `ch7CondEFAtSolutionInf` definition |
| Problem 7.9 finite first-order componentwise and normwise scalar-output formulas plus `χ ≥ 1` lower-bound specializations | `ch7LinearFunctional`, `ch7Problem79AdjointWeight`, `ch7Problem79FirstOrderChange`, `ch7Problem79ComponentwiseSensitivity`, `ch7Problem79LinearizedCond`, `ch7Problem79LinearizedRelativeChange`, `ch7Problem79AttainingDeltaA`, `ch7Problem79AttainingDeltaB`, `problem7_9_linearized_componentwise_functional_formula`, `ch7Problem79_adjointWeight_mul_vec_eq_linearFunctional_matMulVec`, `ch7Problem79_linearFunctional_eq_adjointWeight_mul_Ax`, `ch7Problem79ComponentwiseSensitivity_ge_abs_functional_of_abs_matrix`, `ch7Problem79ComponentwiseSensitivity_ge_abs_functional_of_abs_rhs`, `problem7_9_linearized_componentwise_functional_ge_one_of_abs_matrix`, `problem7_9_linearized_componentwise_functional_ge_one_of_abs_rhs`, `ch7Problem79NormwiseSensitivity`, `ch7Problem79NormwiseLinearizedCond`, `ch7Problem79NormwiseAttainingDeltaA`, `ch7Problem79NormwiseAttainingDeltaB`, `problem7_9_linearized_normwise_functional_formula` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; finite triangle inequalities prove the componentwise upper bound, an explicit source sign perturbation attains the componentwise numerator, the adjoint-weight identity plus `|Ax| ≤ |A||x|` proves the finite `χ ≥ 1` lower-bound specializations, and Cauchy plus `opNorm2Le` proves the normwise upper bound while a rank-one perturbation attains the finite normwise numerator without assuming the nonlinear `lim sup` result |
| Problem 7.9 nonlinear componentwise scalar-output condition number | `Ch7Problem79ComponentwiseLinearizedRadiusSet`, `ch7Problem79ComponentwiseLinearizedRadiusSup`, `problem7_9_componentwise_linearized_radiusSup_tendsto_formula`, `ch7Problem79PerturbedSolutionWithInverse`, `ch7Problem79ExactScalarRelativeChange`, `ch7Problem79ComponentwiseExactRemainderBound`, `problem7_9_exact_componentwise_relative_change_le_linearized_plus_quadratic`, `problem7_9_exact_componentwise_relative_change_ge_linearized_minus_quadratic`, `Ch7Problem79ComponentwiseExactRadiusSet`, `ch7Problem79ComponentwiseExactRadiusSup`, `ch7Problem79ComponentwiseExactRadiusSet_value_le`, `exists_ch7Problem79ComponentwiseExactRadiusSet_lower_witness`, `problem7_9_componentwise_exact_radiusSup_tendsto_linearized`, `problem7_9_componentwise_exact_condition_of_positive_radii` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; finite first-order radius suprema are exact for every positive radius, the nonlinear perturbed solution is built from the local inverse candidate, finite matrix/vector algebra proves an exact first-order-plus-remainder scalar decomposition, a conservative quadratic envelope bounds the exact remainder, and the source-radius supremum is squeezed to the componentwise formula without assuming the nonlinear condition-number result |
| Problem 7.9 nonlinear normwise scalar-output condition number | `ch7Problem79NormwiseConstantEnvelopeMatrix`, `ch7Problem79_normwise_deltaA_componentwise_bound`, `ch7Problem79_normwise_deltaB_componentwise_bound`, `ch7Problem79NormwiseExactRemainderBound`, `problem7_9_exact_normwise_relative_change_le_linearized_plus_quadratic`, `problem7_9_exact_normwise_relative_change_ge_linearized_minus_quadratic`, `Ch7Problem79NormwiseExactRadiusSet`, `ch7Problem79NormwiseExactRadiusSup`, `ch7Problem79NormwiseExactRadiusSet_value_le`, `exists_ch7Problem79NormwiseExactRadiusSet_lower_witness`, `problem7_9_normwise_exact_radiusSup_tendsto_linearized`, `problem7_9_normwise_exact_condition_of_positive_radii` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; basis-vector testing derives entrywise control from `opNorm2Le`, vector-coordinate bounds derive the RHS componentwise envelope from `‖Δb‖₂`, the existing local inverse candidate supplies the exact perturbed solution for small radii, and a normwise quadratic squeeze proves the source-radius supremum tends to `‖c^T A⁻¹‖₂(‖f‖₂+‖E‖₂‖x‖₂)/|c^T x|` without assuming the nonlinear condition-number theorem |
| Problem 7.11 / Appendix A.11, first-order inverse componentwise formula | `ch7InverseLinearizedEntry`, `ch7InverseCompSensitivityEntry`, `ch7InverseCompSensitivityRatio`, `ch7InverseComponentwiseLinearizedCond`, `ch7InverseLinearizedRelativeChangeMax`, `ch7Problem711AttainingDelta`, `problem7_11_linearized_inverse_componentwise_upper_and_sign_attainment`, `problem7_11_linearized_inverse_componentwise_formula` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; finite triangle inequalities prove the upper bound, and the source sign perturbation `ΔA = εD₁ED₂` attains a maximizing entry under nonnegative `E` and nonzero inverse entries |
| Problem 7.11 exact inverse perturbation first-order/remainder identity | `ch7InverseQuadraticRemainderEntry`, `ch7_inversePerturbation_decomposition`, `problem7_11_exact_inverse_firstOrder_remainder_identity` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; finite matrix algebra derives the exact entrywise identity from left inverse of `A` and right inverse of `A + ΔA`, with the quadratic remainder exposed rather than assumed |
| Problem 7.11 exact finite quadratic-remainder upper/lower envelopes, finite lower witness, finite-radius reduction, conditional asymptotic vanishing, exact-to-linearized filter bridge, and entrywise-/infinity-norm inverse-bound discharges | `ch7InverseFirstProductSensitivity`, `ch7InverseQuadraticRemainderSensitivityEntry`, `ch7InverseExactRelativeChangeMax`, `ch7InverseQuadraticRemainderRelativeMax`, `ch7InverseQuadraticRemainderRelativeMax_nonneg`, `ch7InverseQuadraticRemainderRelativeMaxEntryBound`, `ch7InverseQuadraticRemainderRelativeMaxEntryBound_nonneg`, `ch7InverseQuadraticRemainderSensitivityEntry_le_of_entry_bound`, `ch7InverseQuadraticRemainderRelativeMax_le_of_entry_bound`, `ch7InverseQuadraticRemainderRelativeMax_abs_le_of_entry_bound`, `ch7_abs_entry_le_infNorm`, `ch7InverseQuadraticRemainderRelativeMax_le_of_infNorm_bound`, `ch7InverseQuadraticRemainderRelativeMax_abs_le_of_infNorm_bound`, `ch7InverseQuadraticRemainderEntry_abs_le`, `problem7_11_exact_inverse_relative_entry_le_linearized_plus_quadratic`, `problem7_11_exact_inverse_relative_entry_ge_linearized_minus_quadratic`, `problem7_11_exact_inverse_relative_change_max_ge_linearized_entry_minus_quadratic`, `problem7_11_exact_inverse_relative_change_max_le_condition_plus_quadratic`, `problem7_11_exact_inverse_relative_change_max_le_linearized_max_plus_quadratic`, `problem7_11_exact_inverse_relative_change_max_ge_linearized_max_minus_quadratic`, `problem7_11_exact_inverse_relative_change_max_le_condition_plus_radius_bound`, `problem7_11_exact_inverse_relative_change_max_ge_condition_minus_quadratic_of_linearized_attainer`, `problem7_11_exists_exact_inverse_relative_change_max_lower_witness`, `problem7_11_quadratic_remainder_relative_scaled_tendsto_zero_of_eventually_bounded`, `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_quadratic_bound`, `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_eventually_entry_bound`, `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_eventually_infNorm_bound` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; finite matrix-product monotonicity controls the exact quadratic remainder, lower-envelope lemmas derive `εµ'_lin - ε²R`, the lower-witness theorem constructs an admissible perturbation and finite attaining entry, the bounded-radius theorem derives `ε(µ'_lin + δC)`, the filter theorem proves `εR → 0` under explicit eventual boundedness, the squeeze theorem proves exact quotient convergence from linearized quotient convergence, the entry-bound theorem derives the bounded-remainder premise from eventual entrywise boundedness of certified perturbed inverses, and the infinity-norm theorem discharges that entrywise premise from `infNorm` boundedness without assuming the remaining source `lim sup` packaging |
| Problem 7.11 local inverse-family existence and boundedness for exact-to-linearized bridge | `ch7MatAddId`, `ch7_isRightInverse_of_isLeftInverse`, `ch7_matAdd_id_abs_solution_bound_of_abs_infNorm_bound`, `ch7_matAdd_id_det_ne_zero_of_abs_infNorm_bound`, `ch7_nonsingInv_matAdd_id_entry_abs_le_of_abs_infNorm_bound`, `ch7_nonsingInv_matAdd_id_infNorm_le_of_abs_infNorm_bound`, `ch7Problem711PerturbedInverseCandidate`, `problem7_11_perturbed_inverse_candidate_right_inverse_of_abs_left_product_bound`, `problem7_11_perturbed_inverse_candidate_infNorm_bound_of_abs_left_product_bound`, `ch7_abs_left_product_infNorm_le_of_componentwise_bound`, `problem7_11_eventually_abs_left_product_infNormBound_half_of_componentwise_tendsto_zero`, `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_eventually_abs_left_product_bound`, `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_componentwise_tendsto_zero` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; finite matrix algebra proves `I + C` is nonsingular under `‖|C|‖∞ ≤ c < 1`, constructs the candidate `(I + A⁻¹ΔA)⁻¹A⁻¹`, proves it is a right inverse of `A + ΔA`, bounds its `∞`-norm, derives eventual half-contraction from `|ΔA| ≤ εE` and `ε → 0`, and closes the exact-to-linearized quotient bridge for that constructed inverse family |
| Problem 7.11 nonlinear source-radius `lim sup`/supremum wrapper for `µ'_E(A)` | `Ch7InverseComponentwiseRadiusSet`, `ch7InverseComponentwiseRadiusSup`, `IsCh7InverseComponentwiseRadiusLimitValue`, `IsCh7InverseComponentwiseCondValue`, `ch7Problem711LocalInverseInfNormBound`, `ch7InverseComponentwiseRadiusRemainderBound`, `ch7InverseComponentwiseRadiusSet_value_le`, `exists_ch7InverseComponentwiseRadiusSet_lower_witness`, `problem7_11_inverse_componentwise_radiusSup_tendsto_linearized`, `problem7_11_inverse_componentwise_condition_of_positive_radii` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proof; the feasible set ranges over exact relative inverse changes produced by componentwise-admissible perturbations, the finite upper and lower envelopes squeeze the radius supremum between `µ'_lin ± ρC`, and the shrinking-radius theorem proves convergence to the finite linearized condition value without assuming a nonlinear condition-number theorem |
| Problem 7.13 sparse computed residual row with row-support counts | `ch7SparseResidual`, `ch7SparseComputedResidualSafetyTerm`, `ch7SparseComputedResidualImage`, `problem7_13_sparse_residual_error`, `problem7_13_componentwise_bound`, `problem7_13_relative_infNorm_bound` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Newly proved | Genuine Lean proofs; the support-compressed sparse matvec/residual model proves the Appendix A.12 `γ_(w_i+1)` bound without placeholder assumptions or theorem-equivalent hypotheses |

### 2. Formalized End-To-End While Relying On Previous-Split Results

| Source label/name | Lean declaration(s) | File path | Previous split result/contract used | Direct or indirect previous-split reliance | Proof chain |
| --- | --- | --- | --- | --- | --- |
| Theorem 7.1, arbitrary subordinate-norm Rigal-Gaches wrapper | `theorem7_1_subordinate_necessary`, `theorem7_1_subordinate_sufficient`, `theorem7_1_subordinate` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated Split 1 generic norm and mixed-subordinate API: `IsComplexVectorNorm`, `MixedSubordinateMatrixBound`, `IsMixedSubordinateMatrixNormValue` | Direct | Genuine Lean proofs; no placeholder assumptions, local axioms, or certificate-only wrapper |
| Equation (7.1), arbitrary subordinate-norm feasibility surface | `theorem7_1_subordinate_sufficient`, `theorem7_1_subordinate` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Same as Theorem 7.1 row | Direct | Genuine Lean proof; closed by the existential constructive wrapper |
| Equation (7.2), arbitrary subordinate-norm residual formula surface | `theorem7_1_subordinate_necessary`, `theorem7_1_subordinate` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Same as Theorem 7.1 row | Direct | Genuine Lean proof; lower-bound and equivalence surfaces are formalized |
| Equation (7.3), arbitrary subordinate-norm attaining perturbations | `eq_7_3_subordinate_attaining_perturbations` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated Split 1 dual-functional/rank-one API: `IsDualFunctionalNormValue`, `exists_dualFunctionalNormValue_one_of_pos_vector`, `rankOneCMatrixFromFunctional`, `complexMatrixVecMul_rankOneCMatrixFromFunctional` | Direct | Genuine Lean proof; explicit source-shaped perturbations are constructed and verified |
| Theorem 7.2, arbitrary subordinate-norm wrapper | `theorem7_2_subordinate_forward_error_bound` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated Split 1 mixed subordinate norm API: `IsComplexVectorNorm`, `MixedSubordinateMatrixBound`, `IsMixedSubordinateMatrixNormValue`, `IsComplexMatrixLeftInverse` | Direct | Genuine Lean proof; no hypothesis-only wrapper or placeholder |
| Equation (7.4), arbitrary subordinate-norm form | `theorem7_2_subordinate_forward_error_bound` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Same as Theorem 7.2 row | Direct | Genuine Lean proof; same declaration packages the source equation |
| Equation (7.5), generic normwise condition number | `Ch7NormwiseCondEFRadiusSet`, `ch7NormwiseCondEFRadiusSup`, `IsCh7NormwiseCondEFRadiusLimitValue`, `IsCh7NormwiseCondEFValue`, `eq_7_5_subordinate_conditionNumberRadiusLimitValue_of_positive_radii`, `eq_7_5_subordinate_conditionNumber_of_positive_radii` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated Split 1 generic norm, mixed subordinate, dual-functional, rank-one, norm-attainment, and inverse APIs | Direct | Genuine Lean proof; the source radius-supremum model, upper envelope, and sharp lower witness are all formalized with no placeholder assumptions |
| Equation (7.26), relative distance to singularity | `eq_7_26_relative_distance_to_singularity_eq_inv_condition_number` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated Split 1 distance/condition API: `complexMatrix_relativeSingularDistance_min_eq_inv_conditionNumberProduct`, `IsMixedConditionNumberProductValue`, and `IsMinimumMixedRelativeSingularDistance` | Direct | Genuine Lean proof; the wrapper reuses the proved Gastinel-Kahan mixed relative singular-distance theorem and exposes the source norm-value, positivity, and two-sided inverse hypotheses without a local placeholder |
| Theorem 7.4, arbitrary absolute-norm wrapper | `theorem7_4_absolute_forward_error_bound` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated Split 1 absolute/monotone norm API and mixed subordinate matrix values: `IsAbsoluteComplexVectorNorm`, `absolute_norm_iff_monotone_norm`, `IsMixedSubordinateMatrixNormValue`, `IsComplexMatrixLeftInverse`, `complexMatrixVecMul_componentwiseAbsLe_absMatrix` | Direct | Genuine Lean proof; the source denominator and `|A⁻¹|(|E||x|+|f|)` image are proved, not assumed |
| Equation (7.10), arbitrary absolute-norm form | `theorem7_4_absolute_forward_error_bound` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Same as Theorem 7.4 row | Direct | Genuine Lean proof; closed by the same source-shaped wrapper |
| Problem 7.2, arbitrary subordinate-norm lower/upper/scaled inequalities | `problem7_2_subordinate_residual_lower`, `problem7_2_subordinate_residual_upper`, `problem7_2_subordinate_scaled_lower`, `problem7_2_subordinate_scaled_upper` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated Split 1 mixed subordinate norm and matrix-inverse APIs | Direct | Genuine Lean proofs; no theorem-equivalent assumptions |
| Problem 7.7 arbitrary subordinate-norm eta comparison | `problem7_7_subordinate_abs_rhs_feasible_of_zero_rhs_feasible`, `problem7_7_subordinate_abs_rhs_to_zero_rhs_residual_bound`, `problem7_7_subordinate_zero_rhs_feasible_of_abs_rhs_feasible` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated Split 1 generic norm and mixed-subordinate API: `IsComplexVectorNorm`, `MixedSubordinateMatrixBound`, `IsMixedSubordinateMatrixNormValue` | Direct | Genuine Lean proofs; the easy monotonicity and the nontrivial `2η/(1-η)` enlargement are both formalized without placeholder assumptions |
| Equation (7.12), Skeel infinity-norm global condition number | `ch7CondEFGlobalInf`, `ch7SkeelGlobalCondInf`, `ch7SkeelCondAtSolutionInf_le_condSkeel`, `eq_7_12_skeel_global_conditionNumber_eq_condSkeel` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated infinity-norm and Skeel-condition surface: `infNormVec`, `abs_le_infNormVec`, `condSkeel`, `ch7SkeelCondAtOnes_eq_condSkeel` | Direct | Genuine Lean proof; no unproved previous-split hypothesis or local duplicate foundation |
| Prose after (7.14), factor-2 comparison for `f = |b| = |Ax|` | `ch7ComponentwiseDataCondAtSolutionInf`, `ch7SkeelCondAtSolutionInf_le_componentwiseDataCondAtSolutionInf`, `ch7ComponentwiseDataCondAtSolutionInf_le_two_mul_skeelCondAtSolutionInf` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated matrix/vector infinity-norm and matrix-vector multiplication surface | Direct | Genuine Lean proof; no theorem-equivalent assumption or wrapper-only placeholder |
| Appendix A.3 / equations (7.15)-(7.16), row-equilibrated scaling package | `problem7_3_rowEquilibrated_scaling_condition_eq`, `problem7_3_rowEquilibrated_lower_bound`, `eq_7_16_rowEquilibrated_bounds`, `eq_7_15_positive_rowScaling_sInf_eq_condSkeel_of_right_inverse` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated matrix infinity norm, `diagMatrix`, `matMul_diagMatrix_left/right`, `infNorm_matMul_le`, `condSkeel`, and `kappaInf` surfaces | Direct | Genuine Lean proof; the positive-row-scaling infimum theorem constructs the row-equilibrator from reciprocal row one-norms under a right-inverse certificate |
| Problem 7.4, unit-diagonal symmetric PSD scaled-factor condition bounds | `problem7_4_abs_entry_le_one_of_finitePSD_diag_one`, `problem7_4_unitDiagonal_entryBound_condition_bounds`, `problem7_4_unitDiagonal_finitePSD_condition_bounds` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated finite quadratic-form, basis-vector, infinity-norm, Skeel-condition, and `κ∞` APIs | Direct | Genuine Lean proof; no unresolved previous-split dependency or local duplicate foundation |
| Equations (7.19)-(7.22), row/column-equilibration dependencies | `ch7RectColumnLpNormOfReal`, `ch7RectColumnLpNormOfReal_nonneg`, `eq_7_20_column_lpNorm_le_matrixLpNormOfReal`, `ch7_complexVecLpNorm_realRect_matVec_le_sum_column_lpNorm`, `eq_7_20_matrixLpNormOfReal_le_card_rpow_mul_column_bound`, `ch7ColumnEquilibratingScaleLpOfReal`, `ch7RectColumnLpNormOfReal_rightScale`, `ch7RectColumnLpNormOfReal_rightScale_equilibrating`, `eq_7_21_matrixLpNormOfReal_column_equilibrated`, `eq_7_20_column_norm_le_of_rectOpNorm2Le`, `ch7RectColumnNorm2_le_frobNormRect`, `ch7_frobNormRect_le_sqrt_card_mul_column_bound`, `eq_7_20_rectOpNorm2Le_of_column_bound`, `eq_7_21_rectOpNorm2Le_column_equilibrated`, `eq_7_21_oneNormRect_column_equilibrated`, `eq_7_22_oneNormRect_inverseSide_bound`, `theorem7_5_p1_column_equilibration_le_right_scaling`, `eq_7_19_infNormRect_row_equilibrated`, `eq_7_19_infNormRect_inverseSide_bound`, `theorem7_5_pinf_row_equilibration_le_left_scaling` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated rectangular Euclidean/Frobenius/operator APIs plus finite `p`-/1-/infinity-norm row/column-sum APIs: `complexVecLpNorm`, `complexMatrixLpNormOfReal`, `IsComplexVectorNorm.sum_le`, `complexVecOneNorm_le_card_rpow_mul_complexVecLpNorm`, `vecNorm2`, `frobNormRect`, `rectMatMulVec`, `rectOpNorm2Le`, `rectOpNorm2Le_of_frobNormRect_le`, `basisVec`, `oneNormRect`, `infNormRect`, `col_sum_le_oneNormRect`, `oneNormRect_le_of_col_sum_le`, `row_sum_le_infNormRect`, and `infNormRect_le_of_row_sum_le` | Direct | Genuine Lean proof; the finite-real `p` `(7.20)` lower and upper column-bound statements are proved through the local least-bound matrix `p`-norm API and the vector `1`-to-`p` comparison, and the finite-real `p` `(7.21)` column-equilibrated bound is proved from the reciprocal scale and the same `(7.20)` upper-bound theorem. The imported dependencies are compiled norm and finite-vector/matrix facts, not unproved hypotheses. The `p = 1` and `p = ∞` theorems fix the inverse-side matrix explicitly and do not assert Moore-Penrose existence |
| Equation (7.19), finite-real conjugate-row proof-route specialization | `ch7RectRowDualLpNormOfReal`, `ch7RowDualEquilibratingScaleLpOfReal`, `eq_7_19_matrixLpNormOfReal_dual_row_equilibrated`, `eq_7_19_matrixLpNormOfReal_dual_row_inverseSide_bound`, `ch7LpLeftScaledCondOfReal`, `ch7LpLeftScaledCondSetOfReal`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_left_scaling`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated finite `Lp`, Holder-conjugate row-dual, matrix-norm, diagonal-scaling, and `sInf` APIs: `complexVecLpNorm`, `complexMatrixLpNormOfReal`, `complexMatrixLpNormOfReal_rowDualMax_bounds`, `complexMatrixRowDualMaxNorm_le_of_row_le`, `complexMatrixRowDualMaxNorm_row_le_of_nonneg`, `IsComplexVectorNorm.smul`, `isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound`, `hasComplexMatrixLpBound_of_nonneg_mixedSubordinateMatrixBound`, `le_csInf`, and `sInf` | Direct | Genuine Lean proof; integrated row-dual finite `Lp` bounds prove the equilibrated row norm estimate, the local diagonal multiplier proves the inverse-side condition-product inequality, and the `sInf` wrapper ranges over proved reciprocal diagonal scalings rather than assuming a minimum or Moore-Penrose theorem |
| Theorem 7.7, Stewart-Sun Frobenius right-scaling minimizer | `theorem7_7_frobenius_right_scaling_lower_bound`, `theorem7_7_stewart_sun_frobenius_scaling`, `theorem7_7_stewart_sun_frobenius_scaling_of_left_inverse` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated finite Frobenius/Euclidean norm, diagonal-matrix, matrix multiplication, Cauchy, and inverse-certificate APIs: `frobNorm`, `vecNorm2`, `matMul_diagMatrix_left/right`, `abs_vecInnerProduct_le_vecNorm2_mul`, `IsLeftInverse`, and `vecNorm2_eq_zero_iff` | Direct | Genuine Lean proof; the previous-split/repository dependencies are compiled theorems, not unproved hypotheses, and the source nonsingularity side condition is consumed through `IsLeftInverse` |
| Problem 7.10(a), Bauer two-sided scaling algebra under a positive Perron-vector certificate | `ch7TwoSidedScale`, `ch7TwoSidedScaledInfCond`, `ch7_infNorm_ge_of_nonneg_right_eigenvector`, `problem7_10a_scaled_infCond_ge_perron_of_positive_eigenvector`, `problem7_10a_canonical_scaled_infCond_eq_perron_of_positive_eigenvector`, `problem7_10a_positive_entries_canonical_scaled_infCond_eq_perron` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated finite matrix multiplication, matrix-vector multiplication, infinity-norm, and submultiplicativity APIs: `matMul`, `matMulVec`, `matMulVec_matMul`, `infNorm`, `infNormVec`, `infNormVec_matMulVec_le`, and `infNorm_matMul_le` | Direct | Genuine Lean proof; the positive Perron-vector certificate remains an explicit source-facing dependency, not an unproved previous-split blocker or hidden assumption |
| Problem 7.10(a), Bauer infinity-norm `sInf = ρ` minimization under a positive Perron-vector certificate | `ch7TwoSidedScaledInfCondSet`, `ch7TwoSidedScaledInfCond_mem_set`, `ch7TwoSidedScaledInfCondSet_nonempty`, `ch7TwoSidedScaledInfCondSet_bddBelow`, `problem7_10a_scaledInfCondSet_sInf_eq_perron_of_positive_eigenvector`, `problem7_10a_positive_entries_scaledInfCondSet_sInf_eq_perron` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated order-theoretic `sInf` APIs plus finite matrix infinity-norm APIs and the proved Problem 7.10(a) Bauer core | Direct | Genuine Lean proof; the previous-split/repository dependencies are compiled order/norm facts, and the Perron-vector certificate is explicit source data rather than an unresolved Split 1 blocker |
| Problem 7.10(a)/(b), finite complex eigenvalue-radius dominance and attainment under a positive Perron-vector certificate | `ch7IsComplexEigenvalueRadius`, `ch7_complex_eigenvalue_norm_le_of_positive_real_eigenvector`, `ch7_real_positive_eigenvector_complexified`, `ch7_isComplexEigenvalueRadius_of_positive_real_eigenvector`, `problem7_10a_product_isComplexEigenvalueRadius_of_positive_eigenvector`, `problem7_10b_abs_product_isComplexEigenvalueRadius_of_positive_eigenvector` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated finite complex vector/matrix, complexified real-matrix, finite supremum/maximizer, and norm/triangle-inequality APIs plus the Chapter 7 Bauer eigenvector certificate surface | Direct | Genuine Lean proof; every complex eigenvalue certificate is bounded by a supplied positive real eigenvector equation, and the real eigenvector is complexified to show attainment. The previous-split/repository dependencies are compiled algebra/norm APIs; PF existence from irreducibility remains explicit current-source follow-up work |
| Problem 7.10(a)/(b), local finite eigenvalue-modulus maximum and `sSup = ρ` spectral-radius surrogate under a positive Perron-vector certificate | `ch7ComplexEigenvalueModulusSet`, `ch7_complexEigenvalueModulusSet_isGreatest_of_isComplexEigenvalueRadius`, `ch7_complexEigenvalueModulusSet_sSup_eq_of_isComplexEigenvalueRadius`, `problem7_10a_product_complexEigenvalueModulusSet_isGreatest_of_positive_eigenvector`, `problem7_10a_product_complexEigenvalueModulusSet_sSup_eq_of_positive_eigenvector`, `problem7_10b_abs_product_complexEigenvalueModulusSet_isGreatest_of_positive_eigenvector`, `problem7_10b_abs_product_complexEigenvalueModulusSet_sSup_eq_of_positive_eigenvector` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated finite set/order APIs, `IsGreatest`, real `sSup`, and compiled complex matrix-vector/eigenvalue-certificate infrastructure | Direct | Genuine Lean proof; the local radius certificate is converted into set membership and an upper-bound theorem, then into a real `sSup` equality. This uses compiled order APIs and does not introduce any unresolved Split 1 dependency or hidden PF/spectral theorem |
| Problem 7.10(a), scaled Bauer product local eigenvalue-modulus maximum and `sSup = ρ` | `problem7_10a_scaled_product_isComplexEigenvalueRadius_of_positive_eigenvector`, `problem7_10a_scaled_product_complexEigenvalueModulusSet_isGreatest_of_positive_eigenvector`, `problem7_10a_scaled_product_complexEigenvalueModulusSet_sSup_eq_of_positive_eigenvector` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated finite matrix multiplication/scaling, complex eigenvalue-radius, `IsGreatest`, and real `sSup` APIs plus the proved scaled-product eigenvector identity | Direct | Genuine Lean proof; positivity and reciprocal-diagonal hypotheses are used to build a positive scaled eigenvector and nonnegative scaled product, then the compiled local radius-to-`sSup` bridge proves exact `sSup = ρ`. No previous-split blocker, hidden PF theorem, or spectral-radius equality assumption is introduced |
| Problem 7.10(a)/(b), Mathlib `spectralRadius` equality under a positive Perron-vector certificate | `toLin_spectralRadius_eq_of_spectrum_modulusSet_isGreatest`, `toLin_spectralRadius_toReal_eq_of_spectrum_modulusSet_isGreatest`, `complexMatrix_toLin_spectralRadius_eq_of_isMaxComplexMatrixEigenvalueModulus`, `ch7_toLin_spectralRadius_eq_of_isComplexEigenvalueRadius`, `ch7_toLin_spectralRadius_toReal_eq_of_isComplexEigenvalueRadius`, `problem7_10a_product_toLin_spectralRadius_eq_of_positive_eigenvector`, `problem7_10b_abs_product_toLin_spectralRadius_eq_of_positive_eigenvector`, `problem7_10a_scaled_product_toLin_spectralRadius_eq_of_positive_eigenvector` | `LeanFpAnalysis/FP/Analysis/Norms.lean`; `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Mathlib `spectralRadius`, `spectrum`, `ENNReal.ofReal`, and the already proved spectrum-modulus `IsGreatest` certificates | Direct | Genuine Lean proof; the `spectralRadius` supremum over `nnnorm` spectrum elements is bounded above by the proved greatest real modulus and bounded below by the attaining spectral point. This closes the prior Banach-algebra value-representation API gap for supplied positive Perron-vector certificates, without assuming PF existence from irreducibility |
| Problem 7.10(a)/(b), generic Split 1 maximum-modulus and norm-existence export under a positive Perron-vector certificate | `ch7_isMaxComplexMatrixEigenvalueModulus_of_isComplexEigenvalueRadius`, `ch7_exists_mixedSubordinateMatrixNormValue_le_of_isComplexEigenvalueRadius`, `problem7_10a_product_isMaxComplexMatrixEigenvalueModulus_of_positive_eigenvector`, `problem7_10a_product_exists_mixedSubordinateMatrixNormValue_le_perron_add_delta`, `problem7_10b_abs_product_isMaxComplexMatrixEigenvalueModulus_of_positive_eigenvector`, `problem7_10b_abs_product_exists_mixedSubordinateMatrixNormValue_le_perron_add_delta`, `problem7_10a_scaled_product_isMaxComplexMatrixEigenvalueModulus_of_positive_eigenvector`, `problem7_10a_scaled_product_exists_mixedSubordinateMatrixNormValue_le_perron_add_delta` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated Split 1 `IsMaxComplexMatrixEigenvalueModulus` and `exists_mixedSubordinateMatrixNormValue_le_of_maxComplexMatrixEigenvalueModulus` APIs plus the locally proved Chapter 7 radius certificates | Direct | Genuine Lean proof; the local Chapter 7 eigenvalue-radius certificate is converted into the compiled generic maximum-modulus interface, then the integrated Split 1 Problem 6.8 theorem produces consistent complex matrix norm values with `c ≤ ρ + δ`. The previous-split dependency is already available and proved; no theorem-equivalent assumption, hidden PF theorem, or local duplicate of Split 1 norm infrastructure is introduced |
| Problem 7.10(a), Bauer infinity-norm least-value/minimum-attainment wrapper | `problem7_10a_scaledInfCondSet_isLeast_perron_of_positive_eigenvector`, `problem7_10a_positive_entries_scaledInfCondSet_isLeast_perron`, `problem7_10a_irreducible_products_scaledInfCondSet_isLeast_perron_of_nonzero_nonneg_eigenvector` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated order-theoretic `IsLeast`/set membership APIs plus the proved Problem 7.10(a) Bauer lower-bound and canonical-scaling equality | Direct | Genuine Lean proof; the canonical scaling is a proved value-set member and the lower-bound theorem proves leastness. PF existence remains explicit source-facing work, not an unresolved previous-split dependency |
| Problem 7.10(b), Bauer `B = |A|`, `C = |A⁻¹|` absolute-value scaled-`κ∞` instantiation under a positive Perron-vector certificate | `ch7TwoSidedScale_absMatrix_eq`, `ch7_infNorm_twoSidedScale_absMatrix_eq`, `ch7TwoSidedScaledInfKappa`, `ch7TwoSidedScale_isLeftInverse`, `ch7TwoSidedScale_isRightInverse`, `ch7TwoSidedScale_isInverse`, `ch7TwoSidedScaledInfKappa_eq_kappaInf_of_inverse`, `ch7TwoSidedScaledInfKappa_eq_abs_scaledInfCond`, `problem7_10b_scaled_infKappa_ge_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_canonical_scaled_infKappa_eq_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_positive_abs_entries_canonical_scaled_infKappa_eq_perron` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated finite matrix inverse/condition-number, absolute-value, and infinity-norm APIs: `IsInverse`, `kappaInf`, `kappaInf_eq_infNorm_mul_infNorm`, `absMatrix`, `infNorm`, `infNorm_absMatrix`, plus the proved Problem 7.10(a) Bauer core | Direct | Genuine Lean proof; the inverse-scaled partner is proved to be an inverse of the scaled matrix, the scaled product is identified with repository `kappaInf`, and the absolute-value reduction reuses already available Split 1 norm/matrix infrastructure without introducing a Perron-Frobenius or spectral-radius assumption |
| Problem 7.10(b), scaled `κ∞` `sInf = ρ` minimization under a positive Perron-vector certificate for `|A||A⁻¹|` | `ch7TwoSidedScaledInfKappaSet`, `ch7TwoSidedScaledInfKappa_mem_set`, `ch7TwoSidedScaledInfKappaSet_nonempty`, `ch7TwoSidedScaledInfKappaSet_bddBelow`, `problem7_10b_scaledInfKappaSet_sInf_eq_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_positive_abs_entries_scaledInfKappaSet_sInf_eq_perron` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated `sInf`, `kappaInf`, inverse-certificate, absolute-value, and infinity-norm APIs plus the proved Problem 7.10(a)/(b) Bauer core | Direct | Genuine Lean proof; lower and upper bounds are proved through compiled norm/inverse transport and canonical scaling membership, with no unproved PF/spectral or previous-split assumption |
| Problem 7.10(b), scaled `κ∞` least-value/minimum-attainment wrapper | `problem7_10b_scaledInfKappaSet_isLeast_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_irreducible_products_scaledInfKappaSet_isLeast_perron`, `problem7_10b_irreducible_products_scaledInfKappaSet_isLeast_perron_of_nonzero_nonneg_eigenvector`, `problem7_10b_positive_abs_entries_scaledInfKappaSet_isLeast_perron` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated `IsLeast`, `kappaInf`, inverse-certificate, absolute-value, irreducibility, and infinity-norm APIs plus the proved Problem 7.10(a)/(b)/(d) Bauer core | Direct | Genuine Lean proof; lower-bound and membership facts are compiled theorems, while irreducibility and nonzero-nonnegative eigenvector side conditions are discharged locally. No previous-split blocker or hidden PF theorem is used |
| Problem 7.10(b)/(d), irreducible-products canonical scaled-`κ∞` and exact `sInf = ρ` wrappers | `problem7_10b_irreducible_products_canonical_scaled_infKappa_eq_perron`, `problem7_10b_irreducible_products_scaledInfKappaSet_sInf_eq_perron` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated finite matrix, absolute-value, irreducibility, `sInf`, and scaled-`κ∞` APIs plus the already proved source-shaped Problem 7.10(d) positivity bridge | Direct | Genuine Lean proof; the wrappers reuse compiled prior Split/repository infrastructure and prove the `|A⁻¹|x > 0` side condition from irreducible products, while keeping PF eigenpair existence as explicit open source-facing work rather than a hidden previous-split assumption |
| Problem 7.10(a)/(b), irreducible-product Bauer wrappers from a nonzero nonnegative eigenvector certificate | `ch7_perronScalar_nonneg_of_nonzero_nonneg_eigenvector`, `ch7_perronScalar_pos_of_nonzero_nonneg_irreducible_eigenvector`, `ch7_nonzero_nonneg_irreducible_right_eigenvector_pos`, `problem7_10a_irreducible_products_canonical_scaled_infCond_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10a_irreducible_products_scaledInfCondSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10b_irreducible_products_canonical_scaled_infKappa_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10b_irreducible_products_scaledInfKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated finite matrix, irreducibility, power, `sInf`, scaled-`κ∞`, and absolute-value APIs plus the already proved positive-certificate Bauer core | Direct | Genuine Lean proof; irreducibility and a supplied nonzero nonnegative eigenpair are enough to prove `ρ > 0` and `x > 0`, after which the wrappers reuse compiled Bauer lower-bound/canonical/`sInf` theorems. The proof relies on available previous-split/repository APIs, not an unresolved previous-split hypothesis |
| Problem 7.10(b)/(d), positive-entry product irreducibility side condition | `ch7_matrix_isPrimitive_of_pos_entries`, `ch7_matrix_isIrreducible_of_pos_entries`, `ch7_matMul_pos_of_pos`, `ch7_bauer_positive_products_irreducible`, `problem7_10b_positive_abs_entries_products_irreducible` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated finite matrix/absolute-value APIs `matMul` and `absMatrix`, plus Mathlib's compiled `Matrix.IsPrimitive`/`Matrix.IsIrreducible` API | Direct | Genuine Lean proof; positive entries imply primitive/irreducible matrices and positive products, with no unproved previous-split hypothesis and no local duplicate Perron-Frobenius foundation |
| Problem 7.10(d), source-shaped irreducible-product `Cx > 0` transfer | `ch7_perronScalar_pos_of_nonneg_irreducible_eigenvector`, `problem7_10d_Cx_pos_of_irreducible_BC_CB`, `problem7_10d_abs_inverse_Cx_pos_of_irreducible_products` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated finite matrix power/eigenvector APIs and Mathlib's compiled `Matrix.isIrreducible_iff_exists_pow_pos`/`Matrix.pow_apply_nonneg` connectivity API | Direct | Genuine Lean proof; the source irreducibility hypotheses replace the earlier positive-entry side condition, and the remaining positive Perron-vector certificate is a source-facing PF/spectral dependency rather than an unresolved previous-split blocker |
| Problem 7.10(e), one-norm Bauer transpose branch under a positive Perron-vector certificate | `ch7TwoSidedScaledOneCond_eq_transpose_infCond`, `problem7_10e_scaled_oneCond_ge_perron_of_transpose_positive_eigenvector`, `problem7_10e_canonical_scaled_oneCond_eq_perron_of_transpose_positive_eigenvector`, `problem7_10e_positive_entries_canonical_scaled_oneCond_eq_perron_of_transpose`, `ch7TwoSidedScaledOneKappa_eq_abs_scaledOneCond`, `problem7_10e_scaled_oneKappa_ge_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_canonical_scaled_oneKappa_eq_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_positive_abs_entries_canonical_scaled_oneKappa_eq_perron_of_transpose` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated one-/infinity-norm, transpose, two-sided scaling, absolute-value, matrix-vector, and submultiplicativity APIs: `oneNorm`, `infNorm`, `matTranspose`, `ch7_matTranspose_twoSidedScale`, `absMatrix`, `infNorm_absMatrix`, `matMul`, `matMulVec`, and the proved Problem 7.10(a) Bauer core | Direct | Genuine Lean proof; the previous-split/repository dependencies are compiled norm/matrix facts, and the explicit transpose-side Perron-vector certificate is a source-facing hypothesis rather than an unresolved previous-split blocker |
| Problem 7.10(e), one-norm scaled `κ₁` `sInf = ρ` minimization under a transpose-side positive Perron-vector certificate | `ch7TwoSidedScaledOneKappaSet`, `ch7TwoSidedScaledOneKappa_mem_set`, `ch7TwoSidedScaledOneKappaSet_nonempty`, `ch7TwoSidedScaledOneKappaSet_bddBelow`, `problem7_10e_scaledOneKappaSet_sInf_eq_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_positive_abs_entries_scaledOneKappaSet_sInf_eq_perron_of_transpose` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated `sInf`, one-/infinity-norm, transpose, absolute-value, and condition-product APIs plus the proved Bauer transpose branch | Direct | Genuine Lean proof; the proof chain is order-theoretic packaging of the compiled one-norm Bauer lower bound and canonical scaling equality, not an unresolved previous-split or PF/spectral assumption |
| Problem 7.10(e), one-norm scaled `κ₁` least-value/minimum-attainment wrapper | `problem7_10e_scaledOneKappaSet_isLeast_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_positive_abs_entries_scaledOneKappaSet_isLeast_perron_of_transpose`, `problem7_10e_irreducible_transpose_products_scaledOneKappaSet_isLeast_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_products_scaledOneKappaSet_isLeast_perron_of_nonzero_nonneg_eigenvector` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated `IsLeast`, one-/infinity-norm, transpose, absolute-value, irreducibility, and condition-product APIs plus the proved Bauer transpose branch and source-product transpose bridge | Direct | Genuine Lean proof; the canonical transpose-side scaling is a proved value-set member and product irreducibility is transported from the source products. PF/spectral/common-scaling existence remains the only full-source Bauer gap |
| Problem 7.10(e), irreducible transpose-product one-norm wrappers from a nonzero nonnegative eigenvector certificate | `problem7_10e_irreducible_transpose_products_canonical_scaled_oneCond_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_transpose_products_canonical_scaled_oneKappa_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_transpose_products_scaledOneKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated finite matrix, transpose, irreducibility, one-/infinity-norm, `sInf`, and Bauer certificate APIs plus the already proved Problem 7.10(d) positivity bridge | Direct | Genuine Lean proof; irreducibility and a supplied nonzero nonnegative transpose-side eigenpair prove `y > 0` and `Cᵀy > 0`, after which the wrappers reuse compiled one-norm canonical and `sInf` theorems. The proof relies on available previous-split/repository APIs, not an unresolved previous-split hypothesis |
| Problem 7.15, reciprocal scaling invariance of `A ∘ A^{-T}`, Horn-Johnson operator-2 certificate, scaled inverse-partner bound, exact op-2 infimum lower bound, conditional equality/least-value attainability certificates, and nonsingular diagonal attainability | `ch7HadamardProduct`, `ch7_matTranspose_twoSidedScale`, `ch7HadamardProduct_twoSidedScale_transpose_inverse_eq`, `problem7_15_twoSidedScale_hadamard_transpose_inverse_invariant`, `opNorm2Le_transpose`, `problem7_15_transpose_inverse_partner_opNorm2Le`, `frobNormRect_diagMatrix`, `vecNorm2_diagonal_le_frobNormRect`, `matMulVec_hadamard_eq_diag_rectMatMul_diag_transpose`, `opNorm2Le_hadamard`, `complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le`, `opNorm2Le_complexMatrixOp2_realRectToCMatrix`, `problem7_15_hornJohnson_hadamard_opNorm2Le`, `problem7_15_scaled_inverse_hadamard_opNorm2Le`, `ch7TwoSidedScaledOp2KappaSet`, `ch7TwoSidedScaledOp2KappaSet_nonempty`, `problem7_15_hadamard_op2_le_twoSidedScaledOp2Kappa_mem`, `problem7_15_twoSidedScaledOp2Kappa_sInf_ge_hadamard_op2`, `problem7_15_twoSidedScaledOp2Kappa_sInf_ge_hadamard_op2_of_inverse`, `problem7_15_twoSidedScaledOp2Kappa_sInf_eq_hadamard_op2_of_mem`, `problem7_15_twoSidedScaledOp2Kappa_isLeast_hadamard_op2_of_mem`, `problem7_15_twoSidedScaledOp2Kappa_sInf_eq_hadamard_op2_of_attaining_scaling`, `problem7_15_twoSidedScaledOp2Kappa_isLeast_hadamard_op2_of_attaining_scaling`, `problem7_15_complexMatrixOp2_realRectToCMatrix_orthogonal_eq_one`, `problem7_15_ch7TwoSidedScale_diagMatrix_eq`, `problem7_15_hadamard_diag_inverse_transpose_eq_idMatrix`, `problem7_15_diagonal_hadamard_op2_eq_one`, `problem7_15_diagonal_attaining_scaling_eq_hadamard_op2`, `problem7_15_diagonal_twoSidedScaledOp2Kappa_sInf_eq_one`, `problem7_15_diagonal_twoSidedScaledOp2Kappa_isLeast_one` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean`, `LeanFpAnalysis/FP/Analysis/Norms.lean` | Integrated finite matrix transpose, two-sided scaling, Cauchy, matrix-vector multiplication, Frobenius norm, diagonal matrix, real orthogonality/sign-diagonal, triple-product Frobenius, real Euclidean norm surfaces, and exact complexified op-2 norm bridge: `matTranspose`, `ch7TwoSidedScale`, `matMulVec`, `vecNorm2`, `vecNorm2Sq`, `frobNormRect`, `diagMatrix`, `IsOrthogonal.diagMatrix_of_sq_eq_one`, `rectMatMul`, `frobNormRect_triple_rectMatMul_le_of_rectOpNorm2Le`, `abs_vecInnerProduct_le_vecNorm2_mul`, `complexMatrixOp2`, and `realRectToCMatrix` | Direct | Genuine Lean proof; these source adapters prove the invariant Hadamard product, transpose norm side condition, Horn-Johnson Schur-product certificate, exact positive-scaling `sInf` lower-bound statement, conditional equality plus `IsLeast` least-value packaging when the lower-bound value is attained, and Appendix A.7.15's nonsingular diagonal case by scaling to orthogonal sign-diagonal factors and proving `sInf = 1` plus `IsLeast 1` |
| Problem 7.6(a), row-wise relative-data condition comparison | `ch7RowwiseDataCondAtSolutionInf`, `ch7_rowwiseDataForwardBound_lower`, `ch7_rowwiseDataForwardBound_upper`, `problem7_6a_rowwise_data_condition_bounds` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated `condSkeel`, `infNormVec`, `matMulVec`, and existing `oneNormVec` API reused from the repository | Direct | Genuine Lean proof; no unproved previous-split hypothesis or duplicate condition-number foundation |
| Problem 7.6(b), columnwise relative-data condition comparison | `ch7ColumnwiseDataCondAtSolutionInf`, `ch7_columnwiseDataForwardBound_lower`, `ch7_columnwiseDataForwardBound_upper`, `problem7_6b_columnwise_data_condition_bounds` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated `infNorm`, `row_sum_le_infNorm`, `matMulVec`, and `oneNormVec` API reused from the repository | Direct | Genuine Lean proof; no unproved previous-split hypothesis or duplicate condition-number foundation |
| Problem 7.9 finite first-order componentwise and normwise scalar-output formulas plus `χ ≥ 1` lower-bound specializations | `ch7Problem79_firstOrder_abs_le`, `ch7Problem79_linearizedRelativeChange_le`, `ch7Problem79_attaining_firstOrder_eq`, `problem7_9_linearized_componentwise_functional_formula`, `ch7Problem79_linearFunctional_eq_adjointWeight_mul_Ax`, `problem7_9_linearized_componentwise_functional_ge_one_of_abs_matrix`, `problem7_9_linearized_componentwise_functional_ge_one_of_abs_rhs`, `ch7Problem79_normwise_firstOrder_abs_le`, `ch7Problem79_normwiseLinearizedRelativeChange_le`, `ch7Problem79_normwise_attaining_firstOrder_eq`, `problem7_9_linearized_normwise_functional_formula` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated finite-summation sign helper `summationAbsSign`, `summationAbsSign_mul_eq_abs`, `mul_summationAbsSign_eq_abs`, and `abs_summationAbsSign`; integrated matrix-vector inverse API `rectMatMulVec_left_inverse_of_IsLeftInverse`; integrated Euclidean Cauchy/operator-2/rank-one API `abs_vecInnerProduct_le_vecNorm2_mul`, `opNorm2Le`, and `opNorm2Le_residualRankOnePerturbation`; Mathlib finite-sum APIs | Direct | Genuine Lean proof; no unproved previous-split hypothesis or theorem-equivalent assumption |
| Problem 7.9 nonlinear componentwise source-radius condition number | `ch7Problem79_exact_delta_vector_decomposition`, `ch7Problem79_exact_scalar_decomposition`, `ch7Problem79_exact_scalar_remainder_abs_le`, `problem7_9_exact_componentwise_relative_change_le_linearized_plus_quadratic`, `problem7_9_exact_componentwise_relative_change_ge_linearized_minus_quadratic`, `ch7Problem79ComponentwiseExactRadiusSet_value_le`, `exists_ch7Problem79ComponentwiseExactRadiusSet_lower_witness`, `problem7_9_componentwise_exact_radiusSup_tendsto_linearized`, `problem7_9_componentwise_exact_condition_of_positive_radii` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated matrix-vector linearity, infinity-norm, `infNormVec`, `infNorm_matMul_le`, `infNormVec_matMulVec_le`, `infNorm_absMatrix`, finite-square inverse APIs, and the current Chapter 7 local inverse candidate from the Problem 7.11 proof chain | Direct | Genuine Lean proof; the reused APIs are compiled theorems, and the nonlinear source-radius value is proved by a finite quadratic-remainder squeeze rather than assumed |
| Problem 7.9 nonlinear normwise source-radius condition number | `ch7Problem79_normwise_deltaA_componentwise_bound`, `ch7Problem79_normwise_deltaB_componentwise_bound`, `problem7_9_exact_normwise_relative_change_le_linearized_plus_quadratic`, `problem7_9_exact_normwise_relative_change_ge_linearized_minus_quadratic`, `ch7Problem79NormwiseExactRadiusSet_value_le`, `exists_ch7Problem79NormwiseExactRadiusSet_lower_witness`, `problem7_9_normwise_exact_radiusSup_tendsto_linearized`, `problem7_9_normwise_exact_condition_of_positive_radii` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated `finiteBasisVec`, `abs_coord_le_vecNorm2`, `opNorm2Le`, matrix-vector linearity, infinity-norm, finite-square inverse APIs, and the current Chapter 7 local inverse candidate from the Problem 7.11 proof chain | Direct | Genuine Lean proof; the normwise constraints are converted by proved adapter lemmas and the exact source-radius value is proved by a finite quadratic-remainder squeeze rather than assumed |
| Problem 7.11 / Appendix A.11, first-order inverse componentwise formula | `ch7InverseLinearizedEntry`, `ch7InverseCompSensitivityEntry`, `ch7InverseCompSensitivityRatio`, `ch7InverseComponentwiseLinearizedCond`, `ch7InverseLinearizedRelativeChangeMax`, `ch7Problem711AttainingDelta`, `problem7_11_linearized_inverse_componentwise_upper_and_sign_attainment`, `problem7_11_linearized_inverse_componentwise_formula` | `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` | Integrated finite-summation sign helper `summationAbsSign`, `summationAbsSign_mul_eq_abs`, `mul_summationAbsSign_eq_abs`, and `abs_summationAbsSign`; Mathlib finite-sum and finite-sup APIs | Direct | Genuine Lean proof; no unproved previous-split hypothesis or theorem-equivalent assumption |

### 3. Prior Split 1 Dependencies Reused Or Requiring Integration Follow-Up

| Source label/name | Direct or indirect previous-split dependency | Exact previous split number | Integrated Split 1 declaration or interface reused | Thin wrapper added | Integration/API discrepancy |
| --- | --- | --- | --- | --- | --- |
| Theorem 7.1 / equations (7.1)-(7.2) arbitrary subordinate-norm form | Direct | 1 | `IsComplexVectorNorm`, `MixedSubordinateMatrixBound`, `IsMixedSubordinateMatrixNormValue` | `theorem7_1_subordinate_necessary`, `theorem7_1_subordinate_sufficient`, `theorem7_1_subordinate` | None |
| Equation (7.3) arbitrary dual/norming-vector perturbation formula | Direct | 1 | `IsDualFunctionalNormValue`, `exists_dualFunctionalNormValue_one_of_pos_vector`, `rankOneCMatrixFromFunctional`, `complexMatrixVecMul_rankOneCMatrixFromFunctional` | `eq_7_3_subordinate_attaining_perturbations` | None |
| Theorem 7.2 / equation (7.4) arbitrary subordinate-norm form | Direct | 1 | `IsComplexVectorNorm`, `MixedSubordinateMatrixBound`, `IsMixedSubordinateMatrixNormValue`, `IsComplexMatrixLeftInverse` | `theorem7_2_subordinate_forward_error_bound` | None |
| Equation (7.5) generic normwise condition-number wrapper | Direct | 1 | `IsComplexVectorNorm`, `IsMixedSubordinateMatrixNormValue`, `IsComplexMatrixInverse`, `exists_unit_vector_attaining_mixedSubordinateNormValue`, `exists_dualFunctionalNormValue_one_of_pos_vector`, `rankOneCMatrixFromFunctional`, `rankOneCMatrix_isMixedSubordinateMatrixNormValue_of_dualFunctionalNormValue` | `eq_7_5_subordinate_conditionNumberRadiusLimitValue_of_positive_radii`, `eq_7_5_subordinate_conditionNumber_of_positive_radii` | None |
| Equation (7.26), relative distance to singularity | Direct | 1 | `complexMatrix_relativeSingularDistance_min_eq_inv_conditionNumberProduct`, `IsMixedConditionNumberProductValue`, `IsMinimumMixedRelativeSingularDistance` | `eq_7_26_relative_distance_to_singularity_eq_inv_condition_number` | None |
| Theorem 7.4 / equation (7.10) arbitrary absolute-norm form | Direct | 1 | `IsAbsoluteComplexVectorNorm`, `absolute_norm_iff_monotone_norm`, `IsMixedSubordinateMatrixNormValue`, `IsComplexMatrixLeftInverse`, `complexMatrixVecMul_componentwiseAbsLe_absMatrix` | `theorem7_4_absolute_forward_error_bound` | None |
| Problem 7.2 arbitrary subordinate-norm form | Direct | 1 | `IsMixedSubordinateMatrixNormValue`, `IsComplexMatrixLeftInverse`, `complexMatrixVecMul` linearity | `problem7_2_subordinate_*` family | None |
| Problem 7.7 arbitrary subordinate-norm eta comparison | Direct | 1 | `IsComplexVectorNorm`, `MixedSubordinateMatrixBound`, `IsMixedSubordinateMatrixNormValue`, `theorem7_1_subordinate` | `problem7_7_subordinate_*` family | None |
| Equation (7.12), Skeel infinity-norm global condition number | Direct | 1 | `condSkeel`, `infNormVec`, `abs_le_infNormVec`, `ch7SkeelCondAtOnes_eq_condSkeel` | `ch7CondEFGlobalInf`, `ch7SkeelGlobalCondInf`, `ch7SkeelCondAtSolutionInf_le_condSkeel`, `eq_7_12_skeel_global_conditionNumber_eq_condSkeel` | None |
| Prose after (7.14), factor-2 comparison for `f = |b| = |Ax|` | Direct | 1 | `matMulVec`, `infNormVec`, `ch7CondEFAtSolutionInf`, `ch7ForwardBoundEF` | `ch7ComponentwiseDataCondAtSolutionInf`, `ch7SkeelCondAtSolutionInf_le_componentwiseDataCondAtSolutionInf`, `ch7ComponentwiseDataCondAtSolutionInf_le_two_mul_skeelCondAtSolutionInf` | None |
| Appendix A.3 / equations (7.15)-(7.16), row-equilibrated scaling package | Direct | 1 | `diagMatrix`, `matMul_diagMatrix_left/right`, `infNorm_matMul_le`, `condSkeel`, `kappaInf`, `condSkeel_le_kappaInf` | `ch7RowScale`, `ch7InverseRowScale`, `ch7RowsEquilibratedInf`, `ch7PositiveRowScaledKappaInfSet`, `problem7_3_rowEquilibrated_scaling_condition_eq`, `eq_7_15_positive_rowScaling_sInf_eq_condSkeel_of_right_inverse`, `eq_7_16_rowEquilibrated_bounds` | None |
| Problem 7.4, unit-diagonal symmetric PSD scaled-factor condition bounds | Direct | 1 | `finitePSD`, `finiteQuadraticForm`, `finiteBasisVec`, `infNorm_eq_sup_row_sum`, `condSkeel`, `kappaInf`, and `condSkeel_le_kappaInf` | `problem7_4_abs_entry_le_one_of_finitePSD_diag_one`, `problem7_4_unitDiagonal_entryBound_condition_bounds`, `problem7_4_unitDiagonal_finitePSD_condition_bounds` | None |
| Equations (7.19)-(7.22), row/column-equilibration dependencies | Direct | 1 | `complexVecLpNorm`, `complexVecLpNorm_ofReal_monotone`, `complexMatrixLpNormOfReal`, `complexMatrixLpNormOfReal_isComplexMatrixLpNormValue`, `complexMatrixLpNormOfReal_mul_le`, `isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound`, `hasComplexMatrixLpBound_of_nonneg_mixedSubordinateMatrixBound`, `IsComplexVectorNorm.sum_le`, `complexVecOneNorm_le_card_rpow_mul_complexVecLpNorm`, `vecNorm2`, `frobNormRect`, `rectMatMulVec`, `rectOpNorm2Le`, `rectOpNorm2Le_of_frobNormRect_le`, `rectOpNorm2Le_of_complexMatrixOp2_realRectToCMatrix_le`, `complexMatrixOp2_realRectToCMatrix_le_of_rectOpNorm2Le`, `basisVec`, `oneNormRect`, `infNormRect`, `col_sum_le_oneNormRect`, `oneNormRect_le_of_col_sum_le`, `row_sum_le_infNormRect`, `infNormRect_le_of_row_sum_le`, `Set`, `BddBelow`, `le_csInf`, `csInf_le`, and `IsLeast.csInf_eq` | `ch7RectColumnLpNormOfReal`, `ch7RectColumnLpNormOfReal_nonneg`, `eq_7_20_column_lpNorm_le_matrixLpNormOfReal`, `ch7_complexVecLpNorm_realRect_matVec_le_sum_column_lpNorm`, `eq_7_20_matrixLpNormOfReal_le_card_rpow_mul_column_bound`, `ch7ColumnEquilibratingScaleLpOfReal`, `ch7RectColumnLpNormOfReal_rightScale`, `ch7RectColumnLpNormOfReal_rightScale_equilibrating`, `eq_7_21_matrixLpNormOfReal_column_equilibrated`, `ch7_complexMatrixLpNormOfReal_nonneg`, `ch7_complexVecLpNormOfReal_diagScale_le_of_norm_le`, `eq_7_22_matrixLpNormOfReal_inverseSide_bound`, `ch7LpRightScaledCondOfReal`, `ch7LpRightScaledCondSetOfReal`, `ch7LpRightScaledCondOfReal_nonneg`, `ch7LpRightScaledCondOfReal_mem_set`, `ch7LpRightScaledCondSetOfReal_nonempty`, `theorem7_5_lp_column_equilibration_le_card_rpow_right_scaling`, `theorem7_5_lp_column_equilibration_le_card_rpow_sInf_right_scalings`, `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings`, `ch7RectColumnNorm2`, `ch7RectRightScale`, `ch7ColumnEquilibratingScale2`, `eq_7_20_column_norm_le_of_rectOpNorm2Le`, `ch7_frobNormRect_le_sqrt_card_mul_column_bound`, `eq_7_20_rectOpNorm2Le_of_column_bound`, `eq_7_21_rectOpNorm2Le_column_equilibrated`, `ch7RectColumnNorm1`, `ch7RectLeftScale`, `ch7ColumnEquilibratingScale1`, `eq_7_21_oneNormRect_column_equilibrated`, `ch7OneNormRightScaledCondSet`, `eq_7_22_oneNormRect_inverseSide_bound`, `theorem7_5_p1_column_equilibration_le_right_scaling`, `theorem7_5_p1_column_equilibration_sInf_eq_right_scalings`, `ch7_vecNorm2_mul_le_of_abs_le`, `ch7RectLeftScale_rectOpNorm2Le_of_abs_le`, `ch7Op2RightScaledCond`, `ch7Op2RightScaledCondSet`, `ch7Op2RightScaledCondSet_nonempty`, `ch7Op2RightScaledCondSet_bddBelow`, `eq_7_22_op2_inverseSide_bound`, `theorem7_5_p2_column_equilibration_le_sqrt_card_right_scaling`, `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings`, `ch7RectRowNorm1`, `ch7RowEquilibratingScale1Rect`, `eq_7_19_infNormRect_row_equilibrated`, `ch7InfNormLeftScaledCondSet`, `eq_7_19_infNormRect_inverseSide_bound`, `theorem7_5_pinf_row_equilibration_le_left_scaling`, and `theorem7_5_pinf_row_equilibration_sInf_eq_left_scalings` | None for the finite-real `p` `(7.20)`-`(7.22)` dependencies and explicit-`Aplus` `(7.18)` `sInf`/conditional-`min` wrappers; none for the `p = 2` dependency, pairwise column-scaling condition-product specialization, and explicit-`Aplus` `sInf`/conditional-`min` wrappers; none for the `p = 1` pairwise/`sInf` algebraic specialization or the `p = ∞` pairwise/`sInf` algebraic specialization; full Theorem 7.5 still needs the Moore-Penrose/projection and proof that the general source value sets attain their infima |
| Equation (7.19), finite-real conjugate-row proof-route specialization | Direct | 1 | `complexVecLpNorm`, `complexMatrixLpNormOfReal`, `complexMatrixLpNormOfReal_rowDualMax_bounds`, `complexMatrixRowDualMaxNorm_le_of_row_le`, `complexMatrixRowDualMaxNorm_row_le_of_nonneg`, `IsComplexVectorNorm.smul`, `isComplexMatrixLpNormValue_le_of_hasComplexMatrixLpBound`, `hasComplexMatrixLpBound_of_nonneg_mixedSubordinateMatrixBound`, `le_csInf`, `sInf`, and `IsLeast.csInf_eq` | `ch7RectRowDualLpNormOfReal`, `ch7RowDualEquilibratingScaleLpOfReal`, `eq_7_19_matrixLpNormOfReal_dual_row_equilibrated`, `eq_7_19_matrixLpNormOfReal_dual_row_inverseSide_bound`, `ch7LpLeftScaledCondOfReal`, `ch7LpLeftScaledCondSetOfReal`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_left_scaling`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings`, and `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings` | None for the conjugate-row proof-route branch and conditional source-`min` adapter; full source-facing Theorem 7.5 still needs Moore-Penrose/projection, proof of minimizer existence, and packaging/reconciliation for the printed row-scale notation |
| Theorem 7.5 Penrose1-plus-rank source `sInf`/`min` adapters | Direct | 1 | Integrated rank/order/norm interfaces already exposed above: Mathlib `Matrix.rank`, `LinearMap` rank-nullity, `sInf`, `IsLeast.csInf_eq`, and the Chapter 7 rectangular norm/scaling APIs | `theorem7_5_p1_column_equilibration_isLeast_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_lp_column_equilibration_le_card_rpow_sInf_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings_of_penrose1_matrix_rank_eq_height`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings_of_penrose1_matrix_rank_eq_height`, `theorem7_5_p2_row_equilibration_le_sqrt_card_sInf_left_scalings_of_penrose1_matrix_rank_eq_height`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_penrose1_matrix_rank_eq_height`, and `theorem7_5_pinf_row_equilibration_isLeast_left_scalings_of_penrose1_matrix_rank_eq_height` | None. These wrappers reuse the integrated one-sided-inverse/rank bridge and do not expose a missing Split 1 interface; remaining gaps are current Split 2 Moore-Penrose construction and non-endpoint minimizer-existence work |
| Corollary 7.6 Cholesky-factor `D*` and two-sided `sInf` transfer | Direct | 1 | `vecNorm2`, `ch7RectColumnNorm2`, `ch7ColumnEquilibratingScale2`, `eq_7_21_rectOpNorm2Le_column_equilibrated`, `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings`, `complexMatrixOp2`, `realRectToCMatrix`, `complexMatrixOp2_adjoint_mul_self_eq_sq`, `complexMatrixOp2_realRectToCMatrix_transpose_mul_self_eq_sq`, and the generic two-sided inverse transport `ch7TwoSidedScale_isInverse` | `ch7SymmetricDiagEquilibratingScale2`, `ch7SymmetricDiagEquilibratingInvScale2`, `corollary7_6_cholesky_diag_eq_column_norm_sq`, `corollary7_6_cholesky_diag_invScale_eq_column_norm`, `corollary7_6_cholesky_diag_scale_eq_column_equilibrating`, `corollary7_6_cholesky_column_norm_pos`, `corollary7_6_cholesky_factor_column_equilibrated`, `corollary7_6_cholesky_factor_op2Le_sqrt_card`, `corollary7_6_cholesky_factor_column_scaling_le_sqrt_card_sInf_right_scalings`, `ch7SymmetricOp2ScaledCond`, `ch7SymmetricOp2ScaledCondSet`, `ch7SymmetricOp2ScaledCond_mem_set`, `ch7SymmetricOp2ScaledCondSet_nonempty`, `ch7SymmetricOp2ScaledCond_nonneg`, `ch7SymmetricOp2ScaledCondSet_bddBelow`, `ch7CholeskyInverseGram`, `corollary7_6_cholesky_scaled_gram_eq`, `corollary7_6_cholesky_scaled_inverse_gram_eq`, `corollary7_6_cholesky_scaled_cond_eq_factor_cond_sq`, `corollary7_6_cholesky_scaled_cond_le_card_sInf_right_scalings_sq`, `corollary7_6_cholesky_right_sInf_sq_le_symmetric_sInf`, `corollary7_6_cholesky_scaled_cond_le_card_sInf_symmetric_scalings`, `corollary7_6_cholesky_inverse_gram_isInverse`, and `corollary7_6_cholesky_scaled_inverse_gram_isInverse` | None for the repository `sInf` model of Corollary 7.6; no minimizer-attainment theorem is asserted |
| Theorem 7.7, Stewart-Sun Frobenius right-scaling minimizer | Direct | 1 | `frobNorm`, `vecNorm2`, `matMul_diagMatrix_left/right`, `abs_vecInnerProduct_le_vecNorm2_mul`, `IsLeftInverse`, `vecNorm2_eq_zero_iff` | `theorem7_7_stewart_sun_frobenius_scaling_of_left_inverse` plus supporting lower-bound and attainment lemmas | None |
| Problem 7.10(a), Bauer infinity-norm algebra, `sInf = ρ`, and `IsLeast` wrappers | Direct | 1 | `matMul`, `matMulVec`, `matMulVec_matMul`, `infNorm`, `infNormVec`, `infNormVec_matMulVec_le`, `infNorm_matMul_le`, `Set`, `BddBelow`, `le_csInf`, `csInf_le`, and `IsLeast` | `ch7TwoSidedScale`, `ch7TwoSidedScaledInfCond`, `ch7TwoSidedScaledInfCondSet`, `ch7TwoSidedScaledInfCond_mem_set`, `ch7TwoSidedScaledInfCondSet_nonempty`, `ch7TwoSidedScaledInfCondSet_bddBelow`, `problem7_10a_scaled_infCond_ge_perron_of_positive_eigenvector`, `problem7_10a_canonical_scaled_infCond_eq_perron_of_positive_eigenvector`, `problem7_10a_positive_entries_canonical_scaled_infCond_eq_perron`, `problem7_10a_scaledInfCondSet_sInf_eq_perron_of_positive_eigenvector`, `problem7_10a_positive_entries_scaledInfCondSet_sInf_eq_perron`, `problem7_10a_scaledInfCondSet_isLeast_perron_of_positive_eigenvector`, `problem7_10a_positive_entries_scaledInfCondSet_isLeast_perron`, and `problem7_10a_irreducible_products_scaledInfCondSet_isLeast_perron_of_nonzero_nonneg_eigenvector` | None for the explicit positive Perron-vector certificate model; full source Problem 7.10 still needs PF/spectral-radius packaging |
| Problem 7.10(b)/(d), Bauer `B = |A|`, `C = |A⁻¹|` absolute-value scaled-`κ∞` instantiation, exact `sInf = ρ`, `IsLeast` wrapper, positive-entry irreducibility adapter, irreducible-product `Cx > 0` bridge, and irreducible-products canonical/`sInf`/`IsLeast` wrappers | Direct | 1 | `IsInverse`, `kappaInf`, `kappaInf_eq_infNorm_mul_infNorm`, `absMatrix`, `infNorm`, `infNorm_absMatrix`, `matMul`, `matMulVec`, `infNorm_matMul_le`, `Set`, `BddBelow`, `le_csInf`, `csInf_le`, `IsLeast`, and the already closed Problem 7.10(a) Bauer core; Mathlib supplies the compiled `Matrix.IsPrimitive`/`Matrix.IsIrreducible` and positive-power connectivity APIs | `ch7TwoSidedScale_absMatrix_eq`, `ch7_infNorm_twoSidedScale_absMatrix_eq`, `ch7TwoSidedScaledInfKappa`, `ch7TwoSidedScaledInfKappaSet`, `ch7TwoSidedScaledInfKappa_mem_set`, `ch7TwoSidedScaledInfKappaSet_nonempty`, `ch7TwoSidedScaledInfKappaSet_bddBelow`, `ch7TwoSidedScale_isLeftInverse`, `ch7TwoSidedScale_isRightInverse`, `ch7TwoSidedScale_isInverse`, `ch7TwoSidedScaledInfKappa_eq_kappaInf_of_inverse`, `ch7TwoSidedScaledInfKappa_eq_abs_scaledInfCond`, `problem7_10b_scaled_infKappa_ge_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_canonical_scaled_infKappa_eq_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_positive_abs_entries_canonical_scaled_infKappa_eq_perron`, `problem7_10b_scaledInfKappaSet_sInf_eq_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_scaledInfKappaSet_isLeast_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_irreducible_products_canonical_scaled_infKappa_eq_perron`, `problem7_10b_irreducible_products_scaledInfKappaSet_sInf_eq_perron`, `problem7_10b_irreducible_products_scaledInfKappaSet_isLeast_perron`, `problem7_10b_irreducible_products_scaledInfKappaSet_isLeast_perron_of_nonzero_nonneg_eigenvector`, `problem7_10b_positive_abs_entries_scaledInfKappaSet_sInf_eq_perron`, `problem7_10b_positive_abs_entries_scaledInfKappaSet_isLeast_perron`, `ch7_matrix_isPrimitive_of_pos_entries`, `ch7_matrix_isIrreducible_of_pos_entries`, `ch7_matMul_pos_of_pos`, `ch7_bauer_positive_products_irreducible`, `problem7_10b_positive_abs_entries_products_irreducible`, `ch7_perronScalar_pos_of_nonneg_irreducible_eigenvector`, `problem7_10d_Cx_pos_of_irreducible_BC_CB`, and `problem7_10d_abs_inverse_Cx_pos_of_irreducible_products` | None |
| Problem 7.10(e), one-norm Bauer transpose branch, scaled-`κ₁` absolute-value instantiation, exact `sInf = ρ`, and `IsLeast` wrappers | Direct | 1 | `oneNorm`, `infNorm`, `matTranspose`, `absMatrix`, `infNorm_absMatrix`, `matMul`, `matMulVec`, `infNorm_matMul_le`, `Set`, `BddBelow`, `le_csInf`, `csInf_le`, `IsLeast`, and the already closed Problem 7.10(a) Bauer core | `ch7TwoSidedScaledOneCond`, `ch7TwoSidedScaledOneCond_eq_transpose_infCond`, `problem7_10e_scaled_oneCond_ge_perron_of_transpose_positive_eigenvector`, `problem7_10e_canonical_scaled_oneCond_eq_perron_of_transpose_positive_eigenvector`, `problem7_10e_positive_entries_canonical_scaled_oneCond_eq_perron_of_transpose`, `ch7TwoSidedScaledOneKappa`, `ch7TwoSidedScaledOneKappaSet`, `ch7TwoSidedScaledOneKappa_mem_set`, `ch7TwoSidedScaledOneKappaSet_nonempty`, `ch7TwoSidedScaledOneKappaSet_bddBelow`, `ch7TwoSidedScaledOneKappa_eq_abs_scaledOneCond`, `problem7_10e_scaled_oneKappa_ge_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_canonical_scaled_oneKappa_eq_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_positive_abs_entries_canonical_scaled_oneKappa_eq_perron_of_transpose`, `problem7_10e_scaledOneKappaSet_sInf_eq_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_scaledOneKappaSet_isLeast_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_positive_abs_entries_scaledOneKappaSet_sInf_eq_perron_of_transpose`, and `problem7_10e_positive_abs_entries_scaledOneKappaSet_isLeast_perron_of_transpose` | None for the one-norm certificate branch; full source Problem 7.10(e) still needs PF/global minimization packaging |
| Problem 7.10(e), irreducible transpose/source-product one-norm wrappers from a nonzero nonnegative eigenvector certificate | Direct | 1 | `Matrix.IsIrreducible`, `matTranspose`, `matMul`, `matMulVec`, `oneNorm`, `infNorm`, `absMatrix`, `sInf`, `IsLeast`, and the already closed Problem 7.10(d) irreducible-product positivity bridge plus one-norm Bauer core | `problem7_10e_irreducible_transpose_products_canonical_scaled_oneCond_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_transpose_products_canonical_scaled_oneKappa_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_transpose_products_scaledOneKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_transpose_products_scaledOneKappaSet_isLeast_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_products_scaledOneKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector`, and `problem7_10e_irreducible_products_scaledOneKappaSet_isLeast_perron_of_nonzero_nonneg_eigenvector` | None for the strict-positivity side conditions; full source Problem 7.10(e) still needs PF/global minimization packaging |
| Problem 7.10(c)/(e), `CB(Cx)` algebra and 2-norm interpolation/`sInf` packaging for a supplied common scaling | Direct | 1 | Finite `matMulVec` associativity, integrated Chapter 6 complex finite `p`-norm interpolation `complexMatrixLpNormOfReal_rieszThorin_one_top`, exact `p = 2` bridge `complexMatrixLpNormOfReal_two_eq_complexMatrixOp2`, real/complex embedding `realRectToCMatrix`, repository `oneNorm`, `infNorm`, row/column-sum bounds, exact op-2 scaling value set, and `csInf_le` | `ch7_bauer_Cx_eigenvector_CB`, `ch7_complexMatrixOneNorm_realRectToCMatrix_le_oneNorm`, `ch7_complexMatrixInfNorm_realRectToCMatrix_le_infNorm`, `problem7_10e_complexMatrixOp2_realRectToCMatrix_le_sqrt_one_mul_inf`, `ch7TwoSidedScaledOp2Kappa`, `problem7_10e_scaled_op2Kappa_le_sqrt_oneKappa_mul_infKappa`, `problem7_10e_scaled_op2Kappa_le_of_one_inf_bounds`, `ch7TwoSidedScaledOp2Kappa_mem_set`, `problem7_10e_twoSidedScaledOp2Kappa_sInf_le_of_one_inf_bounds` | None for the algebra, fixed-scaling interpolation, or conditional `sInf` packaging; full source `inf κ₂ <= ρ(|A||A⁻¹|)` still needs the compatible Bauer/PF common-scaling existence proof |
| Problem 7.6(a), row-wise relative-data condition comparison | Direct | 1 | `condSkeel`, `matMulVec`, `infNormVec`, `oneNormVec` | `ch7RowwiseRelativeToleranceMatrix`, `ch7RowwiseDataCondAtSolutionInf`, `problem7_6a_rowwise_data_condition_bounds` | None |
| Problem 7.6(b), columnwise relative-data condition comparison | Direct | 1 | `infNorm`, `row_sum_le_infNorm`, `matMulVec`, `oneNormVec` | `ch7ColumnwiseRelativeToleranceMatrix`, `ch7AbsMatrixAbsVecOneNorm`, `ch7ColumnwiseDataCondAtSolutionInf`, `problem7_6b_columnwise_data_condition_bounds` | None |
| Problem 7.9 finite first-order componentwise and normwise scalar-output formulas plus `χ ≥ 1` lower-bound specializations | Direct | 1 | `summationAbsSign`, `summationAbsSign_mul_eq_abs`, `mul_summationAbsSign_eq_abs`, `abs_summationAbsSign`, `rectMatMulVec_left_inverse_of_IsLeftInverse`, `abs_vecInnerProduct_le_vecNorm2_mul`, `opNorm2Le`, `opNorm2Le_residualRankOnePerturbation` | `ch7Problem79AttainingDeltaA`, `ch7Problem79AttainingDeltaB`, `problem7_9_linearized_componentwise_functional_formula`, `problem7_9_linearized_componentwise_functional_ge_one_of_abs_matrix`, `problem7_9_linearized_componentwise_functional_ge_one_of_abs_rhs`, `ch7Problem79NormwiseAttainingDeltaA`, `ch7Problem79NormwiseAttainingDeltaB`, `problem7_9_linearized_normwise_functional_formula` | None |
| Problem 7.9 nonlinear componentwise source-radius condition number | Direct | 1 | `matMulVec_matMul`, `matMulVec_add_right`, `matMulVec_id`, `infNorm`, `infNormVec`, `infNorm_matMul_le`, `infNormVec_matMulVec_le`, `infNorm_absMatrix`, and finite-square inverse facts; current Chapter 7 local inverse candidate from Problem 7.11 | `ch7Problem79PerturbedSolutionWithInverse`, `ch7Problem79ExactScalarRelativeChange`, `problem7_9_exact_componentwise_relative_change_le_linearized_plus_quadratic`, `problem7_9_exact_componentwise_relative_change_ge_linearized_minus_quadratic`, `Ch7Problem79ComponentwiseExactRadiusSet`, `problem7_9_componentwise_exact_radiusSup_tendsto_linearized`, `problem7_9_componentwise_exact_condition_of_positive_radii` | None |
| Problem 7.9 nonlinear normwise source-radius condition number | Direct | 1 | `finiteBasisVec`, `abs_coord_le_vecNorm2`, `opNorm2Le`, `infNorm`, `infNormVec`, `infNorm_matMul_le`, `infNormVec_matMulVec_le`, `infNorm_absMatrix`, finite-square inverse facts, and the current Chapter 7 local inverse candidate from Problem 7.11 | `ch7Problem79NormwiseConstantEnvelopeMatrix`, `ch7Problem79_normwise_deltaA_componentwise_bound`, `ch7Problem79_normwise_deltaB_componentwise_bound`, `problem7_9_exact_normwise_relative_change_le_linearized_plus_quadratic`, `problem7_9_exact_normwise_relative_change_ge_linearized_minus_quadratic`, `Ch7Problem79NormwiseExactRadiusSet`, `problem7_9_normwise_exact_radiusSup_tendsto_linearized`, `problem7_9_normwise_exact_condition_of_positive_radii` | None |
| Problem 7.11 / Appendix A.11 first-order inverse componentwise formula | Direct | 1 | `summationAbsSign`, `summationAbsSign_mul_eq_abs`, `mul_summationAbsSign_eq_abs`, `abs_summationAbsSign` | `ch7AbsSign`, `ch7Problem711AttainingDelta`, `problem7_11_linearized_inverse_componentwise_formula` | None |

### 4. Not Formalized For Another Reason

| Source label/name | Classification | Previous-split dependency status | Exact reason | Destination split/chapter |
| --- | --- | --- | --- | --- |
| Theorems 7.5 and 7.8, equations (7.18)-(7.24), Problem 7.5, Problem 7.10 | `PROVE-NOW-SPLIT2` | No unresolved previous-split blocker; integrated foundations partially available | Problem 7.3 and equations `(7.15)`-`(7.16)` are closed for the positive-row-scaling/infinity-norm formulation, Problem 7.4 is closed for the unit-diagonal symmetric PSD scaled-factor form, equations `(7.20)`-`(7.21)` now have finite-real `p` lower/upper column-bound and column-equilibrated dependencies closed, equations `(7.20)`-`(7.21)` also have the `p = 2` operator-certificate/Frobenius column-equilibration dependency closed, Theorem 7.5 has the `p = 1` pairwise and exact `sInf` column-equilibration algebraic specialization closed through `(7.21)` and `(7.22)`, the `p = 2` pairwise and `sqrt(n) * sInf` column-equilibration condition-product specialization closed, the finite-real conjugate-row pairwise and `m^(1/p) * sInf` left-scaling specialization closed for `(7.19)`, the conditional source-`min` adapters closed for finite-real and `p = 2` non-endpoint value sets when an `IsLeast` certificate is supplied, the Penrose1-plus-matrix-rank adapters now close the same endpoint, `sInf`, and conditional `min` surfaces under `AA⁺A=A` plus the printed rank hypotheses, and the `p = ∞` pairwise and exact `sInf` row-equilibration algebraic specialization is closed for `(7.19)`; Corollary 7.6 / `(7.23)` is closed in the repository explicit inverse-Gram `sInf` model by the Cholesky source-scale, inverse-Gram, product-square, squared factor-infimum, and two-sided SPD `sInf` transfer theorems, without asserting minimizer attainment; Theorem 7.7 is closed by the Stewart-Sun Frobenius scaling package, Problem 7.10(a)'s two-sided Bauer scaling algebra and exact `sInf = ρ` value-set wrapper, Problem 7.10(b)'s inverse-transport plus absolute-value scaled-`κ∞` instantiation and exact `sInf = ρ` wrapper, Problem 7.10(c)'s `CB(Cx)` eigenvector algebra, the positive-entry product irreducibility adapter, Problem 7.10(d)'s source-shaped `Cx > 0` transfer, Problem 7.10(e)'s one-norm transpose-certificate branch, source-irreducible nonzero-nonnegative one-norm transpose wrappers, exact scaled-`κ₁` `sInf = ρ` wrapper, fixed-scaling 2-norm interpolation theorem, conditional `sInf` upper-bound packaging, and conditional Mathlib `spectralRadius` wrappers from source-shaped irreducible nonzero-nonnegative eigenpairs are closed under explicit Perron-vector/common-scaling certificates where applicable, Problem 7.15 is closed for the exact op-2 source lower-bound package, conditional attainability certificate, and nonsingular diagonal equality/least-value case, equation `(7.26)` is closed by the integrated relative singular-distance/condition-number wrapper, Problem 7.6(a)-(b) is closed for row-wise and columnwise relative data, Problem 7.9 has its finite first-order componentwise formula, finite `χ >= 1` lower-bound specializations, finite normwise first-order formula, first-order radius packages, and exact nonlinear componentwise and normwise source-radius `sSup` wrappers closed, and Problem 7.11 including equation `(7.25)` is closed for the componentwise source-radius `sSup` model; remaining rows need proof that the full Theorem 7.5 general/non-endpoint value sets attain the source minima, plus Perron-Frobenius eigenpair existence from irreducibility and proof that the compatible common Bauer scaling exists at the source spectral-radius value for the full `inf κ₂ <= ρ(|A||A⁻¹|)` statement | Current chapter / current split |
| Problem 7.12 | `DEFER-LATER-SPLIT` | No direct previous-split blocker recorded here | Symmetry-preserving backward error depends on later split QR/SPD integration | Later split |
| Problem 7.14 | `DEFER-LATER-SPLIT` | No direct previous-split blocker recorded here | Probability/distribution infrastructure not yet in scope for this split | Later split |
| Equation (7.17), equation (7.32) | `DEFER-LATER-CHAPTER` | No direct previous-split blocker recorded here | Symbolic/asymptotic follow-on rows remain intentionally after prerequisite generic norm/scaling work | Later Chapter 7 block |
| Equation (7.6) | `SKIP` | No previous-split dependency | Numerical illustration only | N/A |

Update 2026-06-25: in the Theorem 7.8 / Problem 7.10 row above, the old
phrase "Bauer variants (c)-(d) beyond the `CB(Cx)` algebra" is now narrowed to
the source-facing PF/spectral/common-scaling gap.  Problem 7.10(c)'s
`CB(Cx)` algebra and Problem 7.10(d)'s source-shaped irreducible-product
`Cx > 0` transfer are closed under a supplied positive Perron-vector
certificate by `ch7_bauer_Cx_eigenvector_CB`,
`ch7_perronScalar_pos_of_nonneg_irreducible_eigenvector`,
`problem7_10d_Cx_pos_of_irreducible_BC_CB`, and
`problem7_10d_abs_inverse_Cx_pos_of_irreducible_products`.

Update 2026-06-25 continuation: the same irreducible-product positivity bridge
now feeds back into Problem 7.10(b)'s scaled-`κ∞` theorem surface.  The new
wrappers `problem7_10b_irreducible_products_canonical_scaled_infKappa_eq_perron`
and `problem7_10b_irreducible_products_scaledInfKappaSet_sInf_eq_perron`
prove the canonical scaled product and exact `sInf = ρ` value-set equality from
irreducibility of both `|A||A⁻¹|` and `|A⁻¹||A|`, plus the supplied positive
Perron-vector certificate, instead of separately assuming `|A⁻¹|x > 0`.
This still does not close Perron-Frobenius existence, spectral-radius
identification, or the compatible common Bauer scaling at the source
spectral-radius value.

Update 2026-06-25 nonzero-nonnegative continuation: the strict positive-vector
certificate in the source-irreducible Bauer wrappers has been weakened to a
nonzero nonnegative right-eigenvector certificate.  The new local lemmas
`ch7_perronScalar_nonneg_of_nonzero_nonneg_eigenvector`,
`ch7_perronScalar_pos_of_nonzero_nonneg_irreducible_eigenvector`, and
`ch7_nonzero_nonneg_irreducible_right_eigenvector_pos` prove the positive
eigenvalue and full strict vector positivity from nonnegative irreducibility and
a supplied nonzero nonnegative eigenpair.  They feed the new Problem 7.10(a)
wrappers
`problem7_10a_irreducible_products_canonical_scaled_infCond_eq_perron_of_nonzero_nonneg_eigenvector`
and
`problem7_10a_irreducible_products_scaledInfCondSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector`,
and the Problem 7.10(b) wrappers
`problem7_10b_irreducible_products_canonical_scaled_infKappa_eq_perron_of_nonzero_nonneg_eigenvector`
and
`problem7_10b_irreducible_products_scaledInfKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector`.
This closes another certificate-level PF side condition locally, while the full
source theorem still needs existence of such an eigenpair and spectral-radius
identification.

### 0. Quantitative progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 98 | ~2 | The printed-rank Moore-Penrose construction, Penrose-equation witnesses, endpoint/`sInf` scaling wrappers, same-`A⁺` conditional source-`min` wrappers, and formal source-audit counterexample to the literal printed row-`∞` max-entry scaling are closed.  The Bauer block now has product/absolute/scaled/transpose Mathlib `spectralRadius` wrappers under source-shaped irreducibility plus supplied nonzero nonnegative eigenpairs; this removes the old conditional `spectralRadius` interface gap but does not prove Perron-Frobenius eigenpair existence.  Remaining Theorem 7.5 work is actual general/non-endpoint minimizer existence.  Remaining Theorem 7.8/Problem 7.10 work is Perron-Frobenius eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 theorem. | Medium-high |

### Additional required checks

- Build/test commands run in this pass: `lake env lean LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean`, `lake env lean LeanFpAnalysis/FP/Analysis/Norms.lean`, `lake build LeanFpAnalysis.FP.Analysis.Norms`, `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, redirected `lake env lean examples/LibraryLookup.lean`, `lake env lean /tmp/ch7_problem79_axioms.lean`, `lake env lean /tmp/ch7_problem79_exact_axioms.lean`, `lake env lean /tmp/ch7_problem79_normwise_exact_axioms.lean`, `lake env lean /tmp/ch7_problem711_radius_axioms.lean`, `lake env lean /tmp/ch7_problem711_asymptotic_bridge_axioms.lean`, `lake env lean /tmp/ch7_problem711_entry_bound_axioms.lean`, `lake env lean /tmp/ch7_problem711_infNorm_bound_axioms.lean`, `lake env lean /tmp/ch7_problem711_local_inverse_axioms.lean`, `lake env lean /tmp/ch7_problem711_radius_sup_axioms.lean`, `lake env lean /tmp/ch7_eq726_axioms.lean`, `lake env lean /tmp/ch7_theorem77_axioms.lean`, `lake env lean /tmp/ch7_eq720_eq721_axioms.lean`, `lake env lean /tmp/ch7_theorem75_p1_axioms.lean`, `lake env lean /tmp/ch7_theorem75_pinf_axioms.lean`, `lake env lean /tmp/ch7_bauer10b_axioms.lean`, `lake env lean /tmp/ch7_bauer_inverse_axioms.lean`, `lake env lean /tmp/ch7_bauer_irreducible_axioms.lean`, `lake env lean /tmp/ch7_bauer10e_axioms.lean`, `lake env lean /tmp/ch7_bauer10e_sinf_axioms.lean`, `lake env lean --stdin` for the latest Bauer `sInf = ρ` wrappers, `lake env lean /tmp/ch7_problem715_transpose_axioms.lean`, `lake env lean /tmp/ch7_problem715_hornjohnson_axioms.lean`, `lake env lean /tmp/ch7_problem715_op2inf_axioms.lean`, and `timeout 600s lake build` all passed where rerun after the relevant implementation step. The latest targeted Chapter 7 build passed with `3020` jobs; the full build passed with `3502` jobs and only the pre-existing `GivensSpec`/`GivensQR`/`FastMatMul` warnings. Two earlier `timeout 180s lake build` attempts timed out while compiling downstream modules, at `3482/3502` and `3493/3502`, without a Lean error. The earlier lookup and axiom runs that referenced newly added declarations exposed stale olean state before the targeted Chapter 7 build; after rebuilding the target, the lookup and axiom checks passed. The unredirected latest lookup check overflowed tool output, but the redirected rerun passed.
- Additional Theorem 7.5 `p = 2` condition-product verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for the five new p=2 declarations, focused implementation/lookup/report placeholder and stale-wait scans, focused conflict-marker scans over the touched Lean/report/log files, `git diff --check` over the touched Lean repository files, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs. The full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.
- Additional Theorem 7.5 explicit-`Aplus` `sInf` wrapper verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for `ch7OneNormRightScaledCondSet`, `theorem7_5_p1_column_equilibration_sInf_eq_right_scalings`, `ch7Op2RightScaledCondSet`, `ch7Op2RightScaledCondSet_nonempty`, `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings`, `ch7InfNormLeftScaledCondSet`, and `theorem7_5_pinf_row_equilibration_sInf_eq_left_scalings`, focused implementation/lookup/report placeholder and stale-label scans, focused conflict-marker scans, `git diff --check` over the touched Lean repository files, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs. The full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.
- Additional Theorem 7.5 endpoint least-element verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, `lake env lean /tmp/ch7_endpoint_minima_axioms.lean`, focused implementation/lookup placeholder scans, stale-wait scans, anchored trailing-whitespace/conflict-marker scans over the touched repo and FLARE dev-log files, `git diff --check` over the touched Lean repository files, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs. The full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.
- Additional Theorem 7.5 `p = 2` row-scaling verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, redirected `lake env lean examples/LibraryLookup.lean`, `lake env lean TmpCh7P2RowAxioms.lean` before deleting the temporary file, focused implementation/lookup placeholder scans, `git diff --check` over the touched Lean repository files, direct FLARE dev-log trailing-whitespace/conflict-marker scans, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.
- Additional Theorem 7.5 finite-real `p` equations `(7.20)`-`(7.21)` verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, redirected `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for the new finite-real `p` declarations, focused implementation/lookup placeholder scans, `git diff --check`, and `timeout 600s lake build` all passed after adding `ch7RectColumnLpNormOfReal`, `eq_7_20_column_lpNorm_le_matrixLpNormOfReal`, `ch7_complexVecLpNorm_realRect_matVec_le_sum_column_lpNorm`, `eq_7_20_matrixLpNormOfReal_le_card_rpow_mul_column_bound`, `ch7ColumnEquilibratingScaleLpOfReal`, `ch7RectColumnLpNormOfReal_rightScale`, `ch7RectColumnLpNormOfReal_rightScale_equilibrating`, and `eq_7_21_matrixLpNormOfReal_column_equilibrated`. The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.
- Additional Theorem 7.5 finite-real `p` explicit-`Aplus` `(7.18)`/`(7.22)` verification: `lake env lean LeanFpAnalysis/FP/Analysis/Norms.lean`, `lake build LeanFpAnalysis.FP.Analysis.Norms`, `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, redirected `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for `complexMatrixLpNormOfReal_mul_le`, `ch7_complexVecLpNormOfReal_diagScale_le_of_norm_le`, `eq_7_22_matrixLpNormOfReal_inverseSide_bound`, `theorem7_5_lp_column_equilibration_le_card_rpow_right_scaling`, and `theorem7_5_lp_column_equilibration_le_card_rpow_sInf_right_scalings`, strict implementation/lookup placeholder scans, conflict-marker/trailing-whitespace scans, `git diff --check`, and `timeout 600s lake build` all passed. The targeted `Norms` build completed with `2911` jobs, the targeted Chapter 7 build completed with `3020` jobs, and the full build completed with `3502` jobs with only the pre-existing QR/Givens/FastMatMul warnings. A first lookup run failed only because the fresh `Norms`/Chapter 7 declarations had not yet been rebuilt into `.olean`; after the targeted builds, lookup passed.
- Additional Theorem 7.5 finite-real `p` value-set verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, `lake env lean /tmp/ch7_finitep_valueset_axioms.lean`, focused implementation/lookup placeholder scans, anchored trailing-whitespace/conflict-marker scans over the touched repo and FLARE dev-log files, `git diff --check` over the touched Lean repository files, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs. The full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.
- Additional Theorem 7.5 finite-real conjugate-row `(7.19)` verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for `eq_7_19_matrixLpNormOfReal_dual_row_equilibrated`, `eq_7_19_matrixLpNormOfReal_dual_row_inverseSide_bound`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_left_scaling`, and `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings`, focused implementation/lookup placeholder scans, report stale-wait scan, typo scan, `git diff --check`, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.
- Additional Theorem 7.5 one-sided-inverse side-condition verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for the twelve new rank/positivity and source-shaped wrapper declarations, focused implementation/lookup placeholder and stale-label scans, conflict-marker/trailing-whitespace scans over the touched repository and FLARE dev-log files, `git diff --check` over the touched repository files, a source re-audit of the Theorem 7.5 PDF passage, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only pre-existing QR/Givens/FastMatMul warnings. The source audit confirmed that the new wrappers model the printed rank side conditions through explicit one-sided inverse witnesses, while the full Moore-Penrose/projection/general minimizer-existence package remains open.
- Additional Theorem 7.5 Matrix-rank source side-condition verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, redirected `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for the eight new Matrix-rank declarations, focused implementation/lookup placeholder and stale-label scans, `git diff --check` over the touched repository files, a source re-audit of the Theorem 7.5 PDF passage, and `timeout 600s lake build` passed. The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings. The source audit confirmed that the new wrappers model the printed real Matrix-rank side conditions `(Matrix.of A).rank = n/m`; the full Moore-Penrose/projection/general minimizer-existence package remains open.
- Additional Corollary 7.6 inverse-Gram/product-square verification: `lake env lean LeanFpAnalysis/FP/Analysis/Norms.lean`, `lake build LeanFpAnalysis.FP.Analysis.Norms`, `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms`, focused implementation/lookup/report placeholder and stale-label scans, `git diff --check`, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs. The full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.
- Additional Corollary 7.6 inverse-Gram/product-square `#print axioms` results for `complexMatrixOp2_adjoint_mul_self_eq_sq`, `complexMatrixOp2_mul_adjoint_self_eq_sq`, `complexMatrixOp2_realRectToCMatrix_transpose_mul_self_eq_sq`, `complexMatrixOp2_realRectToCMatrix_mul_transpose_self_eq_sq`, `corollary7_6_cholesky_scaled_cond_eq_factor_cond_sq`, `corollary7_6_cholesky_inverse_gram_isInverse`, and `corollary7_6_cholesky_scaled_inverse_gram_isInverse` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Corollary 7.6 squared factor-infimum verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with fully qualified `#print axioms` for `LeanFpAnalysis.FP.ch7Op2RightScaledCondSet_sInf_nonneg` and `LeanFpAnalysis.FP.corollary7_6_cholesky_scaled_cond_le_card_sInf_right_scalings_sq`, focused implementation/lookup/report placeholder and stale-label scans, `git diff --check`, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs. The full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings. An earlier unqualified stdin axiom command failed only because it did not open the `LeanFpAnalysis.FP` namespace.
- Additional Corollary 7.6 squared factor-infimum `#print axioms` results for `ch7Op2RightScaledCondSet_sInf_nonneg` and `corollary7_6_cholesky_scaled_cond_le_card_sInf_right_scalings_sq` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Corollary 7.6 two-sided `sInf` transfer verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, redirected `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for `ch7SymmetricOp2ScaledCondSet_nonempty`, `ch7SymmetricOp2ScaledCondSet_bddBelow`, `corollary7_6_cholesky_right_sInf_sq_le_symmetric_sInf`, and `corollary7_6_cholesky_scaled_cond_le_card_sInf_symmetric_scalings`, focused implementation/lookup placeholder and stale-label scans, focused report stale-Corollary-blocker scan, `git diff --check`, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs. The full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings. An unredirected lookup run returned nonzero only because the tool output was too large; the redirected rerun passed.
- Additional Corollary 7.6 two-sided `sInf` transfer `#print axioms` results for `ch7SymmetricOp2ScaledCondSet_nonempty`, `ch7SymmetricOp2ScaledCondSet_bddBelow`, `corollary7_6_cholesky_right_sInf_sq_le_symmetric_sInf`, and `corollary7_6_cholesky_scaled_cond_le_card_sInf_symmetric_scalings` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Bauer-pass verification: `lake env lean /tmp/ch7_bauer_axioms.lean` passed after rebuilding `LeanFpAnalysis.FP.Analysis.HighamChapter7`; it printed only `propext`, `Classical.choice`, and `Quot.sound` for `ch7_infNorm_ge_of_nonneg_right_eigenvector`, `problem7_10a_scaled_infCond_ge_perron_of_positive_eigenvector`, `problem7_10a_canonical_scaled_infCond_eq_perron_of_positive_eigenvector`, and `problem7_10a_positive_entries_canonical_scaled_infCond_eq_perron`.
- Additional Bauer 7.10(b) verification: `lake env lean /tmp/ch7_bauer10b_axioms.lean` passed after rebuilding `LeanFpAnalysis.FP.Analysis.HighamChapter7`; it printed only `propext`, `Classical.choice`, and `Quot.sound` for `ch7TwoSidedScale_absMatrix_eq`, `ch7_infNorm_twoSidedScale_absMatrix_eq`, `ch7TwoSidedScaledInfKappa_eq_abs_scaledInfCond`, `problem7_10b_scaled_infKappa_ge_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_canonical_scaled_infKappa_eq_perron_of_abs_inverse_positive_eigenvector`, and `problem7_10b_positive_abs_entries_canonical_scaled_infKappa_eq_perron`.
- Additional Bauer inverse-transport verification: `lake env lean /tmp/ch7_bauer_inverse_axioms.lean` passed after rebuilding `LeanFpAnalysis.FP.Analysis.HighamChapter7`; it printed only `propext`, `Classical.choice`, and `Quot.sound` for `ch7TwoSidedScale_isLeftInverse`, `ch7TwoSidedScale_isRightInverse`, `ch7TwoSidedScale_isInverse`, and `ch7TwoSidedScaledInfKappa_eq_kappaInf_of_inverse`.
- Additional Bauer irreducibility verification: `lake env lean /tmp/ch7_bauer_irreducible_axioms.lean` passed after rebuilding `LeanFpAnalysis.FP.Analysis.HighamChapter7`; it printed only `propext`, `Classical.choice`, and `Quot.sound` for `ch7_matrix_isPrimitive_of_pos_entries`, `ch7_matrix_isIrreducible_of_pos_entries`, `ch7_matMul_pos_of_pos`, `ch7_bauer_positive_products_irreducible`, and `problem7_10b_positive_abs_entries_products_irreducible`.
- Additional Bauer 7.10(e) one-norm verification: `lake env lean /tmp/ch7_bauer10e_axioms.lean` passed after rebuilding `LeanFpAnalysis.FP.Analysis.HighamChapter7`; it printed only `propext`, `Classical.choice`, and `Quot.sound` for `ch7TwoSidedScaledOneCond_eq_transpose_infCond`, `problem7_10e_scaled_oneCond_ge_perron_of_transpose_positive_eigenvector`, `problem7_10e_canonical_scaled_oneCond_eq_perron_of_transpose_positive_eigenvector`, `problem7_10e_positive_entries_canonical_scaled_oneCond_eq_perron_of_transpose`, `ch7TwoSidedScaledOneKappa_eq_abs_scaledOneCond`, `problem7_10e_scaled_oneKappa_ge_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_canonical_scaled_oneKappa_eq_perron_of_abs_inverse_transpose_positive_eigenvector`, and `problem7_10e_positive_abs_entries_canonical_scaled_oneKappa_eq_perron_of_transpose`.
- Additional Bauer 7.10(e) fixed-scaling 2-norm verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, `lake env lean /tmp/ch7_bauer10e_op2_axioms.lean`, focused placeholder/conflict-marker scans, `git diff --check`, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs. The full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings. The first lookup run before the targeted Chapter 7 build failed only because the fresh `HighamChapter7.olean` did not yet exist; after rebuilding the target, lookup passed.
- Additional Bauer 7.10(e) fixed-scaling 2-norm `#print axioms` results: `ch7_complexMatrixOneNorm_realRectToCMatrix_le_oneNorm`, `ch7_complexMatrixInfNorm_realRectToCMatrix_le_infNorm`, `problem7_10e_complexMatrixOp2_realRectToCMatrix_le_sqrt_one_mul_inf`, `problem7_10e_scaled_op2Kappa_le_sqrt_oneKappa_mul_infKappa`, and `problem7_10e_scaled_op2Kappa_le_of_one_inf_bounds` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Bauer 7.10(c)/(e) `CB(Cx)` and conditional `sInf` packaging verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, `lake env lean /tmp/ch7_bauer10e_sinf_axioms.lean`, focused implementation/lookup/report placeholder and stale-wait scans, conflict-marker scans, FLARE dev-log whitespace/conflict scans, `git diff --check`, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs. The full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.
- Additional Bauer 7.10(c)/(e) `#print axioms` results: `ch7_bauer_Cx_eigenvector_CB`, `ch7TwoSidedScaledOp2Kappa_mem_set`, and `problem7_10e_twoSidedScaledOp2Kappa_sInf_le_of_one_inf_bounds` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Bauer 7.10(e) op-2 value-set lower-bound infrastructure verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, a fully qualified `lake env lean --stdin` `#print axioms` probe, the focused implementation/lookup placeholder scan, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings. `ch7TwoSidedScaledOp2KappaSet_bddBelow` and `ch7TwoSidedScaledOp2KappaSet_sInf_nonneg` report only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional scaling value-set nonnegative-infimum verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with fully qualified `#print axioms` for the five new declarations, focused implementation/lookup placeholder and stale-wait scans, anchored conflict-marker scans, `git diff --check` over the touched Lean repository files, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings. The broad report scan matched only historical scan prose and standard axiom-summary text, not Lean implementation or lookup placeholders.
- Additional scaling value-set nonnegative-infimum `#print axioms` results for `ch7Op2LeftScaledCondSet_sInf_nonneg`, `ch7SymmetricOp2ScaledCondSet_sInf_nonneg`, `ch7TwoSidedScaledInfCondSet_sInf_nonneg`, `ch7TwoSidedScaledInfKappaSet_sInf_nonneg`, and `ch7TwoSidedScaledOneKappaSet_sInf_nonneg` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Bauer 7.10(d) irreducible-positivity verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for the four new irreducibility/Mathlib-power bridge declarations, focused implementation/lookup placeholder scans, `git diff --check` over the touched Lean repository files, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs. The full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.
- Additional Bauer 7.10(d) `#print axioms` results: `ch7_matrix_mulVec_eq_matMulVec`, `ch7_matrix_pow_mulVec_eigen`, `ch7_nonneg_irreducible_right_eigenvector_pos`, and `problem7_10d_Cx_pos_of_irreducible_CB` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Bauer 7.10(d) strict-eigenvalue verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, and `lake env lean /tmp/ch7_new_axioms.lean` passed. The axiom harness printed `#print axioms` for `ch7_perronScalar_pos_of_nonneg_eigenvector_entry_pos` and `problem7_10d_Cx_pos_of_irreducible_CB_of_positive_BC_entry`; both report only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Bauer 7.10(d) source-shaped irreducible-product verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for `ch7_perronScalar_pos_of_nonneg_irreducible_eigenvector`, `problem7_10d_Cx_pos_of_irreducible_BC_CB`, and `problem7_10d_abs_inverse_Cx_pos_of_irreducible_products`, focused implementation/lookup placeholder scans, report stale-label scans, `git diff --check`, `pdftotext` source re-audit of Theorem 7.8 / Problem 7.10, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings. The implementation/lookup scans found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, stale wait label, `placeholder`, or `False.elim` matches; report-inclusive scans matched only historical scan prose and standard axiom-summary text.
- Additional Bauer 7.10(d) source-shaped irreducible-product `#print axioms` results: `ch7_perronScalar_pos_of_nonneg_irreducible_eigenvector`, `problem7_10d_Cx_pos_of_irreducible_BC_CB`, and `problem7_10d_abs_inverse_Cx_pos_of_irreducible_products` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Bauer 7.10(b) irreducible-products scaled-`κ∞` wrapper verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, redirected `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for `problem7_10b_irreducible_products_canonical_scaled_infKappa_eq_perron` and `problem7_10b_irreducible_products_scaledInfKappaSet_sInf_eq_perron`, focused implementation/lookup placeholder and stale-label scans, conflict-marker scan, `git diff --check` over the touched Lean repository files, `pdftotext` source re-audit of Problem 7.10, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings. An unredirected lookup check produced a very large `#check` stream and exited nonzero at the tool/output layer; the redirected rerun passed with status `0`.
- Additional Bauer 7.10(b) irreducible-products scaled-`κ∞` wrapper `#print axioms` results: `problem7_10b_irreducible_products_canonical_scaled_infKappa_eq_perron` and `problem7_10b_irreducible_products_scaledInfKappaSet_sInf_eq_perron` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Bauer nonzero-nonnegative irreducible-eigenvector continuation verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, redirected `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for `ch7_perronScalar_nonneg_of_nonzero_nonneg_eigenvector`, `ch7_perronScalar_pos_of_nonzero_nonneg_irreducible_eigenvector`, `ch7_nonzero_nonneg_irreducible_right_eigenvector_pos`, `problem7_10a_irreducible_products_canonical_scaled_infCond_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10a_irreducible_products_scaledInfCondSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10b_irreducible_products_canonical_scaled_infKappa_eq_perron_of_nonzero_nonneg_eigenvector`, and `problem7_10b_irreducible_products_scaledInfKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector`, focused implementation/lookup placeholder scans, anchored conflict-marker/trailing-whitespace scans, `git diff --check` over the touched Lean repository files, `pdftotext` source re-audit of Problem 7.10, and `timeout 600s lake build` passed. The first lookup run failed only because the freshly edited Chapter 7 module had not yet been rebuilt into `.olean`; after the targeted Chapter 7 build, the redirected lookup passed. The full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.
- Additional Bauer nonzero-nonnegative irreducible-eigenvector `#print axioms` results: the helper `ch7_exists_pos_entry_of_nonzero_nonneg` and the seven new final-facing declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Bauer 7.10(e) one-norm transpose nonzero-nonnegative continuation verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, redirected `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with fully qualified `#print axioms` for `problem7_10e_irreducible_transpose_products_canonical_scaled_oneCond_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_transpose_products_canonical_scaled_oneKappa_eq_perron_of_nonzero_nonneg_eigenvector`, and `problem7_10e_irreducible_transpose_products_scaledOneKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector`, focused implementation/lookup placeholder scans, line-anchored conflict-marker and trailing-whitespace scans, `git diff --check` over the touched Lean repository files, `pdftotext` source re-audit of Theorem 7.8 / Problem 7.10, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs. The first redirected lookup check failed before the targeted build because the fresh declarations were not yet available in the built `.olean`; after rebuilding, the redirected lookup passed. The full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.
- Additional Bauer 7.10(e) one-norm transpose nonzero-nonnegative `#print axioms` results: the three new final-facing declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Bauer 7.10(e) source-product one-norm irreducibility verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for `ch7_irreducible_transpose_product_of_irreducible_product`, `problem7_10e_irreducible_products_canonical_scaled_oneCond_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_products_canonical_scaled_oneKappa_eq_perron_of_nonzero_nonneg_eigenvector`, and `problem7_10e_irreducible_products_scaledOneKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector`, focused implementation/lookup placeholder scans, `git diff --check`, `pdftotext` source re-audit of Theorem 7.8 / Problem 7.10, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings. The unredirected lookup emitted a large `#check` stream but exited `0`.
- Additional Bauer 7.10(e) source-product one-norm irreducibility `#print axioms` results: `ch7_irreducible_transpose_product_of_irreducible_product`, `problem7_10e_irreducible_products_canonical_scaled_oneCond_eq_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_irreducible_products_canonical_scaled_oneKappa_eq_perron_of_nonzero_nonneg_eigenvector`, and `problem7_10e_irreducible_products_scaledOneKappaSet_sInf_eq_perron_of_nonzero_nonneg_eigenvector` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Bauer certificate-level `sInf = ρ` equality verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, redirected `lake env lean examples/LibraryLookup.lean`, focused implementation/lookup placeholder scans, `git diff --check` over the touched Lean repository files, and `lake env lean --stdin` with `#print axioms` for `problem7_10a_scaledInfCondSet_sInf_eq_perron_of_positive_eigenvector`, `problem7_10a_positive_entries_scaledInfCondSet_sInf_eq_perron`, `problem7_10b_scaledInfKappaSet_sInf_eq_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_positive_abs_entries_scaledInfKappaSet_sInf_eq_perron`, `problem7_10e_scaledOneKappaSet_sInf_eq_perron_of_abs_inverse_transpose_positive_eigenvector`, and `problem7_10e_positive_abs_entries_scaledOneKappaSet_sInf_eq_perron_of_transpose` all passed. The targeted Chapter 7 build completed with `3020` jobs.
- Additional Bauer certificate-level `sInf = ρ` `#print axioms` results: the six new final-facing theorems use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Bauer certificate-level `IsLeast` minimum-attainment verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, redirected `lake env lean examples/LibraryLookup.lean`, and `lake env lean --stdin` with `#print axioms` for the new Problem 7.10(a)/(b)/(e) least-value wrappers all passed. The first lookup run before the target rebuild failed only because the fresh `.olean` was not yet available; after rebuilding the target, lookup passed.
- Additional Bauer certificate-level `IsLeast` `#print axioms` results: `problem7_10a_scaledInfCondSet_isLeast_perron_of_positive_eigenvector`, `problem7_10a_irreducible_products_scaledInfCondSet_isLeast_perron_of_nonzero_nonneg_eigenvector`, `problem7_10b_scaledInfKappaSet_isLeast_perron_of_abs_inverse_positive_eigenvector`, `problem7_10b_irreducible_products_scaledInfKappaSet_isLeast_perron_of_nonzero_nonneg_eigenvector`, `problem7_10e_scaledOneKappaSet_isLeast_perron_of_abs_inverse_transpose_positive_eigenvector`, and `problem7_10e_irreducible_products_scaledOneKappaSet_isLeast_perron_of_nonzero_nonneg_eigenvector` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Bauer finite complex eigenvalue-radius verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, redirected `lake env lean examples/LibraryLookup.lean`, `lake env lean /tmp/ch7_spectral_axioms.lean`, focused implementation/lookup placeholder scans, line-anchored conflict-marker scans, trailing-whitespace scans over touched Lean, report, and FLARE log files, `git diff --check` over touched Lean-repository files, `pdftotext -layout` source re-audit of Theorem 7.8 / Problem 7.10, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings. The first redirected lookup run exited nonzero without surfaced errors before the target rebuild had completed; the redirected rerun after the targeted build passed with status `0`.
- Additional Bauer finite complex eigenvalue-radius `#print axioms` results: `ch7_complex_eigenvalue_norm_le_of_positive_real_eigenvector`, `ch7_isComplexEigenvalueRadius_of_positive_real_eigenvector`, `problem7_10a_product_isComplexEigenvalueRadius_of_positive_eigenvector`, and `problem7_10b_abs_product_isComplexEigenvalueRadius_of_positive_eigenvector` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Bauer local eigenvalue-modulus `sSup` verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, redirected `lake env lean examples/LibraryLookup.lean`, `lake env lean /tmp/ch7_spectral_sup_axioms.lean`, focused implementation/lookup placeholder scans, line-anchored conflict-marker scans, trailing-whitespace scans over touched Lean, report, and FLARE log files, `git diff --check` over touched Lean-repository files, `pdftotext -layout` source re-audit of Theorem 7.8 / Problem 7.10, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings. The first redirected lookup run before the target rebuild failed because the fresh declarations were not yet available in the built `.olean`; after the targeted build, the redirected lookup passed with status `0`.
- Additional Bauer local eigenvalue-modulus `sSup` `#print axioms` results: `ch7_complexEigenvalueModulusSet_isGreatest_of_isComplexEigenvalueRadius`, `ch7_complexEigenvalueModulusSet_sSup_eq_of_isComplexEigenvalueRadius`, `problem7_10a_product_complexEigenvalueModulusSet_isGreatest_of_positive_eigenvector`, `problem7_10a_product_complexEigenvalueModulusSet_sSup_eq_of_positive_eigenvector`, `problem7_10b_abs_product_complexEigenvalueModulusSet_isGreatest_of_positive_eigenvector`, and `problem7_10b_abs_product_complexEigenvalueModulusSet_sSup_eq_of_positive_eigenvector` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Bauer scaled-product local spectral-radius verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean --tstack=65536 examples/LibraryLookup.lean`, and `lake env lean --stdin` with `open LeanFpAnalysis.FP` and `#print axioms` for the three new scaled-product spectral wrappers all passed. The targeted Chapter 7 build completed with `3020` jobs. The first lookup and axiom probes before the targeted build used stale `.olean` files or lacked the namespace opening and failed only with unknown fresh declarations; after rebuilding and using the same namespace context as `examples/LibraryLookup.lean`, both checks passed.
- Additional Bauer scaled-product local spectral-radius `#print axioms` results: `problem7_10a_scaled_product_isComplexEigenvalueRadius_of_positive_eigenvector`, `problem7_10a_scaled_product_complexEigenvalueModulusSet_isGreatest_of_positive_eigenvector`, and `problem7_10a_scaled_product_complexEigenvalueModulusSet_sSup_eq_of_positive_eigenvector` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Post-sync scaled-product verification: after updating the unified Split 2 report and FLARE dev logs, focused implementation/lookup placeholder scans, conflict-marker scans, trailing-whitespace scans, `git diff --check` over touched repository files, a fresh `pdftotext -layout` source re-audit of Theorem 7.8 / Problem 7.10, `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean --tstack=65536 examples/LibraryLookup.lean`, namespace-aware `#print axioms` probes for the three scaled-product wrappers, and `timeout 600s lake build` all passed. The full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul linter warnings.
- Additional Bauer Mathlib `spectralRadius` bridge verification: the first direct `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` check after editing failed only because the freshly added `Norms.lean` declarations had not yet been rebuilt into `.olean`; after `lake build LeanFpAnalysis.FP.Analysis.Norms`, the targeted `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3020` jobs. The updated lookup check `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch7_spectral_radius_lookup.out` passed and the output includes all new `toLin_spectralRadius...` and Problem 7.10 `...toLin_spectralRadius_eq...` declarations. Namespace-aware `#print axioms` probes for `toLin_spectralRadius_eq_of_spectrum_modulusSet_isGreatest`, `toLin_spectralRadius_toReal_eq_of_spectrum_modulusSet_isGreatest`, `complexMatrix_toLin_spectralRadius_eq_of_isMaxComplexMatrixEigenvalueModulus`, `ch7_toLin_spectralRadius_eq_of_isComplexEigenvalueRadius`, `ch7_toLin_spectralRadius_toReal_eq_of_isComplexEigenvalueRadius`, `problem7_10a_product_toLin_spectralRadius_eq_of_positive_eigenvector`, `problem7_10b_abs_product_toLin_spectralRadius_eq_of_positive_eigenvector`, and `problem7_10a_scaled_product_toLin_spectralRadius_eq_of_positive_eigenvector` passed.
- Additional Bauer Mathlib `spectralRadius` bridge hygiene/source audit: focused implementation/lookup/report leading-placeholder scans found no `sorry`, `admit`, `axiom`, `unsafe`, or `opaque` declarations. A broader implementation/lookup scan found only pre-existing `False.elim` occurrences in `Norms.lean` and one ordinary doc-comment occurrence of "bounded"; conflict-marker and trailing-whitespace scans over touched repository files and FLARE dev logs returned no matches. `git diff --check` over the touched Lean repository files passed; `/home/mymel/flare-bundle/dev-logs` is outside this Lean git repository, so whitespace there was checked by the explicit `rg` scan. Fresh `pdftotext -layout` extraction of Chapter 7 and Appendix A re-confirmed that Theorem 7.8 and Problem 7.10 use `ρ` as spectral radius, positive Perron vectors, and the Bauer scaling route. Full `timeout 600s lake build` passed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul linter warnings.
- Additional Bauer nonzero-nonnegative irreducible `spectralRadius` continuation verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean --tstack=65536 examples/LibraryLookup.lean > /tmp/ch7_irred_spectral_lookup.out`, namespace-aware `lake env lean --stdin` `#print axioms` for `problem7_10a_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector`, `problem7_10b_abs_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector`, `problem7_10a_scaled_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector`, and `problem7_10e_abs_transpose_product_toLin_spectralRadius_eq_of_irreducible_nonzero_nonneg_eigenvector`, focused implementation/lookup placeholder scan, conflict-marker scan, trailing-whitespace scan, `git diff --check`, `pdftotext -layout` source re-audit of Theorem 7.8 / Problem 7.10, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings. The broad report-inclusive placeholder scan matched only historical report command strings and axiom-summary prose, not implementation or lookup code.
- Additional Bauer nonzero-nonnegative irreducible `spectralRadius` `#print axioms` results: the four new final-facing wrappers use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 Penrose-bridge verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean --tstack=65536 examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for the new Penrose bridge/projection declarations, focused implementation/lookup placeholder scans, anchored conflict-marker scans, trailing-whitespace scans, `git diff --check` over touched repository files, `pdftotext -layout` source re-audit of Theorem 7.5, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings. The broad unredirected lookup run emitted a very large `#check` stream but exited `0`.
- Additional Theorem 7.5 Penrose-bridge `#print axioms` results: `theorem7_5_rect_left_inverse_of_penrose1_rectMatMulVec_injective`, `theorem7_5_rect_right_inverse_of_penrose1_rectMatMulVec_surjective`, `theorem7_5_rect_left_inverse_of_penrose1_matrix_rank_eq_width`, `theorem7_5_rect_right_inverse_of_penrose1_matrix_rank_eq_height`, `theorem7_5_rect_penrose_injective_symmetric_range_projection_op2Le_one`, `theorem7_5_rect_penrose_surjective_symmetric_domain_projection_op2Le_one`, `theorem7_5_rect_penrose_injective_symmetric_range_projection_residual_normSq_isLeast`, `theorem7_5_rect_penrose_surjective_symmetric_domain_projection_residual_normSq_isLeast`, `theorem7_5_rect_penrose_matrix_rank_eq_width_symmetric_range_projection_residual_normSq_isLeast`, and `theorem7_5_rect_penrose_matrix_rank_eq_height_symmetric_domain_projection_residual_normSq_isLeast` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 Penrose-equation package verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` (`3020` jobs), `lake env lean --tstack=65536 examples/LibraryLookup.lean`, `lake env lean /tmp/ch7_penrose_equations_axioms.lean`, focused implementation/lookup placeholder scans, anchored conflict-marker scans, trailing-whitespace scans, `git diff --check` over touched repository files, and `pdftotext -layout` source re-audit of Theorem 7.5 passed.  The source re-audit confirms Theorem 7.5 defines `κp(A)` with `A+` as the pseudoinverse and states the printed rank/minimum inequalities `(7.18)` and `(7.19)`, so the new package correctly closes only the algebra from one-sided inverse/projection-symmetry witnesses to the four Penrose conditions, not the pseudoinverse construction.
- Additional Theorem 7.5 Penrose-equation package `#print axioms` results: `theorem7_5_rect_left_inverse_symmetric_penrose_equations`, `theorem7_5_rect_right_inverse_symmetric_penrose_equations`, `theorem7_5_rect_penrose_injective_symmetric_range_penrose_equations`, `theorem7_5_rect_penrose_surjective_symmetric_domain_penrose_equations`, `theorem7_5_rect_penrose_matrix_rank_eq_width_symmetric_range_penrose_equations`, and `theorem7_5_rect_penrose_matrix_rank_eq_height_symmetric_domain_penrose_equations` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Final current-pass hygiene/build verification: focused implementation/lookup placeholder scan found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, stale wait label, `TODO`, `FIXME`, `False.elim`, `by sorry`, or local placeholder matches; conflict-marker/trailing-whitespace scan over touched implementation, lookup, report, and FLARE log files found no matches; `git diff --check` over touched repository files passed; `pdftotext -layout` source re-audit confirmed Theorem 7.5 states the pseudo-inverse/rank/minimization surface and that the new bridge/package does not construct the Moore-Penrose inverse or prove the first Penrose equation/projection-symmetry witnesses for that construction; and full `timeout 600s lake build` passed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.
- Additional Problem 7.15 Hadamard-scaling verification: `lake env lean /tmp/ch7_problem715_axioms.lean` passed after rebuilding `LeanFpAnalysis.FP.Analysis.HighamChapter7`; it printed only `propext`, `Classical.choice`, and `Quot.sound` for `ch7_matTranspose_twoSidedScale`, `ch7HadamardProduct_twoSidedScale_transpose_inverse_eq`, and `problem7_15_twoSidedScale_hadamard_transpose_inverse_invariant`. The new Horn-Johnson harness `lake env lean /tmp/ch7_problem715_hornjohnson_axioms.lean` also passed and printed only `propext`, `Classical.choice`, and `Quot.sound` for `frobNormRect_diagMatrix`, `vecNorm2_diagonal_le_frobNormRect`, `matMulVec_hadamard_eq_diag_rectMatMul_diag_transpose`, `opNorm2Le_hadamard`, `problem7_15_hornJohnson_hadamard_opNorm2Le`, and `problem7_15_scaled_inverse_hadamard_opNorm2Le`.
- Additional Problem 7.15 exact-op2 infimum verification: `lake env lean /tmp/ch7_problem715_op2inf_axioms.lean` passed after rebuilding `LeanFpAnalysis.FP.Analysis.Norms` and `LeanFpAnalysis.FP.Analysis.HighamChapter7`; it printed only `propext`, `Classical.choice`, and `Quot.sound` for `complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le`, `opNorm2Le_complexMatrixOp2_realRectToCMatrix`, `ch7TwoSidedScaledOp2KappaSet_nonempty`, `problem7_15_hadamard_op2_le_twoSidedScaledOp2Kappa_mem`, `problem7_15_twoSidedScaledOp2Kappa_sInf_ge_hadamard_op2`, `problem7_15_twoSidedScaledOp2Kappa_sInf_ge_hadamard_op2_of_inverse`, `problem7_15_twoSidedScaledOp2Kappa_sInf_eq_hadamard_op2_of_mem`, and `problem7_15_twoSidedScaledOp2Kappa_sInf_eq_hadamard_op2_of_attaining_scaling`.
- Additional Problem 7.15 least-value attainability verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, redirected `lake env lean --tstack=65536 examples/LibraryLookup.lean`, and a fully qualified `lake env lean --stdin` `#print axioms` probe passed for `problem7_15_twoSidedScaledOp2Kappa_isLeast_hadamard_op2_of_mem` and `problem7_15_twoSidedScaledOp2Kappa_isLeast_hadamard_op2_of_attaining_scaling`; both new declarations report only `propext`, `Classical.choice`, and `Quot.sound`. The first axiom attempt before the target rebuild used an obsolete namespace/open line and failed without adopting any result; the rerun after the 3020-job Chapter 7 build passed.
- Additional Problem 7.15 least-value hygiene/source audit: focused implementation/lookup/report scans found no leading `sorry`, `admit`, `axiom`, `unsafe`, or `opaque`, no implementation/lookup `False.elim`, `by sorry`, `TODO`, `FIXME`, stale wait labels, or `placeholder` labels, and no conflict markers or trailing whitespace in the touched files. `git diff --check` over touched repository files passed. `pdftotext` source re-audit of Chapter 7 Problem 7.15 and Appendix A.7.15 confirmed the source lower-bound statement plus attainability discussion. Full `timeout 600s lake build` passed with 3502 jobs and only the known pre-existing QR/Givens/FastMatMul warnings.
- Additional Problem 7.15 nonsingular-diagonal attainability verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed before report updates; `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with 3020 jobs; `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed, with a redirected rerun saved to `/tmp/ch7_lookup_latest.out`; fully qualified `lake env lean --stdin` `#print axioms` probes passed for `problem7_15_complexMatrixOp2_realRectToCMatrix_orthogonal_eq_one`, `problem7_15_diagonal_hadamard_op2_eq_one`, `problem7_15_diagonal_attaining_scaling_eq_hadamard_op2`, `problem7_15_diagonal_twoSidedScaledOp2Kappa_sInf_eq_one`, and `problem7_15_diagonal_twoSidedScaledOp2Kappa_isLeast_one`; focused implementation/lookup placeholder/stale-label scans, conflict-marker scans, trailing-whitespace scans, and `git diff --check` passed; `pdftotext` source re-audit confirmed the Chapter 7 Problem 7.15 statement and Appendix A.7.15 diagonal-equality sentence; full `timeout 600s lake build` passed with 3502 jobs and only the known pre-existing QR/Givens/FastMatMul warnings.
- Source re-audit: extracted `/home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.ch7.pdf` and `1.9780898718027.appa.pdf` with `pdftotext`, and rendered PDF pages around Theorem 7.5 with `pdftotext -layout`; Theorem 7.5 and Corollary 7.6 source around equations (7.18)-(7.23) state a full Moore-Penrose/pseudoinverse/projection and diagonal-minimization theorem for general `p`. The finite-real `p` Lean declarations now match equations `(7.20)`-`(7.21)` in bound form: every column norm is bounded by the local least matrix `p`-norm, a uniform column bound `B` gives `‖A‖_p <= n^(1-1/p) B`, and reciprocal column equilibration yields `‖A D_C‖_p <= n^(1-1/p)` when the source column norms are positive. The new conjugate-row declarations close the finite-real `p` proof route for `(7.19)` generated by the source's transpose identity `κ_p(DA) = κ_q(AᵀD)`, using reciprocal `q`-row norms; the rendered PDF prints `D_R := diag(‖A(i,:)‖_p)^{-1}`, so the full printed row-scale packaging remains open rather than being silently identified with the conjugate-row model. The `p = 1` and `p = ∞` endpoint explicit-`Aplus` models now have genuine least-element/attainment witnesses; the `p = 2`, finite-real column, and conjugate-row Lean theorems have pairwise, `sInf`, and conditional source-`min` adapters where an `IsLeast` value certificate is supplied, but they are not the full Moore-Penrose source theorem and do not prove minimizer existence. Chapter 7 Problem 7.9 states the normwise constraints `‖ΔA‖₂ ≤ ε‖E‖₂` and `‖Δb‖₂ ≤ ε‖f‖₂`, and Appendix A.7.9 gives `ψ_{E,f}(A,x) = ‖c^T A⁻¹‖₂(‖f‖₂+‖E‖₂‖x‖₂)/|c^T x|`, matching the new Lean value.
- Post-transfer Corollary 7.6 source re-audit: re-extracted `/home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.ch7.pdf` and checked the block around Theorem 7.5 and equation `(7.23)`. The source proof uses `A = RᵀR`, `κ₂(DAD) = κ₂(RD)^2`, and Theorem 7.5 to derive `κ₂(D*AD*) <= n min_{D∈D_n} κ₂(DAD)`. The new Lean theorem `corollary7_6_cholesky_scaled_cond_le_card_sInf_symmetric_scalings` matches this inequality in the repository's explicit inverse-Gram model with `sInf` over reciprocal two-sided scalings; the report continues to document that no attained-minimum/minimizer theorem is asserted.
- Source re-audit for Problem 7.10(a)-(b)/(d)-(e): the Lean theorems prove the lower-bound and canonical-attainment algebra under the explicit Perron-vector certificate used by the source hint, prove exact `sInf = ρ` and `IsLeast` wrappers for the positive reciprocal Bauer infinity-norm value set, the scaled-`κ∞` value set, and the one-norm scaled-`κ₁` transpose value set under those explicit certificates, prove that inverse-compatible two-sided scalings transport the inverse certificate and agree with repository `kappaInf`, prove the `B = |A|`, `C = |A⁻¹|` absolute-value scaled-`κ∞` instantiation, prove positive-entry product irreducibility for the absolute-value products, prove the `CB(Cx)` eigenvector algebra in part (c), prove the irreducible `Cx > 0` transfer in part (d), derive positive eigenvalue and strict vector positivity from supplied nonzero nonnegative eigenpairs plus irreducibility, and do the same for the one-norm branch while deriving the needed transpose-product irreducibility from the original source products `BC` and `CB`. The Lean theorems also export the same supplied certificate to the generic Split 1 maximum-modulus/norm-existence APIs, to Mathlib spectrum-modulus `sSup = ρ`, and to Mathlib Banach-algebra `spectralRadius = ENNReal.ofReal ρ`; they prove the fixed-scaling 2-norm interpolation theorem and package it as a conditional positive-scaling `sInf` upper bound. The full source row remains open for Perron-Frobenius eigenpair existence from irreducibility and proof that the compatible common Bauer scaling exists at the source spectral-radius value for part (e).
- Latest finite eigenvalue-radius source audit: the re-extracted Chapter 7 source states Theorem 7.8 using `ρ` as spectral radius and a positive Perron vector from irreducibility, and Problem 7.10(a) directs the proof through a positive right Perron vector `BCx = ρ(BC)x`. The Lean declarations now close the local certificate-to-finite-complex-eigenvalue-radius, local eigenvalue-modulus supremum, generic Split 1 maximum-modulus/norm-existence, Mathlib spectrum-modulus supremum, and Mathlib `spectralRadius` parts of that source proof under a supplied positive Perron-vector certificate: once `x > 0` and `BCx = ρx` are supplied, every complex eigenvalue certificate of the complexified nonnegative matrix has modulus at most `ρ`, the supplied real eigenvector gives attainment, `ρ` is proved to be both an `IsGreatest` value and the real `sSup` of the local and Mathlib spectrum-modulus sets, `spectralRadius ℂ (Matrix.toLin' ...) = ENNReal.ofReal ρ`, and integrated Split 1 supplies consistent norm values with `c ≤ ρ + δ`. This still does not prove Perron-Frobenius eigenpair existence from irreducibility.
- Current-branch API search evidence for the remaining Theorem 7.5 and Theorem 7.8 source blockers: searches over `LeanFpAnalysis`, `.lake/packages/mathlib/Mathlib`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found the integrated SVD declarations `exists_complexMatrixSVDUnitary_diagonal_eq`, `exists_complexMatrixSVDUnitary_diagonal_eq_with_entry_formula`, and `exists_isComplexMatrixSVD` in `Norms.lean`.  The former Moore-Penrose construction gap is now closed locally by the normal-equations declarations `theorem7_5_exists_rect_left_inverse_symmetric_range_of_matrix_rank_eq_width`, `theorem7_5_exists_rect_right_inverse_symmetric_domain_of_matrix_rank_eq_height`, `theorem7_5_exists_rect_penrose_equations_of_matrix_rank_eq_width`, and `theorem7_5_exists_rect_penrose_equations_of_matrix_rank_eq_height`, and the same constructed `A⁺` is connected to endpoint, `sInf`, and conditional source-`min` wrappers.  The literal printed row-`∞` scale audit is closed by `theorem7_5_literal_printed_row_inf_scale_counterexample`, so remaining Theorem 7.5 search evidence is only for actual non-endpoint minimizer-existence.  Searches for Perron-Frobenius and positive/nonnegative eigenvector existence found Mathlib's `Matrix.IsIrreducible` connectivity API, the Chapter 7 certificate-level Perron/Bauer wrappers, the local finite eigenvalue-radius wrappers, the generic maximum-modulus export, Mathlib spectrum-modulus wrappers, and Mathlib `spectralRadius` wrappers; no theorem was found deriving the required Perron eigenpair existence from irreducibility alone.
- Source re-audit for Problem 7.15: the source lower bound is `inf κ₂(D₁AD₂) ≥ ‖A ∘ A^{-T}‖₂` and its hint uses the Horn-Johnson inequality `‖A ∘ B‖₂ ≤ ‖A‖₂‖B‖₂`; the new Lean results close the reciprocal diagonal-scaling invariance of `A ∘ A^{-T}`, the transpose/operator-2 certificate side condition for the inverse-scaled partner, the Horn-Johnson operator-2 Hadamard certificate, the scaled inverse-partner consequence, the exact `complexMatrixOp2` positive-scaling `sInf` lower-bound statement, the conditional attainability certificate, and Appendix A.7.15's statement that equality is trivial for diagonal `A`, modeled as the nonsingular diagonal theorem `problem7_15_diagonal_twoSidedScaledOp2Kappa_sInf_eq_one` plus `problem7_15_diagonal_twoSidedScaledOp2Kappa_isLeast_one`.
- Current-branch search evidence for Problem 7.15: searches for Hadamard/Schur operator-norm declarations found Mathlib's algebraic `Matrix.hadamard` API in `Mathlib/LinearAlgebra/Matrix/Hadamard.lean`, Riesz-Thorin/complex-analysis Hadamard lemmas and real Hadamard-matrix norm lemmas in `Norms.lean`, and unrelated signed-Hadamard/SRHT or Schur-complement material, but no repository or Mathlib theorem matching the needed operator-2 Schur-product inequality was available before this pass. This pass adds the local shared proof `opNorm2Le_hadamard` and the exact op-2 `sInf` wrapper `problem7_15_twoSidedScaledOp2Kappa_sInf_ge_hadamard_op2`; no unresolved previous-split dependency remains for Problem 7.15.
- Placeholder scan results: `rg -n "^\s*(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Analysis/Norms.lean LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean chapter_splitting/reports/chapter7_formalization_report.md chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md` found no leading placeholder declarations; `rg -n "\b(sorry|admit|axiom|unsafe|opaque)\b" LeanFpAnalysis/FP/Analysis/Norms.lean LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean docs/LIBRARY_LOOKUP.md examples/LibraryLookup.lean` found only ordinary prose in an existing `Norms.lean` doc comment, not a declaration or placeholder; the same stale-wait scan over implementation/lookup files found no matches, while the report itself only contains historical command strings mentioning `WAIT-PREVIOUS-SPLIT`/`WAIT-SPLIT1`. A repo-diff placeholder scan over the touched implementation/lookup/report files found matches only in report command strings and standard axiom-summary text, not in Lean implementation or lookup code.
- Additional current-pass implementation/lookup scan results: focused scans over `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no leading `sorry`, `admit`, `axiom`, `unsafe`, or `opaque`, no `False.elim`, no `by sorry`, no `TODO`/`FIXME`/stale-wait/`placeholder` labels, no line-anchored conflict markers, and no trailing whitespace. Report-inclusive broad scans matched only historical scan prose and standard axiom-summary text.
- Additional Theorem 7.5 `sInf` wrapper placeholder/stale scan results: focused scans over `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, `examples/LibraryLookup.lean`, `chapter_splitting/reports/chapter7_formalization_report.md`, and `chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md` found no leading `sorry`, `admit`, `axiom`, `unsafe`, or `opaque`, no implementation/lookup `TODO`/`FIXME`/`WAIT-PREVIOUS-SPLIT`/`WAIT-SPLIT1`/`WAIT-SPLIT`/`placeholder` labels, and no conflict markers.
- Additional Theorem 7.5 endpoint least-element placeholder/stale scan results: focused scans over `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no leading `sorry`, `admit`, `axiom`, `unsafe`, or `opaque`, no `False.elim`, no direct `Classical.choice`, and no `TODO`/`FIXME`/stale-wait/placeholder labels. Report stale-label scans only matched historical command strings that describe earlier clean scans. Anchored trailing-whitespace/conflict-marker scans over touched repo files and FLARE dev logs found no matches.
- Additional finite-real `p` value-set placeholder/stale scan results: focused scans over `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no leading `sorry`, `admit`, `axiom`, `unsafe`, or `opaque`, no `False.elim`, no direct `Classical.choice`, and no `TODO`/`FIXME`/stale-wait/placeholder labels. Anchored trailing-whitespace/conflict-marker scans over touched repo files and FLARE dev logs found no matches.
- `#print axioms` results for final-facing new theorems: `ch7_condSkeel_rowScale_eq`, `problem7_3_rowEquilibrated_scaling_condition_eq`, `problem7_3_rowEquilibrated_lower_bound`, `eq_7_16_rowEquilibrated_bounds`, `eq_7_15_positive_rowScaling_sInf_eq_condSkeel_of_right_inverse`, `eq_7_20_column_norm_le_of_rectOpNorm2Le`, `eq_7_20_rectOpNorm2Le_of_column_bound`, `eq_7_21_rectOpNorm2Le_column_equilibrated`, `eq_7_21_oneNormRect_column_equilibrated`, `eq_7_22_oneNormRect_inverseSide_bound`, `theorem7_5_p1_column_equilibration_le_right_scaling`, `eq_7_19_infNormRect_row_equilibrated`, `eq_7_19_infNormRect_inverseSide_bound`, `theorem7_5_pinf_row_equilibration_le_left_scaling`, `theorem7_7_frobenius_right_scaling_lower_bound`, `theorem7_7_stewart_sun_frobenius_scaling`, `theorem7_7_stewart_sun_frobenius_scaling_of_left_inverse`, `ch7TwoSidedScale_isLeftInverse`, `ch7TwoSidedScale_isRightInverse`, `ch7TwoSidedScale_isInverse`, `ch7TwoSidedScaledInfKappa_eq_kappaInf_of_inverse`, `ch7_matrix_isPrimitive_of_pos_entries`, `ch7_matrix_isIrreducible_of_pos_entries`, `ch7_matMul_pos_of_pos`, `ch7_bauer_positive_products_irreducible`, `problem7_10b_positive_abs_entries_products_irreducible`, `problem7_6a_rowwise_data_condition_bounds`, `problem7_6b_columnwise_data_condition_bounds`, `problem7_9_linearized_componentwise_functional_formula`, `problem7_9_linearized_normwise_functional_formula`, `problem7_9_componentwise_linearized_radiusSup_tendsto_formula`, `problem7_9_normwise_linearized_radiusSup_tendsto_formula`, `problem7_9_exact_componentwise_relative_change_le_linearized_plus_quadratic`, `problem7_9_exact_componentwise_relative_change_ge_linearized_minus_quadratic`, `ch7Problem79ComponentwiseExactRadiusSet_value_le`, `exists_ch7Problem79ComponentwiseExactRadiusSet_lower_witness`, `problem7_9_componentwise_exact_radiusSup_tendsto_linearized`, `problem7_9_componentwise_exact_condition_of_positive_radii`, `ch7Problem79_normwise_deltaA_componentwise_bound`, `ch7Problem79_normwise_deltaB_componentwise_bound`, `problem7_9_exact_normwise_relative_change_le_linearized_plus_quadratic`, `problem7_9_exact_normwise_relative_change_ge_linearized_minus_quadratic`, `ch7Problem79NormwiseExactRadiusSet_value_le`, `exists_ch7Problem79NormwiseExactRadiusSet_lower_witness`, `problem7_9_normwise_exact_radiusSup_tendsto_linearized`, `problem7_9_normwise_exact_condition_of_positive_radii`, `problem7_11_linearized_inverse_componentwise_formula`, `problem7_11_exact_inverse_firstOrder_remainder_identity`, `problem7_11_exact_inverse_relative_change_max_div_tendsto_linearized_of_componentwise_tendsto_zero`, `Ch7InverseComponentwiseRadiusSet`, `ch7InverseComponentwiseRadiusSup`, `IsCh7InverseComponentwiseRadiusLimitValue`, `IsCh7InverseComponentwiseCondValue`, `ch7Problem711LocalInverseInfNormBound`, `ch7Problem711LocalInverseInfNormBound_nonneg`, `ch7InverseComponentwiseRadiusRemainderBound`, `ch7InverseComponentwiseRadiusRemainderBound_nonneg`, `ch7_inverse_componentwise_radius_candidate_right_inverse_of_small`, `ch7_inverse_componentwise_radius_candidate_infNorm_bound_of_small`, `ch7InverseComponentwiseRadiusSet_value_le`, `exists_ch7InverseComponentwiseRadiusSet_lower_witness`, `problem7_11_inverse_componentwise_radiusSup_tendsto_linearized`, `problem7_11_inverse_componentwise_condition_of_positive_radii`, and `eq_7_26_relative_distance_to_singularity_eq_inv_condition_number` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Problem 7.15 `#print axioms` results for `ch7_matTranspose_twoSidedScale`, `ch7HadamardProduct_twoSidedScale_transpose_inverse_eq`, `problem7_15_twoSidedScale_hadamard_transpose_inverse_invariant`, `opNorm2Le_transpose`, `problem7_15_transpose_inverse_partner_opNorm2Le`, `frobNormRect_diagMatrix`, `vecNorm2_diagonal_le_frobNormRect`, `matMulVec_hadamard_eq_diag_rectMatMul_diag_transpose`, `opNorm2Le_hadamard`, `problem7_15_hornJohnson_hadamard_opNorm2Le`, `problem7_15_scaled_inverse_hadamard_opNorm2Le`, `complexMatrixOp2_realRectToCMatrix_le_of_opNorm2Le`, `opNorm2Le_complexMatrixOp2_realRectToCMatrix`, `ch7TwoSidedScaledOp2KappaSet_nonempty`, `problem7_15_hadamard_op2_le_twoSidedScaledOp2Kappa_mem`, `problem7_15_twoSidedScaledOp2Kappa_sInf_ge_hadamard_op2`, `problem7_15_twoSidedScaledOp2Kappa_sInf_ge_hadamard_op2_of_inverse`, `problem7_15_twoSidedScaledOp2Kappa_sInf_eq_hadamard_op2_of_mem`, `problem7_15_twoSidedScaledOp2Kappa_sInf_eq_hadamard_op2_of_attaining_scaling`, `problem7_15_complexMatrixOp2_realRectToCMatrix_orthogonal_eq_one`, `problem7_15_diagonal_hadamard_op2_eq_one`, `problem7_15_diagonal_attaining_scaling_eq_hadamard_op2`, `problem7_15_diagonal_twoSidedScaledOp2Kappa_sInf_eq_one`, and `problem7_15_diagonal_twoSidedScaledOp2Kappa_isLeast_one` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Problem 7.10(e) `#print axioms` results for `ch7TwoSidedScaledOneCond_eq_transpose_infCond`, `problem7_10e_scaled_oneCond_ge_perron_of_transpose_positive_eigenvector`, `problem7_10e_canonical_scaled_oneCond_eq_perron_of_transpose_positive_eigenvector`, `problem7_10e_positive_entries_canonical_scaled_oneCond_eq_perron_of_transpose`, `ch7TwoSidedScaledOneKappa_eq_abs_scaledOneCond`, `problem7_10e_scaled_oneKappa_ge_perron_of_abs_inverse_transpose_positive_eigenvector`, `problem7_10e_canonical_scaled_oneKappa_eq_perron_of_abs_inverse_transpose_positive_eigenvector`, and `problem7_10e_positive_abs_entries_canonical_scaled_oneKappa_eq_perron_of_transpose` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 `p = 2` `#print axioms` results for `ch7_vecNorm2_mul_le_of_abs_le`, `ch7RectLeftScale_rectOpNorm2Le_of_abs_le`, `ch7Op2RightScaledCond`, `eq_7_22_op2_inverseSide_bound`, and `theorem7_5_p2_column_equilibration_le_sqrt_card_right_scaling` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 explicit-`Aplus` `sInf` wrapper `#print axioms` results for `ch7OneNormRightScaledCondSet`, `theorem7_5_p1_column_equilibration_sInf_eq_right_scalings`, `ch7Op2RightScaledCondSet`, `ch7Op2RightScaledCondSet_nonempty`, `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings`, `ch7InfNormLeftScaledCondSet`, and `theorem7_5_pinf_row_equilibration_sInf_eq_left_scalings` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 endpoint least-element `#print axioms` results for `theorem7_5_p1_column_equilibration_isLeast_right_scalings` and `theorem7_5_pinf_row_equilibration_isLeast_left_scalings` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 `p = 2` row-scaling `#print axioms` results for `ch7RectRightScale_rectOpNorm2Le_of_abs_le`, `eq_7_19_rectOpNorm2Le_row_equilibrated`, `eq_7_19_op2_inverseSide_bound`, `theorem7_5_p2_row_equilibration_le_sqrt_card_left_scaling`, and `theorem7_5_p2_row_equilibration_le_sqrt_card_sInf_left_scalings` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 finite-real `p` equations `(7.20)`-`(7.21)` `#print axioms` results for `ch7RectColumnLpNormOfReal_nonneg`, `eq_7_20_column_lpNorm_le_matrixLpNormOfReal`, `ch7_complexVecLpNorm_realRect_matVec_le_sum_column_lpNorm`, `eq_7_20_matrixLpNormOfReal_le_card_rpow_mul_column_bound`, `ch7RectColumnLpNormOfReal_rightScale`, `ch7RectColumnLpNormOfReal_rightScale_equilibrating`, and `eq_7_21_matrixLpNormOfReal_column_equilibrated` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 finite-real `p` value-set `#print axioms` results for `ch7LpRightScaledCondSetOfReal_bddBelow`, `ch7LpRightScaledCondSetOfReal_sInf_nonneg`, `ch7LpLeftScaledCondSetOfReal_bddBelow`, and `ch7LpLeftScaledCondSetOfReal_sInf_nonneg` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 finite-real conjugate-row `(7.19)` `#print axioms` results for `eq_7_19_matrixLpNormOfReal_dual_row_equilibrated`, `eq_7_19_matrixLpNormOfReal_dual_row_inverseSide_bound`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_left_scaling`, and `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 one-sided-inverse side-condition `#print axioms` results for `ch7RectColumnLpNormOfReal_pos_of_rect_left_inverse`, `ch7RectColumnNorm2_pos_of_rect_left_inverse`, `ch7RectColumnNorm1_pos_of_rect_left_inverse`, `ch7RectRowDualLpNormOfReal_pos_of_rect_right_inverse`, `ch7RectRowNorm2_pos_of_rect_right_inverse`, `ch7RectRowNorm1_pos_of_rect_right_inverse`, `theorem7_5_lp_column_equilibration_le_card_rpow_sInf_right_scalings_of_rect_left_inverse`, `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings_of_rect_left_inverse`, `theorem7_5_p1_column_equilibration_isLeast_right_scalings_of_rect_left_inverse`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings_of_rect_right_inverse`, `theorem7_5_p2_row_equilibration_le_sqrt_card_sInf_left_scalings_of_rect_right_inverse`, and `theorem7_5_pinf_row_equilibration_isLeast_left_scalings_of_rect_right_inverse` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 Matrix-rank source side-condition `#print axioms` results for `ch7_rectMatMulVec_injective_of_matrix_rank_eq_width`, `ch7_rectMatMulVec_surjective_of_matrix_rank_eq_height`, `theorem7_5_p1_column_equilibration_exists_left_inverse_of_matrix_rank_eq_width`, `theorem7_5_p2_column_equilibration_exists_left_inverse_of_matrix_rank_eq_width`, `theorem7_5_lp_column_equilibration_exists_left_inverse_of_matrix_rank_eq_width`, `theorem7_5_lp_dual_row_equilibration_exists_right_inverse_of_matrix_rank_eq_height`, `theorem7_5_p2_row_equilibration_exists_right_inverse_of_matrix_rank_eq_height`, and `theorem7_5_pinf_row_equilibration_exists_right_inverse_of_matrix_rank_eq_height` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 conditional source-`min` adapter verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, redirected `lake env lean --tstack=65536 examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for representative new source-`min` adapters, focused implementation/lookup placeholder scans, conflict-marker/trailing-whitespace scans, `git diff --check` over touched repository files, `pdftotext -layout` source re-audit of Theorem 7.5, and `timeout 600s lake build` all passed. The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings. The first redirected lookup run before the targeted build failed only because the fresh Chapter 7 `.olean` did not yet expose the new declarations; after rebuilding the target, lookup passed.
- Additional Theorem 7.5 conditional source-`min` adapter `#print axioms` results for `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings`, `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_rect_left_inverse`, and `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings_of_rect_right_inverse` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 projection-dependency and projection-geometry verification: `lake env lean LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean`, `lake build LeanFpAnalysis.FP.Analysis.MatrixAlgebra`, `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean --tstack=65536 examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for the new reusable/source-facing projection declarations, focused implementation/lookup placeholder scans, anchored conflict-marker and trailing-whitespace scans, `git diff --check` over touched repository files, `pdftotext -layout` source re-audit of Theorem 7.5, and `timeout 600s lake build` all passed.  The targeted MatrixAlgebra build completed with `2412` jobs, the targeted Chapter 7 build completed with `3020` jobs, and the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.  The source re-audit confirmed this work closes algebraic/symmetric-idempotent projection dependencies, range/domain fixing, residual orthogonality, and squared-/ordinary-norm best-approximation dependencies, while Moore-Penrose existence, Penrose symmetry, printed row-scale reconciliation, and general/non-endpoint minimizer existence remain open.
- Additional Theorem 7.5 projection-geometry `#print axioms` results for `finiteMatVec_projection_residual_eq_zero_of_idempotent`, `finiteVecInnerProduct_projection_residual_range_eq_zero`, `finiteVecNorm2Sq_add_of_inner_eq_zero`, `finiteVecNorm2Sq_projection_residual_le_residual_to_range_of_symmetric_idempotent`, `finiteVecNorm2_projection_residual_le_residual_to_range_of_symmetric_idempotent`, `rectMatMulVec_rangeProjection_apply_range_of_left_inverse`, `rectMatMulVec_domainProjection_apply_range_of_right_inverse`, `rectMatMulVec_rangeProjection_residual_orthogonal_range_of_symmetric_left_inverse`, `rectMatMulVec_domainProjection_residual_orthogonal_range_of_symmetric_right_inverse`, `rectMatMulVec_rangeProjection_residual_normSq_le_range_residual_of_symmetric_left_inverse`, `rectMatMulVec_domainProjection_residual_normSq_le_range_residual_of_symmetric_right_inverse`, `rectMatMulVec_rangeProjection_residual_norm_le_range_residual_of_symmetric_left_inverse`, `rectMatMulVec_domainProjection_residual_norm_le_range_residual_of_symmetric_right_inverse`, `theorem7_5_rect_left_inverse_range_projection_fixes_range`, `theorem7_5_rect_right_inverse_domain_projection_fixes_range`, `theorem7_5_rect_left_inverse_symmetric_range_projection_residual_orthogonal_range`, `theorem7_5_rect_right_inverse_symmetric_domain_projection_residual_orthogonal_range`, `theorem7_5_rect_left_inverse_symmetric_range_projection_residual_normSq_le_range_residual`, `theorem7_5_rect_right_inverse_symmetric_domain_projection_residual_normSq_le_range_residual`, `theorem7_5_rect_left_inverse_symmetric_range_projection_residual_norm_le_range_residual`, and `theorem7_5_rect_right_inverse_symmetric_domain_projection_residual_norm_le_range_residual` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 projection-dependency placeholder scan results: focused implementation/lookup scans over `LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean`, `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, stale wait labels, `TODO`, `FIXME`, `placeholder`, or `by sorry` matches.  Focused scans still show pre-existing `False.elim` occurrences in `MatrixAlgebra.lean` at lines 2085, 5460, 6951, and 6981, and a broad added-line diff scan matched report prose plus two earlier Problem 7.15 Hadamard-support `False.elim` lines, not the new projection declarations.
- Additional Theorem 7.5 projection-minimizer wrapper verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean --tstack=65536 examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for the four new set-level residual-minimizer wrappers, focused implementation/lookup placeholder scans, stale-label scans, anchored conflict-marker scans, trailing-whitespace scans, `git diff --check`, and `timeout 600s lake build` all passed.  The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.  The Theorem 7.5 source re-audit in this pass confirmed the full source still requires Moore-Penrose construction/Penrose symmetry and source `min` packaging beyond these supplied-symmetric-projection minimizer wrappers.
- Additional Theorem 7.5 projection-minimizer `#print axioms` results for `theorem7_5_rect_left_inverse_symmetric_range_projection_residual_normSq_isLeast`, `theorem7_5_rect_right_inverse_symmetric_domain_projection_residual_normSq_isLeast`, `theorem7_5_rect_left_inverse_symmetric_range_projection_residual_norm_isLeast`, and `theorem7_5_rect_right_inverse_symmetric_domain_projection_residual_norm_isLeast` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 Penrose rank-min continuation verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake env lean --tstack=65536 examples/LibraryLookup.lean`, `lake env lean /tmp/ch7_penrose_rank_min_axioms.lean`, focused implementation/lookup placeholder scans, anchored conflict-marker/trailing-whitespace scans over the touched implementation, lookup, report, and FLARE log files, `git diff --check`, `pdftotext -layout` source re-audit of the Theorem 7.5 passage, and `timeout 600s lake build` all passed.  The full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.  The source re-audit confirms that Theorem 7.5 states `κ_p(A) = ‖A‖_p ‖A⁺‖_p` with `A⁺` as the pseudoinverse, the printed `rank(A)=n/m` hypotheses, and the source `min` inequalities `(7.18)` and `(7.19)`.  The new wrappers close only the Penrose1-plus-Matrix-rank route into existing endpoint least-element, non-endpoint `sInf`, and conditional `IsLeast` source-`min` surfaces; they do not construct the Moore-Penrose inverse, prove first-Penrose/projection-symmetry witnesses for that construction, reconcile the printed row-scale notation, or prove non-endpoint minimizer existence.
- Additional Theorem 7.5 Penrose rank-min `#print axioms` results for `theorem7_5_p1_column_equilibration_isLeast_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_p2_column_equilibration_le_sqrt_card_sInf_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_lp_column_equilibration_le_card_rpow_sInf_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings_of_penrose1_matrix_rank_eq_width`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_sInf_left_scalings_of_penrose1_matrix_rank_eq_height`, `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings_of_penrose1_matrix_rank_eq_height`, `theorem7_5_p2_row_equilibration_le_sqrt_card_sInf_left_scalings_of_penrose1_matrix_rank_eq_height`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_penrose1_matrix_rank_eq_height`, and `theorem7_5_pinf_row_equilibration_isLeast_left_scalings_of_penrose1_matrix_rank_eq_height` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 Penrose rank-min placeholder and API hygiene: a repository Lean scan `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis examples --glob "*.lean"` found only ordinary prose in the pre-existing `Norms.lean` perturbation doc comment, not a Lean declaration or placeholder.  Focused scans over `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no leading `sorry`, `admit`, `axiom`, `unsafe`, or `opaque`, no `False.elim`, no `by sorry`, no `TODO`/`FIXME`/stale-wait/`placeholder` labels, and no conflict markers or trailing whitespace.  Inspection of the ten new signatures found no orphan typeclass hypotheses; the continuation adds theorem wrappers only, not vacuous definitions.
- Additional Theorem 7.5 Moore-Penrose construction verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after adding the normal-equations full-column and transpose full-row constructions plus the same-`Aplus` scaling wrappers.  The newly closed declarations are `theorem7_5_exists_rect_left_inverse_symmetric_range_of_rectMatMulVec_injective`, `theorem7_5_exists_rect_left_inverse_symmetric_range_of_matrix_rank_eq_width`, `theorem7_5_exists_rect_right_inverse_symmetric_domain_of_matrix_rank_eq_height`, `theorem7_5_exists_rect_penrose_equations_of_rectMatMulVec_injective`, `theorem7_5_exists_rect_penrose_equations_of_matrix_rank_eq_width`, `theorem7_5_exists_rect_penrose_equations_of_matrix_rank_eq_height`, `theorem7_5_p1_column_equilibration_exists_penrose_of_matrix_rank_eq_width`, `theorem7_5_p2_column_equilibration_exists_penrose_of_matrix_rank_eq_width`, `theorem7_5_lp_column_equilibration_exists_penrose_of_matrix_rank_eq_width`, `theorem7_5_lp_dual_row_equilibration_exists_penrose_of_matrix_rank_eq_height`, `theorem7_5_p2_row_equilibration_exists_penrose_of_matrix_rank_eq_height`, and `theorem7_5_pinf_row_equilibration_exists_penrose_of_matrix_rank_eq_height`.  The construction uses Mathlib `Matrix.PosDef.conjTranspose_mul_self`, `Matrix.nonsing_inv_mul`, Hermitian inverse/congruence, and `Matrix.rank_transpose`; no previous-split theorem is missing or duplicated.  The source re-audit remains as above: Theorem 7.5 still has open current-Split-2 work for printed row-scale notation reconciliation and non-endpoint minimizer existence, while its printed-rank Moore-Penrose construction/Penrose-equation witness subrow is now closed.
- Additional Theorem 7.5 Moore-Penrose construction final verification: `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3020` jobs; `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after adding lookup checks; `timeout 600s lake build` passed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.  Focused scans over the touched implementation/lookup surfaces found no leading `sorry`, `admit`, `axiom`, `unsafe`, or `opaque`, no `TODO`/`FIXME`/stale-wait/`placeholder`/`by sorry`/`False.elim`, no conflict markers, and no trailing whitespace.  The broad Lean placeholder scan over `LeanFpAnalysis` and `examples` found only ordinary prose in the pre-existing `Norms.lean` perturbation doc comment.  `#print axioms` for the eleven new Moore-Penrose construction/same-`Aplus` scaling declarations uses only `propext`, `Classical.choice`, and `Quot.sound`.  The post-implementation source re-audit re-read Theorem 7.5 from the Chapter 7 PDF and confirmed the new declarations match the printed `rank(A)=n/m`, pseudoinverse, Penrose-equation, and endpoint/`sInf` scaling scope documented above.
- Additional Theorem 7.5 same-`A⁺` conditional source-`min` verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed before report updates; `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3020` jobs; `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after rebuilding the Chapter 7 target; `lake env lean --stdin` with `#print axioms` for the four new same-`A⁺` conditional source-`min` wrappers passed; `pdftotext -layout /home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.ch7.pdf` source re-audit confirmed that Theorem 7.5 defines `κ_p(A)` using the pseudoinverse, prints source `min` inequalities `(7.18)` and `(7.19)`, and derives `(7.19)` by the transpose/Hölder-conjugate route; focused implementation/lookup placeholder scans, anchored conflict-marker scans, trailing-whitespace scans, and `git diff --check` passed; `timeout 600s lake build` passed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.  The first lookup run before the targeted build failed only because the fresh Chapter 7 `.olean` did not yet expose the new declarations; after rebuilding, lookup passed.
- Additional Theorem 7.5 same-`A⁺` conditional source-`min` `#print axioms` results for `theorem7_5_p2_column_equilibration_exists_penrose_min_imp_of_matrix_rank_eq_width`, `theorem7_5_lp_column_equilibration_exists_penrose_min_imp_of_matrix_rank_eq_width`, `theorem7_5_lp_dual_row_equilibration_exists_penrose_min_imp_of_matrix_rank_eq_height`, and `theorem7_5_p2_row_equilibration_exists_penrose_min_imp_of_matrix_rank_eq_height` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 literal row-`∞` source-audit verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after adding the counterexample; `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3020` jobs; `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after adding lookup checks; `lake env lean --stdin` with `#print axioms` for the counterexample theorem and its concrete matrix definitions passed; `pdftotext -layout /home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.ch7.pdf` source re-audit reconfirmed that the PDF prints `D_R := diag(‖A(i,:)‖_p)^{-1}` but derives `(7.19)` from the transpose/Hölder-conjugate identity; focused implementation/lookup placeholder scans, anchored conflict-marker scans, trailing-whitespace scans, and `git diff --check` passed; `timeout 600s lake build` passed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.  The broad Lean placeholder scan over `LeanFpAnalysis` and `examples` found only ordinary prose in the pre-existing `Norms.lean` perturbation doc comment phrase “admit an actual”.
- Additional Theorem 7.5 literal row-`∞` source-audit `#print axioms` results: `theorem7_5_literal_printed_row_inf_scale_counterexample`, `theorem7_5_literalRowInfCounterexampleA`, and `theorem7_5_literalRowInfCounterexampleAplus` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 literal row-`∞` source-audit conclusion: the older report wording that the printed row-scale reconciliation remained open is superseded for the literal `p = ∞` reading.  The new theorem proves that reciprocal maximum-entry row scaling need not minimize the infinity-norm condition product (`40/9` for the literal identity scale versus `31/9` for a reciprocal alternative).  The formalized row theorem therefore remains the conjugate-row/row-`1` model from the source proof, and the remaining Theorem 7.5 target is actual minimizer existence for the general/non-endpoint source `min` statements.
- Additional Theorem 7.5 `p = 2` global-rescaling normalization inventory update: `(7.18)` now includes proved invariance of the explicit-`Aplus` right-scaling condition product under `D ↦ tD`, `D⁻¹ ↦ t⁻¹D⁻¹`, by `ch7Op2RightScaledCond_global_scale`, plus the equivalent value-set witness `ch7Op2RightScaledCond_mem_set_global_scale`.  `(7.19)` now includes the left-scaling analogue `ch7Op2LeftScaledCond_global_scale` and `ch7Op2LeftScaledCond_mem_set_global_scale`.  These are genuine mathematical dependencies for a compact-slice minimizer-existence proof; they do not assert or close the remaining source `min` attainment theorem.
- Additional Theorem 7.5 `p = 2` global-rescaling normalization verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean --tstack=65536 examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for the four new global-scale declarations, focused implementation/lookup placeholder scans, broad Lean placeholder scan, conflict-marker and trailing-whitespace scans over touched implementation/report/log files, `git diff --check`, `pdftotext -layout` source re-audit of the Theorem 7.5 passage, and `timeout 600s lake build` all passed.  The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.  The source re-audit confirmed that `(7.18)` and `(7.19)` are source `min` statements, so the new global-scale lemmas are recorded as minimizer-existence dependencies rather than full source-row closure.
- Additional Theorem 7.5 `p = 2` global-rescaling normalization `#print axioms` results: `ch7Op2RightScaledCond_global_scale`, `ch7Op2RightScaledCond_mem_set_global_scale`, `ch7Op2LeftScaledCond_global_scale`, and `ch7Op2LeftScaledCond_mem_set_global_scale` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 `p = 2` global-rescaling placeholder and API hygiene: the broad Lean scan found only the pre-existing prose phrase "admit an actual" in `Norms.lean`; the focused implementation/lookup scan matched only ordinary lookup prose containing the word "axioms" and no Lean placeholders.  The new declarations introduce no orphan typeclass hypotheses, no theorem-equivalent assumptions, and no vacuous definitions.
- Additional Theorem 7.5 `p = 2` absolute-sum-one normalization inventory update: `(7.18)` now includes `ch7_sum_abs_pos_of_reciprocal` and `ch7Op2RightScaledCond_sum_abs_normalized_witness`, proving that any reciprocal right diagonal witness on a nonempty index type can be globally rescaled to `∑ |d_j| = 1` while preserving the reciprocal relation and explicit Euclidean condition product.  `(7.19)` now includes `ch7Op2LeftScaledCond_sum_abs_normalized_witness`, the corresponding left-scaling statement.  These are genuine compact-slice dependencies for the remaining minimizer-existence proof; they do not assert the source `min` is attained.
- Additional Theorem 7.5 `p = 2` absolute-sum-one normalization verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean --tstack=65536 examples/LibraryLookup.lean`, `lake env lean --stdin` with `#print axioms` for the three new normalized-slice declarations, focused implementation/lookup placeholder scans, broad Lean placeholder scan, anchored conflict-marker scans, trailing-whitespace scans, `git diff --check`, `pdftotext -layout` source re-audit of Theorem 7.5, and `timeout 600s lake build` all passed.  The targeted Chapter 7 build completed with `3020` jobs; the full build completed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.  One parallel lookup run before the target rebuild saw stale `.olean` state and failed; after rebuilding the target, lookup passed.
- Additional Theorem 7.5 `p = 2` absolute-sum-one normalization `#print axioms` results: `ch7_sum_abs_pos_of_reciprocal`, `ch7Op2RightScaledCond_sum_abs_normalized_witness`, and `ch7Op2LeftScaledCond_sum_abs_normalized_witness` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 `p = 2` absolute-sum-one placeholder and API hygiene: the broad Lean scan found only the pre-existing prose phrase "admit an actual" in `Norms.lean`; the focused implementation/lookup scan found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `False.elim`, stale wait labels, `TODO`, `FIXME`, `placeholder`, or `by sorry` matches.  The new declarations introduce no orphan typeclass hypotheses, no theorem-equivalent assumptions, and no vacuous definitions.
- Additional Theorem 7.5 `p = 2` normalized value-set equality inventory update: `(7.18)` now includes `ch7Op2RightScaledCondNormalizedSet` and `ch7Op2RightScaledCondSet_eq_sum_abs_normalized`, proving that the unrestricted explicit right reciprocal p=2 value set is exactly the `∑ |d_j| = 1` normalized slice when `0 < n`.  `(7.19)` now includes `ch7Op2LeftScaledCondNormalizedSet` and `ch7Op2LeftScaledCondSet_eq_sum_abs_normalized`, the analogous left-scaling result when `0 < m`.  This closes the set-level compact-slice reduction for the p=2 value-set minimizer path; actual least-value attainment remains open.
- Additional Theorem 7.5 `p = 2` normalized value-set equality verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean --tstack=65536 examples/LibraryLookup.lean`, and `lake env lean --stdin` with `#print axioms` for the four normalized value-set declarations passed before this report append.  The targeted Chapter 7 build completed with `3020` jobs and lookup passed against the rebuilt module.
- Additional Theorem 7.5 `p = 2` normalized value-set equality `#print axioms` results: `ch7Op2RightScaledCondNormalizedSet`, `ch7Op2RightScaledCondSet_eq_sum_abs_normalized`, `ch7Op2LeftScaledCondNormalizedSet`, and `ch7Op2LeftScaledCondSet_eq_sum_abs_normalized` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 `p = 2` normalized value-set equality final hygiene: broad Lean placeholder scan found only the pre-existing prose phrase "admit an actual" in `Norms.lean`; focused implementation/lookup scans found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, stale wait labels, `TODO`, `FIXME`, `placeholder`, `False.elim`, or `by sorry` matches; anchored conflict-marker scans, trailing-whitespace scans, `git diff --check`, and Theorem 7.5 `pdftotext` source re-audit passed.  `timeout 600s lake build` passed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.
- Additional Theorem 7.5 `p = 2` normalized least-certificate transfer inventory update: `(7.18)` now includes `ch7Op2RightScaledCondSet_isLeast_iff_sum_abs_normalized`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_normalized`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_rect_left_inverse_of_normalized`, and `theorem7_5_p2_column_equilibration_exists_penrose_min_normalized_imp_of_matrix_rank_eq_width`.  `(7.19)` now includes `ch7Op2LeftScaledCondSet_isLeast_iff_sum_abs_normalized`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_normalized`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_rect_right_inverse_of_normalized`, and `theorem7_5_p2_row_equilibration_exists_penrose_min_normalized_imp_of_matrix_rank_eq_height`.  These declarations transfer normalized-slice `IsLeast` certificates into the existing source-`min` wrappers and into the same normal-equations Moore-Penrose candidate used by the printed-rank wrappers; they do not prove normalized-slice attainment.
- Additional Theorem 7.5 `p = 2` normalized least-certificate transfer verification: `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed; `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3020` jobs; `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after the targeted rebuild; `lake env lean --stdin` with `#print axioms` for the eight new normalized-transfer declarations passed; and `timeout 600s lake build` passed with `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings.  The first lookup attempt run in parallel before the target rebuild saw stale `.olean` state; the rerun after rebuilding passed.
- Additional Theorem 7.5 `p = 2` normalized least-certificate transfer `#print axioms` results: `ch7Op2RightScaledCondSet_isLeast_iff_sum_abs_normalized`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_normalized`, `theorem7_5_p2_column_equilibration_le_sqrt_card_min_right_scalings_of_rect_left_inverse_of_normalized`, `ch7Op2LeftScaledCondSet_isLeast_iff_sum_abs_normalized`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_normalized`, `theorem7_5_p2_row_equilibration_le_sqrt_card_min_left_scalings_of_rect_right_inverse_of_normalized`, `theorem7_5_p2_column_equilibration_exists_penrose_min_normalized_imp_of_matrix_rank_eq_width`, and `theorem7_5_p2_row_equilibration_exists_penrose_min_normalized_imp_of_matrix_rank_eq_height` use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 `p = 2` normalized least-certificate transfer hygiene: broad Lean placeholder scan over `LeanFpAnalysis` and `examples` found only the pre-existing prose phrase "admit an actual" in `Norms.lean`; focused implementation/lookup scans found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `False.elim`, stale wait labels, `TODO`, `FIXME`, `placeholder`, or `by sorry` matches; temporary axiom/probe-file scan found no files; anchored conflict-marker/trailing-whitespace scans over the touched implementation, lookup, report, and FLARE log files found no matches; and `git diff --check` passed.  The new declarations introduce no orphan typeclass hypotheses, no theorem-equivalent assumptions, and no vacuous definitions.
- `git diff --check` passed for `LeanFpAnalysis/FP/Analysis/Norms.lean`, `LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean`, `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, `examples/LibraryLookup.lean`, `chapter_splitting/reports/chapter7_formalization_report.md`, and `chapter_splitting/reports/split2_chapters7_12_unifying_pass_report.md`.
- Direct trailing-whitespace and conflict-marker scans passed for `/home/mymel/flare-bundle/dev-logs/CURRENT.md`, `/home/mymel/flare-bundle/dev-logs/INDEX.md`, `/home/mymel/flare-bundle/dev-logs/2026-06-25-chapter7-bauer-scaling-core.md`, `/home/mymel/flare-bundle/dev-logs/2026-06-25-chapter7-problem7-15-hadamard-scaling.md`, `/home/mymel/flare-bundle/dev-logs/2026-06-25-chapter7-theorem7-5-p2-row-scaling.md`, `/home/mymel/flare-bundle/dev-logs/2026-06-25-chapter7-theorem7-5-min-adapters.md`, `/home/mymel/flare-bundle/dev-logs/2026-06-25-chapter7-theorem7-5-projection-dependency.md`, and `/home/mymel/flare-bundle/dev-logs/2026-06-25-chapter7-theorem7-5-penrose-rank-min.md`; that directory is not a git repository, so `git diff --check` is not applicable there.
- No orphan classes are used as hypotheses in the new declarations added in this pass.
- No vacuous definitions were added in this pass.
- Chapter report path: `chapter_splitting/reports/chapter7_formalization_report.md`.
- Additional Theorem 7.5 `p = 2` reciprocal-domain/coercivity inventory update:
  `(7.18)` now includes the one-diagonal reciprocal normalized value-set model
  `ch7Op2RightScaledCondReciprocalNormalizedSet`, equality and `IsLeast`
  transfer from the existing normalized set, continuity of the reciprocal
  condition product by `continuousOn_ch7Op2RightScaledCond_reciprocal`, and
  boundary/coercivity estimates through
  `ch7Op2RightScaledCond_reciprocal_normalized_lower_exists` and
  `ch7Op2RightScaledCond_reciprocal_normalized_inv_abs_le_of_le`.  `(7.19)`
  has the corresponding left-scaling declarations
  `ch7Op2LeftScaledCondReciprocalNormalizedSet`,
  `continuousOn_ch7Op2LeftScaledCond_reciprocal`,
  `ch7Op2LeftScaledCond_reciprocal_normalized_lower_exists`, and
  `ch7Op2LeftScaledCond_reciprocal_normalized_inv_abs_le_of_le`.  The shared
  dependency `continuous_complexMatrixOp2` was added in `Norms.lean`.  These
  are genuine local analytic dependencies for minimizer existence; they do not
  yet prove a closed compact sublevel or extract the actual `IsLeast` value.
- Additional Theorem 7.5 reciprocal-domain/coercivity verification:
  `lake env lean LeanFpAnalysis/FP/Analysis/Norms.lean`, `lake build
  LeanFpAnalysis.FP.Analysis.Norms`, `lake env lean
  LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `lake build
  LeanFpAnalysis.FP.Analysis.HighamChapter7`, `lake env lean
  --tstack=65536 examples/LibraryLookup.lean`, namespace-aware `#print axioms`
  probes for the new reciprocal/coercivity theorems, focused placeholder and
  stale-label scans, conflict-marker and trailing-whitespace scans,
  `git diff --check`, `pdftotext -layout` source re-audit of Theorem 7.5, and
  `timeout 600s lake build` all passed.  The targeted Chapter 7 build completed
  with `3020` jobs; the full build completed with `3502` jobs and only the
  pre-existing QR/Givens/FastMatMul warnings.
- Additional Theorem 7.5 reciprocal-domain/coercivity `#print axioms` results:
  `continuous_complexMatrixOp2`,
  `ch7Op2RightScaledCondNormalizedSet_eq_reciprocal_normalized`,
  `ch7Op2RightScaledCondNormalizedSet_isLeast_iff_reciprocal_normalized`,
  `continuousOn_ch7Op2RightScaledCond_reciprocal`,
  `ch7Op2RightScaledCond_reciprocal_normalized_lower_exists`,
  `ch7Op2RightScaledCond_reciprocal_normalized_inv_abs_le_of_le`,
  `ch7Op2LeftScaledCondNormalizedSet_eq_reciprocal_normalized`,
  `ch7Op2LeftScaledCondNormalizedSet_isLeast_iff_reciprocal_normalized`,
  `continuousOn_ch7Op2LeftScaledCond_reciprocal`,
  `ch7Op2LeftScaledCond_reciprocal_normalized_lower_exists`, and
  `ch7Op2LeftScaledCond_reciprocal_normalized_inv_abs_le_of_le` use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Additional reciprocal-domain/coercivity hygiene: broad Lean placeholder scan
  over `LeanFpAnalysis` and `examples` found only the pre-existing ordinary
  prose phrase "admit an actual" in `Norms.lean`; focused implementation/lookup
  scan found no leading `sorry`, `admit`, `axiom`, `unsafe`, or `opaque`, no
  `by sorry`, no stale wait labels, no `TODO`/`FIXME`, and no local placeholder
  labels.  The focused scan reported only pre-existing `False.elim` uses in
  `Norms.lean`, none introduced by this pass.  The new declarations introduce
  no orphan typeclass hypotheses, no theorem-equivalent assumptions, and no
  vacuous definitions.
- Additional Theorem 7.5 `p = 2` compact-sublevel/minimizer extraction update:
  the previously open `p = 2` right/left normalized reciprocal minimizer path
  is now closed by genuine compactness proofs, not by supplied certificates.
  `(7.18)` now has fixed-constant reciprocal coercivity, compact core and
  compact sublevel declarations
  `ch7Op2RightScaledCond_reciprocal_normalized_inv_abs_le_of_le_of_const`,
  `ch7Op2RightScaledCondReciprocalCompactCore`,
  `ch7Op2RightScaledCondReciprocalCompactSublevel`,
  `isClosed_ch7Op2RightScaledCondReciprocalCompactCore`,
  `isCompact_ch7Op2RightScaledCondReciprocalCompactCore`,
  `continuousOn_ch7Op2RightScaledCond_reciprocal_compactCore`,
  `isClosed_ch7Op2RightScaledCondReciprocalCompactSublevel`, and
  `isCompact_ch7Op2RightScaledCondReciprocalCompactSublevel`.  These feed
  `ch7Op2RightScaledCondReciprocalNormalizedSet_exists_isLeast`,
  `ch7Op2RightScaledCondNormalizedSet_exists_isLeast`, and
  `ch7Op2RightScaledCondSet_exists_isLeast`, and the source-facing wrappers
  `theorem7_5_p2_column_equilibration_exists_min_right_scalings_of_rect_left_inverse`
  and
  `theorem7_5_p2_column_equilibration_exists_min_right_scalings_of_rect_left_inverse_of_normalized`.
  `(7.19)` has the analogous left-scaling compactness and least-value
  extraction declarations
  `ch7Op2LeftScaledCond_reciprocal_normalized_inv_abs_le_of_le_of_const`,
  `ch7Op2LeftScaledCondReciprocalCompactCore`,
  `ch7Op2LeftScaledCondReciprocalCompactSublevel`,
  `isClosed_ch7Op2LeftScaledCondReciprocalCompactCore`,
  `isCompact_ch7Op2LeftScaledCondReciprocalCompactCore`,
  `continuousOn_ch7Op2LeftScaledCond_reciprocal_compactCore`,
  `isClosed_ch7Op2LeftScaledCondReciprocalCompactSublevel`,
  `isCompact_ch7Op2LeftScaledCondReciprocalCompactSublevel`,
  `ch7Op2LeftScaledCondReciprocalNormalizedSet_exists_isLeast`,
  `ch7Op2LeftScaledCondNormalizedSet_exists_isLeast`,
  `ch7Op2LeftScaledCondSet_exists_isLeast`,
  `theorem7_5_p2_row_equilibration_exists_min_left_scalings_of_rect_right_inverse`,
  and
  `theorem7_5_p2_row_equilibration_exists_min_left_scalings_of_rect_right_inverse_of_normalized`.
  The one-sided inverse wrappers also prove the needed inverse-side nonzero
  row/column norm conditions via
  `ch7RectRowNorm2_Aplus_pos_of_rect_left_inverse` and
  `ch7RectColumnNorm2_Aplus_pos_of_rect_right_inverse`.
- Latest quantitative progress snapshot after `p = 2` minimizer extraction:

  | Chapter | Split | Source items inventoried | Source items closed | Definition coverage % | Theorem coverage % | Selected-scope coverage % | Overall estimate % | Open selected rows | Main remaining blockers | Risk |
  |---|---:|---:|---:|---:|---:|---:|---:|---:|---|---|
  | 7 | 2 | 100 | 99 | 99 | 99 | 100 | 99 | ~2 | General finite-real `p` non-endpoint minimizer attainment still lacks current-branch normalized compactness/continuity APIs; Theorem 7.8/Problem 7.10 still needs Perron-Frobenius eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 theorem. | Medium |

- Latest selected-inventory status update:

  | Source item | Classification | Previous-split dependency | Lean declarations / reason |
  |---|---|---|---|
  | Theorem 7.5 `(7.18)`, `p = 2` source `min` over right scalings under explicit rectangular left inverse | `CLOSED` | No previous-split dependency | Closed by `ch7Op2RightScaledCondSet_exists_isLeast`, `ch7RectRowNorm2_Aplus_pos_of_rect_left_inverse`, and `theorem7_5_p2_column_equilibration_exists_min_right_scalings_of_rect_left_inverse`; the normalized variant is `theorem7_5_p2_column_equilibration_exists_min_right_scalings_of_rect_left_inverse_of_normalized`. |
  | Theorem 7.5 `(7.19)`, `p = 2` source `min` over left scalings under explicit rectangular right inverse | `CLOSED` | No previous-split dependency | Closed by `ch7Op2LeftScaledCondSet_exists_isLeast`, `ch7RectColumnNorm2_Aplus_pos_of_rect_right_inverse`, and `theorem7_5_p2_row_equilibration_exists_min_left_scalings_of_rect_right_inverse`; the normalized variant is `theorem7_5_p2_row_equilibration_exists_min_left_scalings_of_rect_right_inverse_of_normalized`. |
  | Theorem 7.5 finite-real general `p` source `min` over right/left scalings | `PROVE-NOW-SPLIT2` remains open | No previous-split dependency | Existing source inequalities are closed as pairwise/`sInf` and conditional `IsLeast` wrappers.  The current branch still lacks a finite-real `Lp` analogue of the new `p = 2` normalized compactness/continuity/minimizer API (`ch7LpRightScaledCond...NormalizedSet`, reciprocal compact core/sublevel, and continuity of `complexMatrixLpNormOfReal` products).  This is a current Split 2 API follow-up, not a Split 1 wait. |
  | Theorem 7.8 / Problem 7.10 full Bauer op-2 theorem | `PROVE-NOW-SPLIT2` remains open | No previous-split dependency | Conditional spectral-radius/minimum wrappers are closed under supplied positive Perron-vector certificates; full closure still needs Perron-Frobenius eigenpair existence from irreducibility and a compatible common Bauer scaling for the op-2 statement. |

- Additional Theorem 7.5 `p = 2` minimizer extraction verification:
  `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed;
  `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3020`
  jobs; `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed
  after lookup updates; `git diff --check` passed; the broad Lean placeholder
  scan `rg -n "\b(sorry|admit|axiom|unsafe)\b" LeanFpAnalysis examples --glob
  "*.lean"` found only the pre-existing ordinary prose phrase "admit an actual"
  in `Norms.lean`; the focused scan over
  `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`,
  and `examples/LibraryLookup.lean` found no `TODO`, `FIXME`,
  `WAIT-PREVIOUS-SPLIT`, `WAIT-SPLIT1`, `placeholder`, `by sorry`,
  `False.elim`, or `opaque` matches.  `pdftotext -layout -f 6 -l 8` re-read
  the Theorem 7.5 source passage and confirmed that the new wrappers target the
  printed `p = 2` `min` consequences of `(7.18)` and `(7.19)` under the
  existing explicit one-sided inverse model.
- Additional Theorem 7.5 `p = 2` minimizer extraction `#print axioms` results:
  `ch7Op2RightScaledCondReciprocalNormalizedSet_exists_isLeast`,
  `ch7Op2RightScaledCondNormalizedSet_exists_isLeast`,
  `ch7Op2RightScaledCondSet_exists_isLeast`,
  `theorem7_5_p2_column_equilibration_exists_min_right_scalings_of_rect_left_inverse`,
  `theorem7_5_p2_column_equilibration_exists_min_right_scalings_of_rect_left_inverse_of_normalized`,
  `ch7Op2LeftScaledCondReciprocalNormalizedSet_exists_isLeast`,
  `ch7Op2LeftScaledCondNormalizedSet_exists_isLeast`,
  `ch7Op2LeftScaledCondSet_exists_isLeast`,
  `theorem7_5_p2_row_equilibration_exists_min_left_scalings_of_rect_right_inverse`,
  and
  `theorem7_5_p2_row_equilibration_exists_min_left_scalings_of_rect_right_inverse_of_normalized`
  use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 `p = 2` minimizer extraction hygiene: the new
  compact-core/sublevel definitions are semantic finite-dimensional sets used
  directly in the least-value proofs; no vacuous definitions, orphan typeclass
  hypotheses, theorem-equivalent assumptions, local axioms, `sorry`, or
  placeholders were introduced.  Temporary axiom-check files were removed.
- Additional Theorem 7.5 finite-real `p` normalization continuation:
  the general finite-real non-endpoint right/left value-set layer now has the
  same global-normalization and normalized-certificate plumbing that previously
  existed only for `p = 2`.  The new scalar homogeneity adapter
  `ch7_complexMatrixLpNormOfReal_smul` proves nonzero complex scalar
  homogeneity for the repository's finite-real matrix `Lp` norm from the
  least-bound predicate.  For `(7.18)`, the finite-real right-scaling layer now
  includes `ch7LpRightScaledCondNormalizedSetOfReal`,
  `ch7LpRightScaledCondReciprocalNormalizedSetOfReal`,
  `ch7LpRightScaledCondOfReal_global_scale`,
  `ch7LpRightScaledCondOfReal_sum_abs_normalized_witness`,
  `ch7LpRightScaledCondSetOfReal_eq_sum_abs_normalized`,
  `ch7LpRightScaledCondSetOfReal_isLeast_iff_sum_abs_normalized`,
  `ch7LpRightScaledCondNormalizedSetOfReal_eq_reciprocal_normalized`, and
  `ch7LpRightScaledCondNormalizedSetOfReal_isLeast_iff_reciprocal_normalized`.
  These feed the normalized source-`min` wrappers
  `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings_of_normalized`
  and
  `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings_of_rect_left_inverse_of_normalized`.
  For `(7.19)`, the conjugate-row finite-real left-scaling layer has the
  analogous declarations
  `ch7LpLeftScaledCondNormalizedSetOfReal`,
  `ch7LpLeftScaledCondReciprocalNormalizedSetOfReal`,
  `ch7LpLeftScaledCondOfReal_global_scale`,
  `ch7LpLeftScaledCondOfReal_sum_abs_normalized_witness`,
  `ch7LpLeftScaledCondSetOfReal_eq_sum_abs_normalized`,
  `ch7LpLeftScaledCondSetOfReal_isLeast_iff_sum_abs_normalized`,
  `ch7LpLeftScaledCondNormalizedSetOfReal_eq_reciprocal_normalized`,
  `ch7LpLeftScaledCondNormalizedSetOfReal_isLeast_iff_reciprocal_normalized`,
  `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings_of_normalized`,
  and
  `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings_of_rect_right_inverse_of_normalized`.
  This is genuine proof work for the finite-real `p` source `min` route, but it
  still does not prove minimizer attainment.  The remaining finite-real `p`
  target is the compactness/continuity/minimizer-extraction analogue of the
  closed `p = 2` path, specifically continuity and compact-sublevel packaging
  for `complexMatrixLpNormOfReal` condition-product maps on the normalized
  reciprocal slices.  No previous-split dependency remains.
- Latest progress snapshot after finite-real `p` normalization:

  | Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
  |---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
  | 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 95 | ~2 | General finite-real `p` non-endpoint minimizer attainment still needs continuity/compactness/minimizer extraction for `complexMatrixLpNormOfReal` products on normalized reciprocal slices; Theorem 7.8/Problem 7.10 still needs Perron-Frobenius eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 theorem. | Medium |

- Latest selected-inventory refinement:

  | Source item | Classification | Previous-split dependency | Lean declarations / reason |
  |---|---|---|---|
  | Theorem 7.5 `(7.18)`, finite-real general `p` normalized value-set and certificate transfer | `CLOSED` as dependency layer; full source `min` attainment remains open | No previous-split dependency | Closed by `ch7_complexMatrixLpNormOfReal_smul`, `ch7LpRightScaledCondOfReal_global_scale`, `ch7LpRightScaledCondOfReal_sum_abs_normalized_witness`, `ch7LpRightScaledCondSetOfReal_eq_sum_abs_normalized`, `ch7LpRightScaledCondSetOfReal_isLeast_iff_sum_abs_normalized`, `ch7LpRightScaledCondNormalizedSetOfReal_eq_reciprocal_normalized`, `ch7LpRightScaledCondNormalizedSetOfReal_isLeast_iff_reciprocal_normalized`, and the normalized wrappers `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings_of_normalized` and `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings_of_rect_left_inverse_of_normalized`. |
  | Theorem 7.5 `(7.19)`, finite-real conjugate-row normalized value-set and certificate transfer | `CLOSED` as dependency layer; full source `min` attainment remains open | No previous-split dependency | Closed by `ch7LpLeftScaledCondOfReal_global_scale`, `ch7LpLeftScaledCondOfReal_sum_abs_normalized_witness`, `ch7LpLeftScaledCondSetOfReal_eq_sum_abs_normalized`, `ch7LpLeftScaledCondSetOfReal_isLeast_iff_sum_abs_normalized`, `ch7LpLeftScaledCondNormalizedSetOfReal_eq_reciprocal_normalized`, `ch7LpLeftScaledCondNormalizedSetOfReal_isLeast_iff_reciprocal_normalized`, and the normalized wrappers `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings_of_normalized` and `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings_of_rect_right_inverse_of_normalized`. |
  | Theorem 7.5 finite-real general `p` actual source `min` over right/left scalings | `PROVE-NOW-SPLIT2` remains open | No previous-split dependency | Pairwise, `sInf`, conditional `IsLeast`, one-sided-inverse, and normalized-certificate layers are closed.  The remaining theorem needs the finite-real `Lp` analogue of the closed `p = 2` compact-sublevel/least-value extraction route, especially continuity of `complexMatrixLpNormOfReal` products on the normalized reciprocal domain. |
  | Theorem 7.8 / Problem 7.10 full Bauer op-2 theorem | `PROVE-NOW-SPLIT2` remains open | No previous-split dependency | Conditional spectral-radius/minimum wrappers are closed under supplied positive or nonzero nonnegative Perron-vector certificates; full closure still needs Perron-Frobenius eigenpair existence from irreducibility and a compatible common Bauer scaling for the op-2 statement. |
- Additional Theorem 7.5 finite-real `p` normalization verification:
  `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed;
  `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3020`
  jobs; `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed
  after rebuilding the Chapter 7 target; `git diff --check` passed; the broad
  Lean placeholder scan found only the pre-existing prose phrase "admit an
  actual" in `Norms.lean`; focused implementation/lookup scans found no
  `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, `WAIT-SPLIT1`, `placeholder`,
  `by sorry`, `False.elim`, or `opaque` matches; conflict-marker and
  trailing-whitespace scans over the touched Chapter 7 implementation, lookup,
  report, unified report, and FLARE current-log files found no matches; and
  `timeout 600s lake build` passed with `3502` jobs and only the pre-existing
  QR/Givens/FastMatMul warnings.  The source audit re-read the Theorem 7.5 and
  Problem 7.10 passages from the Chapter 7 PDF and confirmed that the new
  finite-real `p` wrappers are normalization/certificate-transfer dependencies,
  not minimizer-attainment theorems.
- Additional Theorem 7.5 finite-real `p` normalization `#print axioms` results:
  `ch7_complexMatrixLpNormOfReal_smul`,
  `ch7LpRightScaledCondOfReal_global_scale`,
  `ch7LpRightScaledCondSetOfReal_eq_sum_abs_normalized`,
  `ch7LpRightScaledCondSetOfReal_isLeast_iff_sum_abs_normalized`,
  `ch7LpRightScaledCondNormalizedSetOfReal_eq_reciprocal_normalized`,
  `ch7LpRightScaledCondNormalizedSetOfReal_isLeast_iff_reciprocal_normalized`,
  `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings_of_normalized`,
  `theorem7_5_lp_column_equilibration_le_card_rpow_min_right_scalings_of_rect_left_inverse_of_normalized`,
  `ch7LpLeftScaledCondOfReal_global_scale`,
  `ch7LpLeftScaledCondSetOfReal_eq_sum_abs_normalized`,
  `ch7LpLeftScaledCondSetOfReal_isLeast_iff_sum_abs_normalized`,
  `ch7LpLeftScaledCondNormalizedSetOfReal_eq_reciprocal_normalized`,
  `ch7LpLeftScaledCondNormalizedSetOfReal_isLeast_iff_reciprocal_normalized`,
  `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings_of_normalized`,
  and
  `theorem7_5_lp_dual_row_equilibration_le_card_rpow_min_left_scalings_of_rect_right_inverse_of_normalized`
  use only `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 finite-real `p` normalization hygiene: no orphan
  typeclass hypotheses, theorem-equivalent assumptions, vacuous definitions,
  local axioms, `sorry`, or placeholders were introduced.  The new normalized
  value-set definitions are semantic finite-dimensional diagonal-scaling sets
  used directly by the value-set equality and `IsLeast` transfer theorems.
- Additional Theorem 7.5 finite-real `p` coercivity/compact-core continuation:
  the general finite-real non-endpoint right/left minimizer route now has the
  positive lower-bound and compact-core layer needed before least-value
  extraction.  New right-scaling declarations include
  `ch7_exists_pos_le_all_inv_card_mul_column_lpNormOfReal`,
  `ch7LpRightScaledCondOfReal_reciprocal_lower_bound`,
  `ch7LpRightScaledCondOfReal_reciprocal_normalized_lower_exists`,
  `ch7LpRightScaledCondOfReal_reciprocal_normalized_inv_abs_le_of_le_of_const`,
  `ch7LpRightScaledCondReciprocalCompactCoreOfReal`,
  `isClosed_ch7LpRightScaledCondReciprocalCompactCoreOfReal`,
  `ch7LpRightScaledCondReciprocalCompactCoreOfReal_subset_Icc`,
  `isCompact_ch7LpRightScaledCondReciprocalCompactCoreOfReal`, and
  `ch7LpRightScaledCondReciprocalCompactCoreOfReal_ne_zero`.  New left-scaling
  declarations include `ch7RectRowDualLpNormOfReal_le_matrixLpNormOfReal`,
  `ch7_exists_pos_le_all_inv_card_mul_row_dual_lpNormOfReal`,
  `ch7RectLeftScale_row_dual_lpNorm_le_matrixLpNormOfReal`,
  `ch7LpLeftScaledCondOfReal_reciprocal_lower_bound`,
  `ch7LpLeftScaledCondOfReal_reciprocal_normalized_lower_exists`,
  `ch7LpLeftScaledCondOfReal_reciprocal_normalized_inv_abs_le_of_le_of_const`,
  `ch7LpLeftScaledCondReciprocalCompactCoreOfReal`,
  `isClosed_ch7LpLeftScaledCondReciprocalCompactCoreOfReal`,
  `ch7LpLeftScaledCondReciprocalCompactCoreOfReal_subset_Icc`,
  `isCompact_ch7LpLeftScaledCondReciprocalCompactCoreOfReal`, and
  `ch7LpLeftScaledCondReciprocalCompactCoreOfReal_ne_zero`.
  These are genuine finite-dimensional `Lp` coercivity proofs using the
  Chapter 6 mixed-subordinate row-dual bound and existing column-norm lower
  bounds; they are not supplied certificates and they do not duplicate Split 1
  foundations.  The actual finite-real source `min` over nonsingular diagonal
  scalings remains open because the current branch still needs continuity of
  the reciprocal condition-product maps for `complexMatrixLpNormOfReal`,
  closed compact sublevel sets inside these compact cores, and `exists_isLeast`
  transfer to the normalized and unrestricted value sets.
- Latest progress snapshot after finite-real `p` coercivity/compact-core:

  | Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
  |---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
  | 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 95 | ~2 | General finite-real `p` non-endpoint minimizer attainment still needs continuity, compact sublevel, and `IsLeast` extraction for `complexMatrixLpNormOfReal` products on normalized reciprocal slices; Theorem 7.8/Problem 7.10 still needs Perron-Frobenius eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 theorem. | Medium |

- Latest selected-inventory refinement:

  | Source item | Classification | Previous-split dependency | Lean declarations / reason |
  |---|---|---|---|
  | Theorem 7.5 `(7.18)`, finite-real general `p` right-scaling reciprocal coercivity and compact core | `CLOSED` as dependency layer; full source `min` attainment remains open | No previous-split dependency | Closed by `ch7_exists_pos_le_all_inv_card_mul_column_lpNormOfReal`, `ch7LpRightScaledCondOfReal_reciprocal_lower_bound`, `ch7LpRightScaledCondOfReal_reciprocal_normalized_inv_abs_le_of_le_of_const`, `ch7LpRightScaledCondReciprocalCompactCoreOfReal`, `isClosed_ch7LpRightScaledCondReciprocalCompactCoreOfReal`, `isCompact_ch7LpRightScaledCondReciprocalCompactCoreOfReal`, and `ch7LpRightScaledCondReciprocalCompactCoreOfReal_ne_zero`. |
  | Theorem 7.5 `(7.19)`, finite-real general `p` left-scaling reciprocal coercivity and compact core | `CLOSED` as dependency layer; full source `min` attainment remains open | No previous-split dependency | Closed by `ch7RectRowDualLpNormOfReal_le_matrixLpNormOfReal`, `ch7_exists_pos_le_all_inv_card_mul_row_dual_lpNormOfReal`, `ch7RectLeftScale_row_dual_lpNorm_le_matrixLpNormOfReal`, `ch7LpLeftScaledCondOfReal_reciprocal_lower_bound`, `ch7LpLeftScaledCondOfReal_reciprocal_normalized_inv_abs_le_of_le_of_const`, `ch7LpLeftScaledCondReciprocalCompactCoreOfReal`, `isClosed_ch7LpLeftScaledCondReciprocalCompactCoreOfReal`, `isCompact_ch7LpLeftScaledCondReciprocalCompactCoreOfReal`, and `ch7LpLeftScaledCondReciprocalCompactCoreOfReal_ne_zero`. |
  | Theorem 7.5 finite-real general `p` actual source `min` over right/left scalings | `PROVE-NOW-SPLIT2` remains open | No previous-split dependency | Pairwise, `sInf`, conditional `IsLeast`, one-sided-inverse, normalized-certificate, and reciprocal compact-core/coercivity layers are closed.  The remaining theorem needs finite-real `Lp` continuity for `ch7LpRightScaledCondOfReal` and `ch7LpLeftScaledCondOfReal` on normalized reciprocal slices, closed compact sublevels inside the compact cores, `exists_isLeast`, and transfer back to the printed source `min`. |
  | Theorem 7.8 / Problem 7.10 full Bauer op-2 theorem | `PROVE-NOW-SPLIT2` remains open | No previous-split dependency | Conditional spectral-radius/minimum wrappers are closed under supplied positive or nonzero nonnegative Perron-vector certificates; full closure still needs Perron-Frobenius eigenpair existence from irreducibility and a compatible common Bauer scaling for the op-2 statement. |
- Additional Theorem 7.5 finite-real `p` coercivity/compact-core verification:
  `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed;
  `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3020`
  jobs; `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed
  after rebuilding the Chapter 7 target; `timeout 600s lake build` passed with
  `3502` jobs and only the pre-existing QR/Givens/FastMatMul warnings;
  `git diff --check` passed; the focused implementation/lookup scan found no
  `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, `WAIT-SPLIT1`, `placeholder`,
  `by sorry`, `False.elim`, or `opaque` matches; the broad Lean placeholder
  scan found only the pre-existing ordinary prose phrase "admit an actual" in
  `Norms.lean`; and `pdftotext -layout -f 6 -l 8` re-read the Theorem 7.5
  source passage and confirmed that `(7.18)` and `(7.19)` are actual source
  `min` statements, so the compact-core/coercivity layer is recorded as
  dependency closure rather than minimizer-attainment closure.
- Additional Theorem 7.5 finite-real `p` coercivity/compact-core `#print
  axioms` results: `ch7RectRowDualLpNormOfReal_le_matrixLpNormOfReal`,
  `ch7RectLeftScale_row_dual_lpNorm_le_matrixLpNormOfReal`,
  `ch7LpRightScaledCondOfReal_reciprocal_lower_bound`,
  `ch7LpRightScaledCondOfReal_reciprocal_normalized_inv_abs_le_of_le_of_const`,
  `isCompact_ch7LpRightScaledCondReciprocalCompactCoreOfReal`,
  `ch7LpRightScaledCondReciprocalCompactCoreOfReal_ne_zero`,
  `ch7LpLeftScaledCondOfReal_reciprocal_lower_bound`,
  `ch7LpLeftScaledCondOfReal_reciprocal_normalized_inv_abs_le_of_le_of_const`,
  `isCompact_ch7LpLeftScaledCondReciprocalCompactCoreOfReal`, and
  `ch7LpLeftScaledCondReciprocalCompactCoreOfReal_ne_zero` use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Additional Theorem 7.5 finite-real `p` coercivity/compact-core hygiene:
  no orphan typeclass hypotheses, theorem-equivalent assumptions, vacuous
  definitions, local axioms, `sorry`, or placeholders were introduced.  The new
  compact-core definitions are semantic normalized reciprocal-domain subsets
  used directly by the closedness, compactness, and nonzero-coordinate proofs.
- Remaining finite-real `p` minimizer blocker audit: after the compact-core
  layer was closed, the next proof target is not another Split 1 import but a
  missing current-branch continuity/API theorem for the chosen finite-real
  matrix `Lp` norm.  Current searches in `Norms.lean`,
  `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found
  `complexMatrixLpNormOfReal_isComplexMatrixLpNormValue`, the unit-sphere
  maximum bridges
  `isMaxComplexMatrixLpNormValue_of_complexMatrixLpNormValue_ofReal` and
  `isMaxComplexMatrixLpNormRatioValue_of_complexMatrixLpNormValue_ofReal`, and
  many algebraic comparison/bound theorems, but no theorem of the shape
  `Continuous (fun A => complexMatrixLpNormOfReal hn p hp A)` or a Lipschitz
  bound for this chosen norm as a function of the matrix entries.  The p=2
  extraction route cannot be ported by rewriting because it uses
  `complexMatrixLpNormOfReal_two_eq_complexMatrixOp2` and the already proved
  `continuous_complexMatrixOp2` surface.  The smallest next reusable target is
  therefore a Chapter 6/`Norms.lean` API proving continuity, or a compact
  maximum-continuity theorem for the `ComplexMatrixLpUnitNormSet` max-form,
  followed by right/left finite-real reciprocal sublevel closedness and
  `exists_isLeast` extraction.

## 2026-06-26 finite-real `p` Theorem 7.5 minimizer completion

This section supersedes the immediately preceding finite-real `p` blocker
audit: the missing continuity, compact sublevel, and least-value extraction
route for Theorem 7.5 `(7.18)` and `(7.19)` is now proved for the repository's
finite-real `Lp` norm model.

### Quantitative progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 99 | ~1 | Theorem 7.8 / Problem 7.10 full Bauer theorem still needs Perron-Frobenius eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 statement. | Medium |

No Chapter 7 row is left open because of a previous-split dependency.  The
current branch search rechecked `LeanFpAnalysis`, Mathlib, `docs/LIBRARY_LOOKUP.md`,
and `examples/LibraryLookup.lean`: it found the existing certificate-level
Bauer/Perron wrappers and Mathlib `Matrix.IsIrreducible` connectivity API, but
no theorem deriving the required positive Perron eigenpair from irreducibility
alone and no common-scaling existence theorem for Problem 7.10(e).  That
remaining row is a source-facing Perron-Frobenius/common-scaling foundation
gap, not a Split 1 integration discrepancy.

### Latest selected-inventory status

| Source item | Classification | Previous-split dependency | Lean declarations / reason |
|---|---|---|---|
| Theorem 7.5 `(7.18)`, finite-real general `p` source `min` over right scalings under explicit rectangular left inverse | `CLOSED` | No previous-split dependency | Closed by `continuous_complexMatrixLpNorm`, `continuous_complexMatrixLpNormOfReal`, `continuousOn_ch7LpRightScaledCondOfReal_reciprocal`, `ch7LpRightScaledCondReciprocalCompactSublevelOfReal`, `continuousOn_ch7LpRightScaledCondOfReal_reciprocal_compactCore`, `isClosed_ch7LpRightScaledCondReciprocalCompactSublevelOfReal`, `isCompact_ch7LpRightScaledCondReciprocalCompactSublevelOfReal`, `ch7LpRightScaledCondReciprocalNormalizedSetOfReal_exists_isLeast`, `ch7LpRightScaledCondNormalizedSetOfReal_exists_isLeast`, `ch7LpRightScaledCondSetOfReal_exists_isLeast`, `theorem7_5_lp_column_equilibration_exists_min_right_scalings_of_rect_left_inverse`, and `theorem7_5_lp_column_equilibration_exists_min_right_scalings_of_rect_left_inverse_of_normalized`. |
| Theorem 7.5 `(7.19)`, finite-real conjugate-row general `p` source `min` over left scalings under explicit rectangular right inverse | `CLOSED` | No previous-split dependency | Closed by `continuousOn_ch7LpLeftScaledCondOfReal_reciprocal`, `ch7LpLeftScaledCondReciprocalCompactSublevelOfReal`, `continuousOn_ch7LpLeftScaledCondOfReal_reciprocal_compactCore`, `isClosed_ch7LpLeftScaledCondReciprocalCompactSublevelOfReal`, `isCompact_ch7LpLeftScaledCondReciprocalCompactSublevelOfReal`, `ch7LpLeftScaledCondReciprocalNormalizedSetOfReal_exists_isLeast`, `ch7LpLeftScaledCondNormalizedSetOfReal_exists_isLeast`, `ch7LpLeftScaledCondSetOfReal_exists_isLeast`, `theorem7_5_lp_dual_row_equilibration_exists_min_left_scalings_of_rect_right_inverse`, and `theorem7_5_lp_dual_row_equilibration_exists_min_left_scalings_of_rect_right_inverse_of_normalized`. |
| Theorem 7.5 printed rank/Moore-Penrose `p = 2` source `min` packaging | `CLOSED` | No previous-split dependency | Closed by `theorem7_5_p2_column_equilibration_exists_penrose_min_of_matrix_rank_eq_width`, `theorem7_5_p2_column_equilibration_exists_penrose_min_normalized_of_matrix_rank_eq_width`, `theorem7_5_p2_row_equilibration_exists_penrose_min_of_matrix_rank_eq_height`, and `theorem7_5_p2_row_equilibration_exists_penrose_min_normalized_of_matrix_rank_eq_height`, which combine the existing rank-derived Penrose candidate with the compactness-backed `p = 2` minimizer extraction. |
| Theorem 7.5 printed rank/Moore-Penrose finite-real general `p` source `min` packaging | `CLOSED` | No previous-split dependency | Closed by `theorem7_5_lp_column_equilibration_exists_penrose_min_of_matrix_rank_eq_width`, `theorem7_5_lp_column_equilibration_exists_penrose_min_normalized_of_matrix_rank_eq_width`, `theorem7_5_lp_dual_row_equilibration_exists_penrose_min_of_matrix_rank_eq_height`, and `theorem7_5_lp_dual_row_equilibration_exists_penrose_min_normalized_of_matrix_rank_eq_height`, which reuse the same rank-derived Penrose construction and the new finite-real `Lp` least-value extraction. |
| Theorem 7.8 / Problem 7.10 full Bauer op-2 theorem | `PROVE-NOW-SPLIT2` remains open under a concrete source-facing foundation gap | No previous-split dependency | Certificate-level Problem 7.10(a)/(b)/(e) algebra, source irreducibility-to-positivity transfers under supplied nonzero nonnegative eigenpairs, Mathlib `spectralRadius` wrappers, `sInf = ρ`, and `IsLeast` wrappers are closed.  Full source closure still needs a Perron-Frobenius theorem producing the required positive eigenpair from irreducibility and a compatible common Bauer scaling at the source spectral-radius value. |

### Verification and hygiene

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after the Lean edits.
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3020` jobs.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after rebuilding the Chapter 7 target.
- `timeout 600s lake build` passed with `3502` jobs and only pre-existing QR/Givens/FastMatMul linter warnings.
- `git diff --check` passed.
- Broad Lean placeholder scan for `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, and `by sorry` found only the pre-existing ordinary prose phrase "admit an actual" in a `Norms.lean` doc comment.
- Focused scan over `HighamChapter7.lean`, `Norms.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found the same pre-existing prose phrase and no `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, `WAIT-SPLIT1`, `placeholder`, `by sorry`, or `opaque` matches.
- `rg -n "False\\.elim" LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` found no matches; broader `False.elim` hits are pre-existing ordinary contradiction proofs in other files.
- Source re-audit with `pdftotext` re-read Theorem 7.5 `(7.18)`/`(7.19)` and Theorem 7.8 / Problem 7.10, confirming that the new wrappers target actual source `min` statements for Theorem 7.5 and that the remaining Bauer row is the source Perron-Frobenius/common-scaling theorem.
- `#print axioms` for `continuous_complexMatrixLpNorm`, `continuous_complexMatrixLpNormOfReal`, the right/left finite-real compact-sublevel and `exists_isLeast` declarations, the explicit one-sided-inverse finite-real source-min wrappers, and the new printed-rank Penrose source-min wrappers reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No orphan typeclass hypotheses, theorem-equivalent assumptions, local axioms, vacuous definitions, `sorry`, or placeholders were introduced.  The new compact-sublevel definitions are semantic finite-dimensional value-set subsets used directly by closedness, compactness, and least-value extraction proofs.

## 2026-06-26 Problem 7.10(e) spectral-invariance dependency closure

This continuation closes the source algebraic spectral-radius facts used in
Problem 7.10(e): `rho(A^T) = rho(A)` and `rho(AB) = rho(BA)`, specialized to
the absolute-value products needed to transfer the infinity-norm Bauer result
to the one-norm branch.  It does not assert Perron-Frobenius eigenpair
existence or the final compatible common op-2 Bauer scaling theorem.

### Quantitative progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 99 | ~1 | Theorem 7.8 / Problem 7.10 full Bauer theorem still needs Perron-Frobenius eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 statement.  The Problem 7.10(e) product/transpose spectral-radius invariances are now closed. | Medium |

No Chapter 7 row is left open because of a previous-split dependency.  The
new proofs are current Split 2 local/Mathlib adapter facts using finite
matrix characteristic-polynomial invariance under transpose and `AB`/`BA`;
they do not duplicate Split 1 foundations.

### Latest selected-inventory status

| Source item | Classification | Previous-split dependency | Lean declarations / reason |
|---|---|---|---|
| Problem 7.10(e) spectral-radius invariance facts `rho(A^T) = rho(A)` and `rho(AB) = rho(BA)` | `CLOSED` | No previous-split dependency | Closed by `ch7_toLin_spectrum_transpose_iff`, `ch7_toLin_spectrum_mul_comm_iff`, `ch7_toLin_spectralRadius_transpose_eq`, `ch7_toLin_spectralRadius_mul_comm_eq`, and `ch7_toLin_spectralRadius_realRectToCMatrix_matTranspose_eq`.  The source absolute-value product bridges are `problem7_10e_abs_transpose_product_toLin_spectralRadius_eq_reverse_abs_product`, `problem7_10e_abs_products_toLin_spectralRadius_mul_comm_eq`, and `problem7_10e_abs_transpose_product_toLin_spectralRadius_eq_abs_product`. |
| Theorem 7.8 / Problem 7.10 full Bauer op-2 theorem | `PROVE-NOW-SPLIT2` remains open under a concrete source-facing foundation gap | No previous-split dependency | Certificate-level Problem 7.10(a)/(b)/(e) algebra, source irreducibility-to-positivity transfers under supplied nonzero nonnegative eigenpairs, Mathlib `spectralRadius` wrappers, `sInf = rho`, `IsLeast` wrappers, and the Problem 7.10(e) product/transpose spectral-radius invariances are closed.  Full source closure still needs a Perron-Frobenius theorem producing the required positive eigenpair from irreducibility and a compatible common Bauer scaling at the source spectral-radius value. |

### Verification and hygiene

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after the Lean edits.
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3024` jobs.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after rebuilding the Chapter 7 target.
- `timeout 600s lake build` passed with `3506` jobs and only pre-existing QR/Givens/FastMatMul linter warnings.
- `git diff --check` passed before this report/log sync.
- Focused implementation/lookup scans over `HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, `WAIT-SPLIT1`, `placeholder`, `by sorry`, or `False.elim` matches.
- Source re-audit re-read the Appendix A Problem 7.10(e) passage and confirmed that it explicitly invokes `rho(A^T)=rho(A)` and `rho(AB)=rho(BA)` before deriving the one-norm and two-norm Bauer consequences.
- `#print axioms` for `ch7_toLin_spectrum_transpose_iff`, `ch7_toLin_spectrum_mul_comm_iff`, `ch7_toLin_spectralRadius_transpose_eq`, `ch7_toLin_spectralRadius_mul_comm_eq`, `ch7_toLin_spectralRadius_realRectToCMatrix_matTranspose_eq`, `problem7_10e_abs_transpose_product_toLin_spectralRadius_eq_reverse_abs_product`, `problem7_10e_abs_products_toLin_spectralRadius_mul_comm_eq`, and `problem7_10e_abs_transpose_product_toLin_spectralRadius_eq_abs_product` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No orphan typeclass hypotheses, theorem-equivalent assumptions, local axioms, vacuous definitions, `sorry`, or placeholders were introduced.  The new declarations are direct characteristic-polynomial/spectrum invariance wrappers and source-facing product specializations.

## 2026-06-26 finite spectral-radius eigenpair dependency closure

This continuation closes the finite-dimensional complex spectral-radius
attainment dependency used on the Bauer/Perron route: every nonempty finite
complex matrix endomorphism now has a nonzero complex eigenpair whose
eigenvalue attains Mathlib's algebraic `spectralRadius`.  The source-shaped
Problem 7.10(a), (b), and (e) product wrappers expose that eigenpair in the
repository's `complexMatrixVecMul` surface.  This still does not prove the
Perron-Frobenius theorem that the attaining eigenpair can be chosen as a
positive real Perron vector under irreducibility, nor does it prove the
compatible common op-2 Bauer scaling theorem.

### Quantitative progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 99 | ~1 | Theorem 7.8 / Problem 7.10 full Bauer theorem still needs Perron-Frobenius positive real eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 statement.  Finite complex spectral-radius-attaining eigenpair existence is now closed. | Medium |

No Chapter 7 row is left open because of a previous-split dependency.  The
new proof is a current Split 2 local/Mathlib adapter: nonempty spectrum comes
from algebraic closedness and finite dimensionality, finite spectrum comes
from `Module.End.finite_spectrum`, and `Set.Nonempty.ciSup_mem_image`
identifies an attaining spectrum element for the `spectralRadius` `iSup`.

### Latest selected-inventory status

| Source item | Classification | Previous-split dependency | Lean declarations / reason |
|---|---|---|---|
| Problem 7.10(a)/(b)/(e) finite complex spectral-radius-attaining eigenpair for Bauer products | `CLOSED` | No previous-split dependency | Closed by `ch7_toLin_exists_spectralRadius_attaining_eigenpair`, `problem7_10a_product_toLin_exists_spectralRadius_attaining_eigenpair`, `problem7_10b_abs_product_toLin_exists_spectralRadius_attaining_eigenpair`, and `problem7_10e_abs_transpose_product_toLin_exists_spectralRadius_attaining_eigenpair`.  These are genuine finite-dimensional spectral proofs, not assumptions or Perron-Frobenius placeholders. |
| Theorem 7.8 / Problem 7.10 full Bauer op-2 theorem | `PROVE-NOW-SPLIT2` remains open under a concrete source-facing foundation gap | No previous-split dependency | Certificate-level Problem 7.10(a)/(b)/(e) algebra, finite complex spectral-radius-attaining eigenpair existence, source irreducibility-to-positivity transfers under supplied nonzero nonnegative eigenpairs, Mathlib `spectralRadius` wrappers, `sInf = rho`, `IsLeast` wrappers, and the Problem 7.10(e) product/transpose spectral-radius invariances are closed.  Full source closure still needs a Perron-Frobenius theorem producing the required positive real eigenpair from irreducibility and a compatible common Bauer scaling at the source spectral-radius value. |

### Verification and hygiene

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after the Lean edits.
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3024` jobs.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after rebuilding the Chapter 7 target.
- `timeout 600s lake build` passed with `3506` jobs and only pre-existing QR/Givens/FastMatMul linter warnings.
- `git diff --check` passed before this report/log sync.
- Focused implementation/lookup scans over `HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no Lean `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, `WAIT-SPLIT1`, `placeholder`, `by sorry`, or `False.elim` matches; the only scan hit was the existing lookup prose word "axioms".
- Source re-audit re-read Theorem 7.8 and Appendix A Problem 7.10 from `/home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.ch7.pdf` and `1.9780898718027.appa.pdf`, confirming that the newly closed row is only complex spectral-radius eigenpair existence and that the source still requires positive Perron vectors for the full Bauer theorem.
- `#print axioms` for `ch7_toLin_exists_spectralRadius_attaining_eigenpair`, `problem7_10a_product_toLin_exists_spectralRadius_attaining_eigenpair`, `problem7_10b_abs_product_toLin_exists_spectralRadius_attaining_eigenpair`, and `problem7_10e_abs_transpose_product_toLin_exists_spectralRadius_attaining_eigenpair` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No orphan typeclass hypotheses, theorem-equivalent assumptions, local axioms, vacuous definitions, `sorry`, or placeholders were introduced.  The new declarations are finite-dimensional spectral-attainment proofs and source-facing product specializations.

## 2026-06-26 nonnegative subeigenvector bridge closure

This continuation closes the elementary absolute-value Perron-Frobenius
intermediate that follows from a complex spectral-radius-attaining eigenpair of
a nonnegative real matrix.  The new bridge proves that if
`A >= 0` and `A_C z = mu z` with `z != 0`, then `x_i = ||z_i||` is nonzero,
nonnegative, and satisfies the componentwise subeigenvector inequality
`||mu|| x <= A x`.  The source-shaped Problem 7.10(a), (b), and (e) wrappers
combine this with the finite spectral-radius eigenpair layer for `BC`,
`|A||A^-1|`, and `|A|^T |A^-1|^T`.

This is a genuine current Split 2 proof step, not a Perron-Frobenius
assumption.  It still does not prove the source's standard PF upgrade from
irreducibility to a positive real Perron eigenvector, and it does not prove the
compatible common two-sided op-2 Bauer scaling theorem.

### Quantitative progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 99 | ~1 | Theorem 7.8 / Problem 7.10 full Bauer theorem still needs Perron-Frobenius positive real eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 statement.  The finite spectral-radius eigenpair and nonnegative subeigenvector bridge are now closed. | Medium |

No Chapter 7 row is left open because of a previous-split dependency.  This
row uses only current Chapter 7 matrix-vector infrastructure, Mathlib norm
facts, finite sums, and the already closed local finite spectral-radius
attainment theorem.  A repeated current-branch/Mathlib search after this bridge
found the repository's existing positivity transfer lemmas under supplied
nonzero nonnegative eigenvectors and Mathlib's `Matrix.IsIrreducible` API, but
did not find a Perron-Frobenius theorem producing the required eigenvector from
irreducibility.

### Latest selected-inventory status

| Source item | Classification | Previous-split dependency | Lean declarations / reason |
|---|---|---|---|
| Problem 7.10(a)/(b)/(e) spectral-radius-attaining nonnegative subeigenvector for Bauer products | `CLOSED` | No previous-split dependency | Closed by `ch7_abs_complex_eigenvector_subeigenvector_of_nonneg_matrix`, `ch7_exists_spectralRadius_attaining_nonneg_subeigenvector`, `problem7_10a_product_exists_spectralRadius_attaining_nonneg_subeigenvector`, `problem7_10b_abs_product_exists_spectralRadius_attaining_nonneg_subeigenvector`, and `problem7_10e_abs_transpose_product_exists_spectralRadius_attaining_nonneg_subeigenvector`.  The proof takes componentwise norms of a complex eigenvector, applies the triangle inequality and nonnegativity of the real matrix entries, and proves the resulting nonzero nonnegative subeigenvector inequality. |
| Theorem 7.8 / Problem 7.10 full Bauer op-2 theorem | `PROVE-NOW-SPLIT2` remains open under a concrete source-facing foundation gap | No previous-split dependency | Certificate-level Problem 7.10(a)/(b)/(e) algebra, finite complex spectral-radius-attaining eigenpair existence, nonnegative subeigenvector extraction, source irreducibility-to-positivity transfers under supplied nonzero nonnegative eigenpairs, Mathlib `spectralRadius` wrappers, `sInf = rho`, `IsLeast` wrappers, and the Problem 7.10(e) product/transpose spectral-radius invariances are closed.  Full source closure still needs a Perron-Frobenius theorem producing the required positive real eigenpair from irreducibility and a compatible common Bauer scaling at the source spectral-radius value. |

### Verification and hygiene

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after the Lean edits.
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3024` jobs.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after rebuilding the Chapter 7 target.
- `timeout 600s lake build` passed with `3506` jobs and only pre-existing QR/Givens/FastMatMul linter warnings.
- Focused implementation/lookup scans over `HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no Lean `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, `WAIT-SPLIT1`, `placeholder`, `by sorry`, or `False.elim` matches.
- Current-branch/Mathlib PF search over `LeanFpAnalysis`, `docs`, `examples`, and `.lake/packages/mathlib/Mathlib` found no theorem upgrading `Matrix.IsIrreducible` for a nonnegative matrix to existence of a positive real Perron eigenvector; the available repository declarations require that eigenvector as input.
- Source re-audit re-read Theorem 7.8 and Appendix A Problem 7.10 from `/home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.ch7.pdf` and `1.9780898718027.appa.pdf`, confirming that the new row is exactly the absolute-value subeigenvector intermediate and that the full source theorem still requires positive Perron vectors from irreducibility.
- `#print axioms` for `ch7_abs_complex_eigenvector_subeigenvector_of_nonneg_matrix`, `ch7_exists_spectralRadius_attaining_nonneg_subeigenvector`, `problem7_10a_product_exists_spectralRadius_attaining_nonneg_subeigenvector`, `problem7_10b_abs_product_exists_spectralRadius_attaining_nonneg_subeigenvector`, and `problem7_10e_abs_transpose_product_exists_spectralRadius_attaining_nonneg_subeigenvector` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No orphan typeclass hypotheses, theorem-equivalent assumptions, local axioms, vacuous definitions, `sorry`, or placeholders were introduced.  The new declarations are finite-dimensional norm/sum proofs and source-facing product specializations.

## 2026-06-26 irreducible support-propagation dependency closure

This continuation extracts a reusable Perron-Frobenius route dependency from
the existing supplied-eigenvector positivity proof: for a nonnegative
irreducible matrix, every nonzero nonnegative vector reaches every coordinate
after some positive matrix power.  This is a genuine Mathlib-powered
irreducibility/power proof step.  It still does not prove the source's
Perron-Frobenius eigenvector existence theorem, and it does not prove the
compatible common two-sided op-2 Bauer scaling theorem.

### Quantitative progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 99 | ~1 | Theorem 7.8 / Problem 7.10 full Bauer theorem still needs Perron-Frobenius positive real eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 statement.  The irreducible support-propagation dependency is now closed and reused by the supplied-eigenpair positivity theorem. | Medium |

No Chapter 7 row is left open because of a previous-split dependency.  The
current-branch search again found Mathlib's `Matrix.IsIrreducible` power
reachability API and the repository's supplied-eigenvector positivity wrappers,
but no theorem upgrading irreducibility to existence of a positive real Perron
eigenvector.  The remaining gap is therefore the source-facing
Perron-Frobenius/common-scaling foundation, not a Split 1 integration
discrepancy.

### Latest selected-inventory status

| Source item | Classification | Previous-split dependency | Lean declarations / reason |
|---|---|---|---|
| Problem 7.10(d) / Theorem 7.8 irreducible support propagation used on the PF route | `CLOSED` | No previous-split dependency | Closed by `ch7_irreducible_pow_mulVec_pos_of_nonzero_nonneg`, which proves that if `M` is Mathlib-irreducible and `x >= 0`, `x != 0`, then for every coordinate `i` there is `k > 0` with `0 < (M^k x)_i`.  The existing `ch7_nonneg_irreducible_right_eigenvector_pos` now reuses this lemma before applying the supplied eigenvector equation. |
| Theorem 7.8 / Problem 7.10 full Bauer op-2 theorem | `PROVE-NOW-SPLIT2` remains open under a concrete source-facing foundation gap | No previous-split dependency | Certificate-level Problem 7.10(a)/(b)/(e) algebra, finite complex spectral-radius-attaining eigenpair existence, nonnegative subeigenvector extraction, irreducible support propagation, source irreducibility-to-positivity transfers under supplied nonzero nonnegative eigenpairs, Mathlib `spectralRadius` wrappers, `sInf = rho`, `IsLeast` wrappers, and the Problem 7.10(e) product/transpose spectral-radius invariances are closed.  Full source closure still needs a Perron-Frobenius theorem producing the required positive real eigenpair from irreducibility and a compatible common Bauer scaling at the source spectral-radius value. |

### Verification and hygiene

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after the Lean edits.
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3024` jobs.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after the lookup update.
- `timeout 600s lake build` passed with `3506` jobs and only pre-existing QR/Givens/FastMatMul linter warnings.
- `git diff --check` passed.
- Focused implementation/lookup scan over `HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no Lean `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, `WAIT-SPLIT1`, `placeholder`, `by sorry`, or `False.elim` matches; the only hit was the existing prose word "axioms" in `docs/LIBRARY_LOOKUP.md`.
- Source re-audit re-read Theorem 7.8 and Appendix A Problem 7.10 from `/home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.ch7.pdf` and `1.9780898718027.appa.pdf`, confirming that the source invokes standard Perron-Frobenius positivity for irreducible nonnegative matrices and that this pass closes only a support-propagation dependency, not eigenvector existence.
- Current-branch/Mathlib PF search over `LeanFpAnalysis`, `docs`, `examples`, and relevant Mathlib `LinearAlgebra`, `Analysis`, and `Topology` directories found no theorem deriving a positive real Perron eigenvector from `Matrix.IsIrreducible`.
- `#print axioms` for `ch7_irreducible_pow_mulVec_pos_of_nonzero_nonneg` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No orphan typeclass hypotheses, theorem-equivalent assumptions, local axioms, vacuous definitions, `sorry`, or placeholders were introduced.  The new declaration is a direct consequence of Mathlib irreducible power reachability plus finite-sum positivity, and it is used by the existing supplied-eigenpair positivity theorem.

## 2026-06-26 irreducible finite power-sum dependency closure

This continuation closes two further local dependencies on the
Perron-Frobenius route.  First, powers of a nonnegative finite matrix preserve
nonnegative vectors.  Second, irreducibility supplies a finite set of positive
powers whose matrix-entry sum is strictly positive in every entry, and whose
mulVec action sends every nonzero nonnegative vector to a strictly positive
vector.  These are genuine finite-sum consequences of Mathlib's
`Matrix.isIrreducible_iff_exists_pow_pos`; they are not Perron-Frobenius
existence assumptions and do not weaken the source theorem.

The red-bottleneck protocol remains active for the full source row.  A compact
math-only whole-problem packet was prepared at
`chapter_splitting/proof_packets/ch7_bauer_pf_whole_problem_2026-06-26.tex`.
The attempted `npx @steipete/oracle ... --model gpt-5.5-pro` consultation was
rejected by the approval layer because it would export project-derived content
to an external service.  No Oracle advisory result was received or adopted, and
no workaround was attempted.

### Quantitative progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 99 | ~1 | Theorem 7.8 / Problem 7.10 full Bauer theorem still needs Perron-Frobenius positive real eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 statement.  The finite positive power-sum dependencies are now closed. | Medium |

No Chapter 7 row is left open because of a previous-split dependency.  Current
searches still find no Mathlib/repository theorem deriving the required
positive real Perron eigenpair from irreducibility alone.  The remaining gap is
a source-facing Perron-Frobenius/common-scaling foundation, not a Split 1
integration discrepancy.

### Latest selected-inventory status

| Source item | Classification | Previous-split dependency | Lean declarations / reason |
|---|---|---|---|
| Problem 7.10(d) / Theorem 7.8 nonnegative-power and finite-positive-power-sum dependencies | `CLOSED` | No previous-split dependency | Closed by `ch7_matrix_pow_mulVec_nonneg_of_nonneg`, `ch7_exists_irreducible_pow_sum_pos`, and `ch7_exists_irreducible_pow_sum_mulVec_pos_of_nonzero_nonneg`.  These prove nonnegative-vector preservation by powers, a finite positive matrix polynomial in an irreducible nonnegative matrix, and a finite positive powered-iterate sum for every nonzero nonnegative vector. |
| Theorem 7.8 / Problem 7.10 full Bauer op-2 theorem | `PROVE-NOW-SPLIT2` remains open under a concrete source-facing red bottleneck | No previous-split dependency | Certificate-level Problem 7.10(a)/(b)/(e) algebra, finite complex spectral-radius-attaining eigenpair existence, nonnegative subeigenvector extraction, irreducible support propagation, finite positive power-sum dependencies, source irreducibility-to-positivity transfers under supplied nonzero nonnegative eigenpairs, Mathlib `spectralRadius` wrappers, `sInf = rho`, `IsLeast` wrappers, and the Problem 7.10(e) product/transpose spectral-radius invariances are closed.  Full source closure still needs a Perron-Frobenius theorem producing the required positive real eigenpair from irreducibility and a compatible common Bauer scaling at the source spectral-radius value. |

### Verification and hygiene

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after the Lean edits.
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3024` jobs.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after the lookup update.
- `timeout 600s lake build` passed with `3506` jobs and only pre-existing QR/Givens/FastMatMul linter warnings.
- `git diff --check` passed.
- Focused implementation/lookup scan over `HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no Lean `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, `WAIT-SPLIT1`, `placeholder`, `by sorry`, or `False.elim` matches; the only hit was the existing prose word "axioms" in `docs/LIBRARY_LOOKUP.md`.
- Source re-audit re-read Theorem 7.8 and Appendix A Problem 7.10 from `/home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.ch7.pdf` and `1.9780898718027.appa.pdf`, confirming that the source invokes standard Perron-Frobenius positivity for irreducible nonnegative matrices and that this pass closes only finite power-sum dependencies, not eigenvector existence.
- Current-branch/Mathlib PF search over `LeanFpAnalysis`, `docs`, `examples`, and relevant Mathlib `LinearAlgebra`, `Analysis`, `Topology`, and convex/fixed-point directories found no theorem deriving a positive real Perron eigenvector from `Matrix.IsIrreducible` and no reusable Brouwer/Schauder simplex fixed-point theorem.
- `#print axioms` for `ch7_matrix_pow_mulVec_nonneg_of_nonneg`, `ch7_exists_irreducible_pow_sum_pos`, and `ch7_exists_irreducible_pow_sum_mulVec_pos_of_nonzero_nonneg` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No orphan typeclass hypotheses, theorem-equivalent assumptions, local axioms, vacuous definitions, `sorry`, or placeholders were introduced.

## 2026-06-26 subeigenvector iteration dependency closure

This continuation closes the next local order-theoretic dependency in the
Perron-Frobenius route for Theorem 7.8 / Problem 7.10.  Nonnegative matrix
actions are now proved monotone for componentwise vector order; a
componentwise subeigenvector inequality `lam * x <= A * x` is proved to
iterate through every power `A^k`; and the corresponding finite-sum inequality
is packaged with the already closed irreducible finite positive power-sum
certificate.  These are genuine finite-dimensional order proofs.  They do not
assert the source Perron-Frobenius theorem that irreducibility produces a
positive real Perron eigenpair, and they do not assert the compatible common
two-sided op-2 Bauer scaling theorem.

### Quantitative progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 99 | ~1 | Theorem 7.8 / Problem 7.10 full Bauer theorem still needs Perron-Frobenius positive real eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 statement.  The nonnegative subeigenvector iteration and finite-sum order dependencies are now closed. | Medium |

No Chapter 7 row is left open because of a previous-split dependency.  Current
searches continue to find Mathlib's irreducible power-reachability API and the
repository's supplied-eigenvector Bauer wrappers, but no theorem deriving the
required positive real Perron eigenpair from `Matrix.IsIrreducible`.  The
remaining gap is source-facing Perron-Frobenius/common-scaling infrastructure,
not a Split 1 integration/API discrepancy.

### Latest selected-inventory status

| Source item | Classification | Previous-split dependency | Lean declarations / reason |
|---|---|---|---|
| Problem 7.10(d) / Theorem 7.8 subeigenvector iteration and finite-sum order dependencies | `CLOSED` | No previous-split dependency | Closed by `ch7_matrix_mulVec_mono_of_nonneg`, `ch7_matrix_pow_mulVec_subeigen_le_of_nonneg`, `ch7_pow_sum_mulVec_subeigen_le_of_nonneg`, and `ch7_exists_irreducible_pow_sum_mulVec_pos_and_subeigen_le`.  These prove nonnegative `mulVec` monotonicity, iteration of `lam * x <= A*x` through all powers, summation over finite power sets, and the combined irreducible nonzero nonnegative subeigenvector certificate. |
| Theorem 7.8 / Problem 7.10 full Bauer op-2 theorem | `PROVE-NOW-SPLIT2` remains open under a concrete source-facing red bottleneck | No previous-split dependency | Certificate-level Problem 7.10(a)/(b)/(e) algebra, finite complex spectral-radius-attaining eigenpair existence, nonnegative subeigenvector extraction, subeigenvector power/sum iteration, irreducible support propagation, finite positive power-sum dependencies, source irreducibility-to-positivity transfers under supplied nonzero nonnegative eigenpairs, Mathlib `spectralRadius` wrappers, `sInf = rho`, `IsLeast` wrappers, and the Problem 7.10(e) product/transpose spectral-radius invariances are closed.  Full source closure still needs a Perron-Frobenius theorem producing the required positive real eigenpair from irreducibility and a compatible common Bauer scaling at the source spectral-radius value. |

### Verification and hygiene

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after the Lean edits.
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3024` jobs.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after the lookup update and fresh Chapter 7 rebuild.  One earlier parallel invocation ran before the rebuilt interface was available and was discarded as a stale-artifact check.
- `timeout 600s lake build` passed with `3506` jobs and only pre-existing QR/Givens/FastMatMul linter warnings.
- `git diff --check` passed.
- Focused implementation/lookup scan over `HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no Lean `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, `WAIT-SPLIT1`, `placeholder`, `by sorry`, or `False.elim` matches.
- Source re-audit searched extracted text from `/home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.ch7.pdf` and `1.9780898718027.appa.pdf`.  Theorem 7.8 and Appendix Problem 7.10 still explicitly invoke positive Perron vectors from irreducibility; the new Lean work closes only the order-iteration dependency below that theorem.
- Current-branch/Mathlib searches still find no theorem deriving a positive real Perron eigenpair from `Matrix.IsIrreducible`.
- `#print axioms` for `ch7_matrix_mulVec_mono_of_nonneg`, `ch7_matrix_pow_mulVec_subeigen_le_of_nonneg`, `ch7_pow_sum_mulVec_subeigen_le_of_nonneg`, and `ch7_exists_irreducible_pow_sum_mulVec_pos_and_subeigen_le` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No orphan typeclass hypotheses, theorem-equivalent assumptions, local axioms, vacuous definitions, `sorry`, or placeholders were introduced.

## 2026-06-26 positive subeigenvector upgrade dependency closure

This continuation closes the next dependency below the remaining
Perron-Frobenius gate.  If a nonnegative irreducible matrix has a nonzero
nonnegative subeigenvector `lam*x <= A*x`, then summing the already-proved
finite positive powered iterates produces a strictly positive subeigenvector
with the same subeigenvalue.  The proof is a finite-dimensional order argument:
it propagates the subeigenvector inequality one power step, sums the resulting
inequalities, and uses the finite positive power-sum certificate for strict
positivity.  It does not assert an eigenvector equation or spectral-radius
equality.

### Quantitative progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 99 | ~1 | Theorem 7.8 / Problem 7.10 full Bauer theorem still needs Perron-Frobenius positive real eigenpair existence from irreducibility and compatible common Bauer scaling for the full op-2 statement.  The positive subeigenvector upgrade from a nonzero nonnegative subeigenvector is now closed. | Medium |

No Chapter 7 row is left open because of a previous-split dependency.  Current
searches continue to find Mathlib's irreducible power-reachability API and the
repository's supplied-eigenvector Bauer wrappers, but no theorem deriving the
required positive real Perron eigenpair from `Matrix.IsIrreducible`.  The
remaining gap is source-facing Perron-Frobenius/common-scaling infrastructure,
not a Split 1 integration/API discrepancy.

### Latest selected-inventory status

| Source item | Classification | Previous-split dependency | Lean declarations / reason |
|---|---|---|---|
| Problem 7.10(d) / Theorem 7.8 positive subeigenvector upgrade below PF existence | `CLOSED` | No previous-split dependency | Closed by `ch7_matrix_pow_mulVec_subeigen_step_of_nonneg` and `ch7_exists_positive_subeigenvector_of_irreducible_nonzero_nonneg_subeigen`.  These prove one-step propagation from `lam*x <= A*x` to `lam*(A^k*x) <= A^(k+1)*x`, then use the irreducible finite powered-iterate sum to construct `y > 0` with `lam*y <= A*y`. |
| Theorem 7.8 / Problem 7.10 full Bauer op-2 theorem | `PROVE-NOW-SPLIT2` remains open under a concrete source-facing red bottleneck | No previous-split dependency | Certificate-level Problem 7.10(a)/(b)/(e) algebra, finite complex spectral-radius-attaining eigenpair existence, nonnegative subeigenvector extraction, positive subeigenvector upgrade, subeigenvector power/sum iteration, irreducible support propagation, finite positive power-sum dependencies, source irreducibility-to-positivity transfers under supplied nonzero nonnegative eigenpairs, Mathlib `spectralRadius` wrappers, `sInf = rho`, `IsLeast` wrappers, and the Problem 7.10(e) product/transpose spectral-radius invariances are closed.  Full source closure still needs a Perron-Frobenius theorem producing the required positive real eigenpair from irreducibility and a compatible common Bauer scaling at the source spectral-radius value. |

### Verification and hygiene

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after the Lean edits.
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3024` jobs.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after the lookup update and fresh Chapter 7 rebuild.
- `timeout 600s lake build` passed with `3506` jobs and only pre-existing QR/Givens/FastMatMul linter warnings.
- `git diff --check` passed.
- Focused implementation/lookup scan over `HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no Lean `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, `WAIT-SPLIT1`, `placeholder`, `by sorry`, or `False.elim` matches.
- Source re-audit re-extracted `/home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.ch7.pdf` and `1.9780898718027.appa.pdf`; Theorem 7.8 and Appendix Problem 7.10 still invoke positive Perron vectors from irreducibility, so this pass closes only the positive-subeigenvector dependency below PF eigenpair existence.
- `#print axioms` for `ch7_matrix_pow_mulVec_subeigen_step_of_nonneg` and `ch7_exists_positive_subeigenvector_of_irreducible_nonzero_nonneg_subeigen` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No orphan typeclass hypotheses, theorem-equivalent assumptions, local axioms, vacuous definitions, `sorry`, or placeholders were introduced.

## 2026-06-26 positive spectral-radius subeigenvector dependency closure

This continuation combines the finite complex spectral-radius-attaining
eigenpair, the absolute-value nonnegative subeigenvector bridge, and the
irreducible positive-subeigenvector upgrade.  For a nonnegative irreducible
matrix, the spectral-radius-attaining complex eigenpair now supplies a
nonzero nonnegative subeigenvector and a strictly positive subeigenvector at
the same scalar `‖mu‖`.  Source-product wrappers expose this for `BC`,
`|A||A⁻¹|`, and `|A|ᵀ|A⁻¹|ᵀ`.  This still does not assert the real Perron
eigenvector equation or the compatible common op-2 Bauer scaling theorem.

### Quantitative progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 99 | ~1 | Theorem 7.8 / Problem 7.10 full Bauer theorem still needs Perron-Frobenius positive real eigenpair equality from irreducibility and compatible common Bauer scaling for the full op-2 statement.  Positive spectral-radius subeigenvectors for the source products are now closed. | Medium |

No Chapter 7 row is left open because of a previous-split dependency.  The
remaining gap is source-facing Perron-Frobenius/common-scaling infrastructure,
not a Split 1 integration/API discrepancy.

### Latest selected-inventory status

| Source item | Classification | Previous-split dependency | Lean declarations / reason |
|---|---|---|---|
| Problem 7.10 / Theorem 7.8 positive spectral-radius subeigenvector intermediates | `CLOSED` | No previous-split dependency | Closed by `ch7_exists_spectralRadius_attaining_positive_subeigenvector`, `problem7_10a_product_exists_spectralRadius_attaining_positive_subeigenvector`, `problem7_10b_abs_product_exists_spectralRadius_attaining_positive_subeigenvector`, and `problem7_10e_abs_transpose_product_exists_spectralRadius_attaining_positive_subeigenvector`.  These combine spectral-radius-attaining complex eigenpairs, componentwise absolute values, and irreducible finite powered-iterate sums to produce strictly positive subeigenvectors at the attained spectral-radius scalar. |
| Theorem 7.8 / Problem 7.10 full Bauer op-2 theorem | `PROVE-NOW-SPLIT2` remains open under a concrete source-facing red bottleneck | No previous-split dependency | The spectral-radius-attaining nonnegative and positive subeigenvector stages are closed for the source products, along with the existing certificate-level Bauer algebra and `sInf`/`IsLeast` wrappers.  Full source closure still needs the Perron-Frobenius upgrade from positive subeigenvector to a positive real eigenvector/equality at the source spectral-radius value and compatible common Bauer scaling. |

### Verification and hygiene

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after the Lean edits.
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3024` jobs.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after the lookup update and fresh Chapter 7 rebuild.
- `timeout 600s lake build` passed with `3506` jobs and only pre-existing QR/Givens/FastMatMul linter warnings.
- `git diff --check` passed.
- Focused implementation/lookup scan over `HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no Lean `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, `WAIT-SPLIT1`, `placeholder`, `by sorry`, or `False.elim` matches.
- Source re-audit re-extracted `/home/mymel/flare-bundle/higham-split/sources/chapter-pdfs/1.9780898718027.ch7.pdf` and `1.9780898718027.appa.pdf`; Theorem 7.8 and Appendix Problem 7.10 still require positive Perron vectors/eigenvector equations from irreducibility, so this pass closes only the positive spectral-radius subeigenvector stage below PF eigenpair equality.
- `#print axioms` for `ch7_exists_spectralRadius_attaining_positive_subeigenvector`, `problem7_10a_product_exists_spectralRadius_attaining_positive_subeigenvector`, `problem7_10b_abs_product_exists_spectralRadius_attaining_positive_subeigenvector`, and `problem7_10e_abs_transpose_product_exists_spectralRadius_attaining_positive_subeigenvector` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No orphan typeclass hypotheses, theorem-equivalent assumptions, local axioms, vacuous definitions, `sorry`, or placeholders were introduced.

## 2026-06-26 Bauer lower-bound closure from positive subeigenvectors

This continuation proves the Bauer lower-bound half that is already supported
by the positive spectral-radius subeigenvectors.  A positive subeigenvector
`rho*x <= A*x` now gives `rho <= ||A||_infty`, and the Bauer two-sided scaling
algebra transports this inequality through every positive reciprocal scaling.
Consequently, the Problem 7.10(a) product, Problem 7.10(b) absolute
condition-product, and Problem 7.10(e) one-norm transpose branches now expose
source-facing `rho <= sInf` lower bounds directly from irreducibility and the
spectral-radius-attaining positive subeigenvector construction.  This is a
genuine proof of the universal lower-bound side, not a Perron-vector
assumption.  It still does not provide the canonical attaining scaling or the
real eigenvector equation `A*x = rho*x`.

### Quantitative progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 99 | ~1 | Theorem 7.8 / Problem 7.10 full Bauer theorem still needs Perron-Frobenius positive real eigenpair equality from irreducibility and compatible common Bauer scaling for the full op-2 statement.  The universal lower-bound half from positive spectral-radius subeigenvectors is now closed for the product, `kappa_infty`, and transpose `kappa_1` branches. | Medium |

No Chapter 7 row is left open because of a previous-split dependency.  The
remaining gap is source-facing Perron-Frobenius/common-scaling infrastructure,
not a Split 1 integration/API discrepancy.

### Latest selected-inventory status

| Source item | Classification | Previous-split dependency | Lean declarations / reason |
|---|---|---|---|
| Problem 7.10(a)/(b)/(e) Bauer lower-bound half from spectral-radius positive subeigenvectors | `CLOSED` | No previous-split dependency | Closed by `ch7_infNormVec_mono_of_nonneg_le`, `ch7_infNorm_ge_of_positive_right_subeigenvector`, `ch7_bauer_scaled_product_mulVec_eq`, `ch7_bauer_scaled_product_subeigenvector`, `problem7_10a_scaled_infCond_ge_perron_of_positive_subeigenvector`, `problem7_10a_scaledInfCondSet_sInf_ge_perron_of_positive_subeigenvector`, `problem7_10a_irreducible_product_scaledInfCondSet_sInf_ge_spectralRadius`, `problem7_10b_scaled_infKappa_ge_perron_of_abs_inverse_positive_subeigenvector`, `problem7_10b_scaledInfKappaSet_sInf_ge_perron_of_abs_inverse_positive_subeigenvector`, `problem7_10b_irreducible_abs_product_scaledInfKappaSet_sInf_ge_spectralRadius`, `problem7_10e_scaled_oneCond_ge_perron_of_transpose_positive_subeigenvector`, `problem7_10e_scaled_oneKappa_ge_perron_of_abs_inverse_transpose_positive_subeigenvector`, `problem7_10e_scaledOneKappaSet_sInf_ge_perron_of_abs_inverse_transpose_positive_subeigenvector`, and `problem7_10e_irreducible_abs_transpose_product_scaledOneKappaSet_sInf_ge_spectralRadius`.  These prove the universal lower-bound side from actual positive subeigenvectors supplied by irreducibility and spectral-radius-attaining complex eigenpairs. |
| Theorem 7.8 / Problem 7.10 full Bauer op-2 theorem | `PROVE-NOW-SPLIT2` remains open under a concrete source-facing red bottleneck | No previous-split dependency | The spectral-radius-attaining nonnegative/positive subeigenvector stages and the universal `rho <= sInf` lower-bound halves are closed for the source products.  Full source closure still needs the Perron-Frobenius upgrade from positive subeigenvector to a positive real eigenvector/equality at the source spectral-radius value, canonical attaining scalings, and compatible common Bauer scaling for the op-2 conclusion. |

### Verification and hygiene

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after the Lean edits.
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3024` jobs.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after rebuilding the Chapter 7 target.  The first lookup attempt saw stale `.olean` state while the target build was still in progress; the rerun passed.
- `timeout 600s lake build` passed with `3506` jobs and only the pre-existing QR/Givens/FastMatMul linter warnings outside Chapter 7.
- `git diff --check` passed.
- Focused implementation/lookup scan over `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `by sorry`, `False.elim`, `placeholder`, `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, or `WAIT-SPLIT1` matches.  A broader scan including this report matched only historical report prose and command strings.
- Broad Lean-file scan over `LeanFpAnalysis` and `examples` found only pre-existing ordinary `False.elim` contradiction proofs and the pre-existing `Norms.lean` doc phrase "admit an actual"; it found no implementation placeholder introduced by this pass.
- Source re-audit re-extracted Chapter 7 Theorem 7.8 and Appendix Problem 7.10.  The new declarations match the universal lower-bound inequality in Appendix (A.5); the attaining equality/minimum construction in (A.6)--(A.8) and the op-2 conclusion remain open as recorded above.
- `#print axioms` for `ch7_infNorm_ge_of_positive_right_subeigenvector`, `ch7_bauer_scaled_product_subeigenvector`, `problem7_10a_irreducible_product_scaledInfCondSet_sInf_ge_spectralRadius`, `problem7_10b_irreducible_abs_product_scaledInfKappaSet_sInf_ge_spectralRadius`, and `problem7_10e_irreducible_abs_transpose_product_scaledOneKappaSet_sInf_ge_spectralRadius` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No orphan typeclass hypotheses, theorem-equivalent assumptions, local axioms, vacuous definitions, `sorry`, or placeholders were introduced by these declarations.

## 2026-06-26 Strict Collatz propagation step for the Bauer PF route

This continuation closes the local strict-defect propagation dependency below
the remaining Perron-Frobenius equality step.  If a nonnegative irreducible
matrix has a strictly positive subeigenvector `lam*y <= A*y` and the defect is
strict in some coordinate, a finite positive power-sum of the defect produces a
new strictly positive vector `v` and a positive `eps` with
`(lam + eps)*v <= A*v`.  The companion dichotomy states that every strictly
positive subeigenvector is either already a right eigenvector or admits such a
strictly stronger positive subeigenvalue certificate.

This is genuine proof work on the Collatz-Wielandt/Perron-Frobenius route, not
a source-facing assumption.  It does not by itself prove that the
spectral-radius-attaining positive subeigenvector is an eigenvector: the
remaining missing theorem is the spectral-radius/no-stronger-subeigenvalue
contradiction, equivalently the Collatz-Wielandt/Perron-Frobenius lower-bound
step for positive subeigenvalues, followed by the compatible common Bauer
scaling needed for the full op-2 statement.

### Quantitative progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 99 | 99 | 99 | 100 | 99 | ~1 | Theorem 7.8 / Problem 7.10 full Bauer theorem still needs the spectral-radius lower/no-stronger-positive-subeigenvalue theorem that turns the positive spectral-radius subeigenvector into a positive real Perron eigenvector, plus canonical attaining scalings and compatible common op-2 scaling.  The new strict-defect propagation and eigen-or-stronger dichotomy are closed. | Medium |

No Chapter 7 row is left open because of a previous-split dependency.  The
remaining gap is current Split 2 Perron-Frobenius/common-scaling proof/API work,
not a Split 1 integration/API discrepancy.

### Latest selected-inventory status

| Source item | Classification | Previous-split dependency | Lean declarations / reason |
|---|---|---|---|
| Problem 7.10(a)/(b)/(d)/(e) Perron-Frobenius strict-defect propagation dependency | `CLOSED` | No previous-split dependency | Closed by `ch7_exists_stronger_positive_subeigenvector_of_strict_subeigen` and `ch7_positive_subeigenvector_eigen_or_exists_stronger`.  These prove that strict positive subeigenvector defect propagates through irreducible finite power sums to a strictly larger positive subeigenvalue, and package the resulting eigenvector-or-stronger dichotomy. |
| Problem 7.10(a)/(b)/(e) Bauer lower-bound half from spectral-radius positive subeigenvectors | `CLOSED` | No previous-split dependency | Remains closed by the lower-bound declarations listed in the previous section; Appendix (A.5) is matched by the `rho <= sInf` wrappers for the product, `kappa_infty`, and transpose `kappa_1` branches. |
| Theorem 7.8 / Problem 7.10 full Bauer op-2 theorem | `PROVE-NOW-SPLIT2` remains open under a concrete source-facing red bottleneck | No previous-split dependency | Source re-audit of Chapter 7 and Appendix A.10 confirms that equality in (A.6)--(A.8) still requires a positive Perron vector/eigenvector equation from irreducibility and then compatible common Bauer scaling for the op-2 conclusion.  Current repo/Mathlib searches expose eigenpair attainment and norm-existence/spectral-radius wrappers, but not a theorem proving the needed no-stronger-positive-subeigenvalue contradiction from `Matrix.IsIrreducible`. |

### Verification and hygiene

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after the Lean edits.
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3024` jobs.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after the lookup update and fresh Chapter 7 rebuild.
- `timeout 600s lake build` passed with `3506` jobs and only the pre-existing QR/Givens/FastMatMul linter warnings outside Chapter 7.
- `git diff --check` passed.
- Focused implementation/lookup scan over `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `by sorry`, `False.elim`, `placeholder`, `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, or `WAIT-SPLIT1` matches.
- Source re-audit re-extracted Chapter 7 Theorem 7.8 and Appendix Problem 7.10.  The new declarations are below the Perron-vector equality step used in Appendix (A.6)--(A.8); they do not weaken or replace the source statement.
- `#print axioms` for `ch7_exists_stronger_positive_subeigenvector_of_strict_subeigen` and `ch7_positive_subeigenvector_eigen_or_exists_stronger` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No orphan typeclass hypotheses, theorem-equivalent assumptions, local axioms, vacuous definitions, `sorry`, or placeholders were introduced by these declarations.

## 2026-06-26 Perron eigenvector and Bauer `sInf` equality closure

This continuation closes the Perron-Frobenius equality gate that was open in
the previous strict-Collatz section.  A positive right subeigenvector at scalar
`lam` now gives a finite-matrix Gelfand/spectral-radius lower bound
`lam <= rho(A)`.  Applied to the spectral-radius-attaining positive
subeigenvectors, this rules out the strictly stronger positive subeigenvalue
branch and produces actual positive real Perron eigenvectors.

The Problem 7.10(a), 7.10(b), and 7.10(e) Bauer branches then reuse the
existing Bauer scaling algebra to prove the exact `sInf = spectralRadius`
wrappers for the product, `kappa_infty`, and transpose `kappa_1` value sets.
This closes the Appendix (A.6)--(A.8) Perron-vector equality/minimum gate for
Theorem 7.8 and the one-norm/infinity-norm branches.  A source re-audit shows
that Theorem 7.8 itself is the infinity-norm equality
`min_{D1,D2} kappa_infty(D1 A D2) = rho(|A||A^{-1}|)`, not the later 2-norm
statement.  The remaining selected Bauer source row is Problem 7.10(e)'s
2-norm infimum upper bound.

This pass also adds the product-bound op-2 bridge
`problem7_10e_scaled_op2Kappa_le_of_one_inf_product_bound` and its global
`sInf` wrapper
`problem7_10e_twoSidedScaledOp2Kappa_sInf_le_of_one_inf_product_bound`.
These prove that one admissible scaling with
`kappa_1(D1AD2) * kappa_infty(D1AD2) <= rho^2` suffices for the exact
operator-2 bound.  The remaining source-facing work is therefore narrower than
the previous ledger stated: prove or expose such a product-bound/common
two-sided scaling at `rho(|A||A^{-1}|)`.

### Quantitative progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 100 | 99 | 99 | 100 | 96 | ~1 | Theorem 7.8 and the Problem 7.10(a)/(b)/(d)/(e) one-/infinity-norm equality branches are closed.  Problem 7.10(e)'s 2-norm infimum upper bound still needs a compatible product-bound/common two-sided scaling. | Medium |

No Chapter 7 row is left open because of a previous-split dependency.  The
remaining gap is current Split 2 Bauer common-scaling proof work, not a Split 1
integration/API discrepancy.

### Latest selected-inventory status

| Source item | Classification | Previous-split dependency | Lean declarations / reason |
|---|---|---|---|
| Problem 7.10(a)/(b)/(d)/(e) positive Perron eigenvector from irreducible nonnegative product | `CLOSED` | No previous-split dependency | Closed by `ch7_matrix_spectralRadius_ge_of_positive_right_subeigenvector`, `ch7_toLin_spectralRadius_ge_of_positive_right_subeigenvector`, and `ch7_exists_spectralRadius_attaining_positive_eigenvector`.  These combine the existing strict-Collatz dichotomy with Mathlib's finite-dimensional Gelfand spectral-radius formula, not a Perron-vector assumption. |
| Problem 7.10(a) product `sInf = rho(BC)` equality branch | `CLOSED` | No previous-split dependency | Closed by `problem7_10a_product_exists_spectralRadius_attaining_positive_eigenvector` and `problem7_10a_irreducible_products_scaledInfCondSet_sInf_eq_spectralRadius`, reusing the existing nonzero-nonnegative-eigenvector Bauer equality wrapper. |
| Theorem 7.8 / Problem 7.10(b,d) absolute-product `kappa_infty` equality `min kappa_infty(D1 A D2) = rho(|A||A^{-1}|)` | `CLOSED` | No previous-split dependency | Closed by `problem7_10b_abs_product_exists_spectralRadius_attaining_positive_eigenvector` and `problem7_10b_irreducible_products_scaledInfKappaSet_sInf_eq_spectralRadius`, reusing the existing `kappa_infty` Bauer equality wrapper.  Source re-audit confirms this is Theorem 7.8's norm, not an op-2 theorem. |
| Problem 7.10(e) transpose absolute-product `kappa_1` `sInf = rho(|A|^T |A^{-1}|^T)` branch | `CLOSED` | No previous-split dependency | Closed by `problem7_10e_abs_transpose_product_exists_spectralRadius_attaining_positive_eigenvector` and `problem7_10e_irreducible_products_scaledOneKappaSet_sInf_eq_spectralRadius`, reusing the transpose-product one-norm Bauer equality wrapper and the irreducible-transpose adapter. |
| Problem 7.10(e) 2-norm infimum upper bound `inf kappa_2(D1 A D2) <= rho(|A||A^{-1}|)` | `PROVE-NOW-SPLIT2` remains open | No previous-split dependency | The PF eigenvector/equality gate is closed.  The new product-bound bridge `problem7_10e_twoSidedScaledOp2Kappa_sInf_le_of_one_inf_product_bound` reduces the remaining source row to proving one admissible scaling with `kappa_1 * kappa_infty <= rho^2`; no current repository/Mathlib search exposed that common-scaling theorem. |

### Verification and hygiene

- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3025` jobs after the product-bound Lean and lookup updates.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after adding the product-bound lookup checks.
- `timeout 600s lake build` passed with `3507` jobs and only the pre-existing QR/Givens/FastMatMul linter warnings outside Chapter 7.
- Source re-audit re-extracted the Chapter 7 PDF and Appendix A PDF.  The new declarations match the positive Perron-vector/equality steps in Appendix Problem 7.10(A.6)--(A.8); Theorem 7.8 is the now-closed infinity-norm equality, and Problem 7.10(e)'s op-2 product-bound/common-scaling step remains the open source row.
- Focused implementation/lookup scan over `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `by sorry`, `False.elim`, `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, `WAIT-SPLIT1`, or `placeholder` matches.  Scratch/probe files `ScratchCh7.lean` and `AxiomCheckCh7.lean` are absent.
- `git diff --check` passed after the final report/log updates.
- `#print axioms` for `ch7_matrix_spectralRadius_ge_of_positive_right_subeigenvector`, `ch7_toLin_spectralRadius_ge_of_positive_right_subeigenvector`, `ch7_exists_spectralRadius_attaining_positive_eigenvector`, `problem7_10a_product_exists_spectralRadius_attaining_positive_eigenvector`, `problem7_10a_irreducible_products_scaledInfCondSet_sInf_eq_spectralRadius`, `problem7_10b_abs_product_exists_spectralRadius_attaining_positive_eigenvector`, `problem7_10b_irreducible_products_scaledInfKappaSet_sInf_eq_spectralRadius`, `problem7_10e_abs_transpose_product_exists_spectralRadius_attaining_positive_eigenvector`, and `problem7_10e_irreducible_products_scaledOneKappaSet_sInf_eq_spectralRadius` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `#print axioms` for `problem7_10e_scaled_op2Kappa_le_of_one_inf_product_bound` and `problem7_10e_twoSidedScaledOp2Kappa_sInf_le_of_one_inf_product_bound` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- No orphan typeclass hypotheses, theorem-equivalent assumptions, local axioms, vacuous definitions, `sorry`, or unproved placeholders were introduced by these declarations.
- No external proof source or GPT-5.5 Pro Oracle result was used in this pass; the proof route uses existing repository declarations plus Mathlib's finite-dimensional spectral-radius/Gelfand infrastructure.

## 2026-06-26 Bauer op-2 compatible Schur scaling closure

This continuation closes the remaining Problem 7.10(e) two-norm Bauer upper
bound that the previous section reduced to a compatible common-scaling
obligation.  The proof does not use the earlier insufficient strategy of
combining independently optimal one- and infinity-norm scalings.  Instead it
constructs a single two-sided scaling from compatible right and left Perron
data:

- right data for `B = |A|`, `C = |A^{-1}|`: `C*x = y` and `B*y = rho*x`;
- left data from the transpose product: `C^T*b = a` and `B^T*a = rho*b`;
- scaling factors `d1_i = a_i / sqrt(a_i*x_i)` and
  `d2_j = y_j / sqrt(y_j*b_j)`, with reciprocal partners.

A finite Schur-test proof gives `||D1 B D2||_2 <= rho` and
`||D2^{-1} C D1^{-1}||_2 <= 1`, so the exact operator-2 condition product is
at most `rho`.  The source irreducible-product wrapper obtains the required
right Perron vector from `|A||A^{-1}|`, the left Perron vector from
`|A|^T|A^{-1}|^T`, and identifies their scalars using the already proved
`rho(AB)=rho(BA)` and transpose spectral-radius equalities.  This closes the
Problem 7.10(e) op-2 infimum upper-bound row as current Split 2 proof work,
with no previous-split blocker.

### Quantitative progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 100 | 100 | 100 for Theorem 7.8 / Problem 7.10 Bauer rows; broader Chapter 7 remains 99 because finite-real Theorem 7.5 source-min extraction is still tracked separately | 100 | 98 | ~1 broader Chapter 7 row | Problem 7.10(e)'s two-norm Bauer upper bound is closed.  The remaining broader Chapter 7 caveat is the finite-real Theorem 7.5 actual source `min` extraction over general `p`, whose pairwise/`sInf`/conditional wrappers and compact-core dependencies are already recorded above. | Medium-high |

No Chapter 7 Bauer row is left open because of a previous-split dependency.
The new proofs are current Split 2 local/Mathlib adapter work over already
integrated norm, spectral-radius, and Perron-Frobenius infrastructure.

### Latest selected-inventory status

| Source item | Classification | Previous-split dependency | Lean declarations / reason |
|---|---|---|---|
| Problem 7.10(e) Schur-test infrastructure for compatible left/right Bauer scaling | `CLOSED` | No previous-split dependency | Closed by `ch7_weighted_row_cauchy_sum_sq`, `ch7_vecNorm2Sq_matMulVec_le_of_schur_bounds`, `ch7_opNorm2Le_of_schur_bounds`, `ch7_bauer_left_scaled_opNorm2Le_of_left_right_vectors`, and `ch7_bauer_right_scaled_opNorm2Le_of_left_right_vectors`.  These are genuine 2-norm estimates for nonnegative matrices with positive row/column weights, not assumptions. |
| Problem 7.10(e) fixed compatible scaling `kappa_2(D1 A D2) <= rho` | `CLOSED` | No previous-split dependency | Closed by `problem7_10e_scaled_op2Kappa_le_perron_of_abs_left_right_vectors`.  The theorem proves the exact operator-2 condition product bound for the reciprocal scaling built from supplied positive right and left Perron-vector data. |
| Problem 7.10(e) global infimum upper bound from compatible left/right data | `CLOSED` | No previous-split dependency | Closed by `problem7_10e_twoSidedScaledOp2Kappa_sInf_le_perron_of_abs_left_right_vectors`, using the existing positive reciprocal two-sided value set and `csInf_le`. |
| Problem 7.10(e) source irreducible-product op-2 upper bound `inf kappa_2(D1 A D2) <= rho(|A||A^{-1}|)` | `CLOSED` | No previous-split dependency | Closed by `problem7_10e_irreducible_products_twoSidedScaledOp2KappaSet_sInf_le_spectralRadius`.  It reuses `problem7_10b_abs_product_exists_spectralRadius_attaining_positive_eigenvector`, `problem7_10e_abs_transpose_product_exists_spectralRadius_attaining_positive_eigenvector`, `problem7_10d_abs_inverse_Cx_pos_of_irreducible_products`, `problem7_10d_Cx_pos_of_irreducible_BC_CB`, and `problem7_10e_abs_transpose_product_toLin_spectralRadius_eq_abs_product` to obtain and align the required positive right and left vector certificates. |
| Theorem 7.8 / Problem 7.10(a,b,d,e) Bauer equality and upper-bound package | `CLOSED` for the repository's selected `sInf`/least-value model | No previous-split dependency | Theorem 7.8's infinity-norm equality remains closed by the declarations in the previous Perron-eigenvector section.  Problem 7.10(e)'s one-norm branch and two-norm upper-bound branch are now both closed; older rows saying the op-2 row still awaited compatible common scaling are superseded by this section. |
| Theorem 7.5 finite-real general `p` actual source `min` over right/left scalings | `PROVE-NOW-SPLIT2` remains open in the broader Chapter 7 ledger | No previous-split dependency | This pass did not alter the existing Theorem 7.5 finite-real minimizer-extraction caveat.  Pairwise, `sInf`, conditional `IsLeast`, one-sided-inverse, normalized-certificate, and reciprocal compact-core/coercivity layers remain closed; the report continues to track the remaining finite-real `Lp` continuity/closed-sublevel/`exists_isLeast` extraction separately from the now-closed Bauer row. |

### Verification and hygiene

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after the Schur/Perron-vector Lean edits.
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3025` jobs after adding the source irreducible-product wrapper and lookup updates.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after adding lookup checks for the new declarations.
- Focused implementation/example placeholder scan over `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` and `examples/LibraryLookup.lean` found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `by sorry`, `False.elim`, `placeholder`, `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, or `WAIT-SPLIT1` matches.
- Focused implementation/lookup scan over `HighamChapter7.lean`, `docs/LIBRARY_LOOKUP.md`, and `examples/LibraryLookup.lean` found only the pre-existing lookup prose phrase "relative-error axioms" in the `FPModel` description, not a Lean declaration or placeholder.  Report-inclusive scans matched historical command strings and axiom-summary prose only.
- `#print axioms` for `ch7_opNorm2Le_of_schur_bounds`, `ch7_bauer_left_scaled_opNorm2Le_of_left_right_vectors`, `ch7_bauer_right_scaled_opNorm2Le_of_left_right_vectors`, `problem7_10e_scaled_op2Kappa_le_perron_of_abs_left_right_vectors`, `problem7_10e_twoSidedScaledOp2Kappa_sInf_le_perron_of_abs_left_right_vectors`, and `problem7_10e_irreducible_products_twoSidedScaledOp2KappaSet_sInf_le_spectralRadius` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `timeout 600s lake build` passed with `3507` jobs and only pre-existing QR/Givens/FastMatMul linter warnings outside Chapter 7.
- Post-implementation source re-audit re-extracted the local Chapter 7 and Appendix A PDFs with `pdftotext -layout`.  Chapter Problem 7.10(e) asks for the 1- and 2-norm consequences, and Appendix lines around solution 7.10(e) derive the one-norm branch by transpose/spectral-radius identities and the two-norm upper bound from `||A||_2 <= sqrt(||A||_1 ||A||_infty)`.  The new compatible Schur scaling supplies the required op-2 `sInf` upper bound at `rho(|A||A^{-1}|)` without weakening the source statement.

## 2026-06-26 Problem 7.5 SVD perturbation closure and final Split 2 re-audit

This section supersedes older rows that still listed Problem 7.5, finite-real
Theorem 7.5 minimizer extraction, or Bauer common-scaling obligations as open.
The current branch contains the necessary Split 1/repository interfaces, and no
selected Chapter 7 Split 2 row remains open because of a previous-split
dependency.

Problem 7.5 is now formalized in the repository's complex SVD-coordinate model.
The source statement is real, with `A = U Sigma V^T`, `P_k = U_k U_k^T`,
`Ax=b`, `A(x+Delta x)=b+Delta b`, and
`||Delta x||_2 / ||x||_2 <=
  (sigma_{n+1-k} ||b||_2) / (sigma_n ||P_k b||_2)
    * ||Delta b||_2 / ||b||_2`.
The Lean statement proves the same singular-value proof pattern over finite
complex Euclidean spaces.  The projection `||P_k b||_2` is represented as the
tail coordinate energy of `b` in an orthonormal basis containing the left
singular vectors.  The source-index wrapper maps `sigma_n` to Lean index
`n - 1` and `sigma_{n+1-k}` to Lean index `n - k`.

### Quantitative progress snapshot

| Chapter | Mode | Inventory % | Statement % | Dependency % | Proof % | Verification/report % | Estimated overall % | Open selected rows | Main blocker | Confidence |
|---|---|---:|---:|---:|---:|---:|---:|---:|---|---|
| 7 | proof-completion | 100 | 100 | 100 | 100 | 100 | 100 | 0 | None for selected Split 2 source rows.  Remaining non-formalized material is empirical/expository or outside the selected formalization policy. | High |

### Final selected-inventory status

| Source item | Classification | Previous-split dependency | Lean declarations / reason |
|---|---|---|---|
| Problem 7.5 SVD-projected perturbation bound | `CLOSED` | Yes, direct previous-split/repository dependency, already integrated and available | Closed by `problem7_5_projection_norm_le_sigmaTail_mul_norm`, `problem7_5_sigmaMin_mul_norm_le_image_norm`, `problem7_5_norm_le_inv_sigmaMin_mul_image_norm`, `problem7_5_svd_projection_relative_error_bound`, and `problem7_5_svd_projection_relative_error_bound_source_indices`.  The proof uses the available repository SVD-coordinate API, `complexMatrixSingularValue`, `complexMatrixLeftSingularVector`, `complexMatrixGramEigenvectorBasis`, and `complexMatrixSVDFinDiagonalCoordinateMatrix_mulVec_repr`; these are current-branch declarations, not unproved hypotheses. |
| Theorem 7.5 finite-real `p` minimizer source rows `(7.18)` and `(7.19)` | `CLOSED` | Yes, direct previous-split/repository dependency, already integrated and available | Closed by the existing source-min wrappers `theorem7_5_lp_column_equilibration_exists_min_right_scalings_of_rect_left_inverse`, `theorem7_5_lp_dual_row_equilibration_exists_min_left_scalings_of_rect_right_inverse`, `theorem7_5_lp_column_equilibration_exists_penrose_min_of_matrix_rank_eq_width`, and `theorem7_5_lp_dual_row_equilibration_exists_penrose_min_of_matrix_rank_eq_height`, together with the continuity/compact-sublevel and reciprocal scaling infrastructure recorded above.  Older rows saying this was open are stale. |
| Theorem 7.8 and Appendix Problem 7.10(a,b,d,e) Bauer equalities and norm consequences | `CLOSED` | No previous-split dependency | Closed by the Perron-Frobenius/equality declarations recorded above, including `problem7_10a_irreducible_products_scaledInfCondSet_sInf_eq_spectralRadius`, `problem7_10b_irreducible_products_scaledInfKappaSet_sInf_eq_spectralRadius`, `problem7_10e_irreducible_products_scaledOneKappaSet_sInf_eq_spectralRadius`, and `problem7_10e_irreducible_products_twoSidedScaledOp2KappaSet_sInf_le_spectralRadius`. |
| Problem 7.15 Hadamard-product lower bound and diagonal equality | `CLOSED` | No previous-split dependency | Closed by `problem7_15_twoSidedScale_hadamard_transpose_inverse_invariant`, `problem7_15_hornJohnson_hadamard_opNorm2Le`, `problem7_15_twoSidedScaledOp2Kappa_sInf_ge_hadamard_op2`, and `problem7_15_diagonal_twoSidedScaledOp2Kappa_sInf_eq_one`. |
| Chapter 7 componentwise/mixed condition-number rows, including Problems 7.6, 7.9, 7.11, and associated equations | `CLOSED` | No unresolved previous-split dependency | Already closed in the current branch by the componentwise, Skeel, and perturbation-bound declarations listed earlier in this report and exported through `docs/LIBRARY_LOOKUP.md` / `examples/LibraryLookup.lean`. |
| Qualitative interpretation prose following Problem 7.5 and fixed numerical/empirical examples | `SKIP` | No previous-split dependency | Expository or empirical material; the theorem-equivalent mathematical inequality is formalized. |

### Previous-split dependency re-audit

| Source item | Direct/indirect dependency | Previous split | Integrated declaration/interface reused | Thin wrapper added or follow-up |
|---|---|---|---|---|
| Problem 7.5 SVD bound | Direct | Split 1 / repository SVD-norm infrastructure | `complexMatrixSingularValue`, `complexMatrixLeftSingularVector`, `complexMatrixGramEigenvectorBasis`, `complexMatrixSVDFinDiagonalCoordinateMatrix_mulVec_repr`, and finite-dimensional Euclidean norm lemmas | Added the Chapter 7 wrappers listed above.  No integration/API discrepancy remains. |
| Theorem 7.5 source-min extraction | Direct | Split 1 / repository norm and real-to-complex infrastructure | `continuous_complexMatrixLpNorm`, `continuous_complexMatrixLpNormOfReal`, reciprocal scaling and Moore-Penrose/rank interfaces already present in the branch | Existing source-min wrappers close the rows; no follow-up remains. |

### Verification and hygiene

- `lake env lean LeanFpAnalysis/FP/Analysis/HighamChapter7.lean` passed after the Problem 7.5 insertion.
- `lake build LeanFpAnalysis.FP.Analysis.HighamChapter7` passed with `3025` jobs after the Problem 7.5 and lookup updates.
- `lake env lean --tstack=65536 examples/LibraryLookup.lean` passed after the lookup updates.
- `timeout 600s lake build` passed after the final report/log updates with `3507` jobs and only pre-existing QR/Givens/FastMatMul linter warnings outside Chapter 7.
- `git diff --check` passed after the final report/log updates.
- Focused scan over `LeanFpAnalysis/FP/Analysis/HighamChapter7.lean`, `examples/LibraryLookup.lean`, and `docs/LIBRARY_LOOKUP.md` found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, `by sorry`, `False.elim`, `placeholder`, `TODO`, `FIXME`, `WAIT-PREVIOUS-SPLIT`, or `WAIT-SPLIT1` matches.
- Broad Lean-file scan over `LeanFpAnalysis` and `examples` for `sorry`, `admit`, `axiom`, `unsafe`, `opaque`, and `by sorry` found only the pre-existing prose phrase "admit an actual" in a `Norms.lean` doc comment.  A broader `False.elim` scan found only ordinary contradiction proofs outside the final Chapter 7 surface, not placeholders.
- `#print axioms` for `problem7_5_projection_norm_le_sigmaTail_mul_norm`, `problem7_5_sigmaMin_mul_norm_le_image_norm`, `problem7_5_norm_le_inv_sigmaMin_mul_image_norm`, `problem7_5_svd_projection_relative_error_bound`, and `problem7_5_svd_projection_relative_error_bound_source_indices` reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Post-proof source re-audit re-extracted the Chapter 7 PDF and Appendix A text.  The Lean proof follows the Appendix A solution: `Delta x = A^{-1} Delta b`, `||Delta x||_2 <= sigma_n^{-1} ||Delta b||_2`, and the lower bound for `||x||_2` from the projected left-singular-vector coordinates.
- No orphan typeclass hypotheses, theorem-equivalent assumptions, local axioms, vacuous definitions, or unproved placeholders were introduced.  The Problem 7.5 projection norm definition is non-vacuous coordinate energy, not a certificate field.
- The requested split-planning filenames are not present under the repository-local `chapter_splitting/` directory, but the canonical FLARE copies were located and read under `/home/mymel/flare-bundle/higham-split/planning/`.  Those planning files assign Chapter 7 to Split 2, list the primary labels Theorems 7.1-7.8, Corollary 7.6, and Lemma 7.9, list equations `(7.1)`-`(7.33)`, and list Problems 7.1-7.6 and 7.10-7.14 as the Chapter 7 Split 2 ledger.
