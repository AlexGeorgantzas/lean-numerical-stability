# Higham Chapter 13 Bottleneck Ledger

This ledger records selected-scope Chapter 13 targets that survived repeated
proof or audit passes with the same missing foundation. It is a work queue, not
a completion claim. A row closes only when the listed Lean dependency is proved
locally or replaced by a stronger local theorem that directly proves the source
claim.

| Status | Source claim | Exact blocking Lean theorem | Dependencies and local candidates | Failed routes and evidence | Chosen route | Next dependency theorem | Validation |
|---|---|---|---|---|---|---|---|
| RED | Theorems 13.7--13.8 and Eq.13.21 active Algorithm 13.3 block diagonal dominance/growth route. | Instantiate the source inverse-bound table for the concrete active Schur-stage pivots, or prove directly that `higham13_algorithm13_3_pivotInvNorm pivotInv k * higham13_algorithm13_3_diagLowerCert ... k ⟨k,hk⟩ <= 1`. The table route must supply the initial lower bound, the Eq.13.18 active diagonal update inequality, and the active reciprocal upper bound by `(higham13_algorithm13_3_pivotInvNorm pivotInv k)⁻¹`. | Existing bridges: `higham13_algorithm13_3_diagLowerCert`, `higham13_algorithm13_3_diagLowerCert_eq`, `higham13_algorithm13_3_diagLowerCert_update`, `higham13_algorithm13_3_diagLowerCert_active_le_of_diag_update`, `higham13_algorithm13_3_diagLowerCert_diag_lower_of_source_table`, `higham13_algorithm13_3_pivotInvNorm`, `norm_ne_zero_of_isRightInverse`, `higham13_algorithm13_3_diagLowerCert_active_mul_eq_one_of_pivot_right_inverse_reciprocal`, `SchurStageActivePivotInvDiagLower13_7`, `SchurStageActivePivotInvDiagLower13_7.of_active_mul_eq_one`, `SchurStageActivePivotInvDiagLower13_7.of_pivot_bound`, `higham13_algorithm13_3_diagLowerCert_diag_lower_of_active_mul_eq_one`, `higham13_algorithm13_3_diagLowerCert_diag_lower_of_pivot_bound`, `higham13_algorithm13_3_diagLowerCert_pivot_bound_of_diag_lower`, `higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_column_bdd_diag_lower`, `higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_column_bdd_diag_lower`, `higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_diag_lower`, `higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_of_det_ne_zero`, `higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_of_diag_eq_of_det_ne_zero`, and the Eq.13.21 upper-stage wrappers. | Multiple passes added exact-update, local-Schur, upper-stage, diagonal-update, reciprocal, active-product, direct-product, one-sided certificate adapters, a right-inverse/reciprocal bridge, the source-table diagonal-lower bridge, and now the direct one-sided-certificate/source-table finite-history packages. The determinant-nonzero source-table wrappers remove the separate positive-growth-denominator proof artifact from both the table package and exact diagonal-update equality form by deriving it from `det (blockMatrixFlatFin A) != 0`. What remains is not another wrapper: it is constructing or instantiating that source inverse-bound table/active reciprocal upper bound from actual nonsingular Schur-stage pivots, or proving the direct active product/certificate bound. | Use the source-table bridge if the inverse/min-norm proof path supplies a stage table; otherwise use the direct one-sided-certificate or pivot-product route. Use the right-inverse bridge when exact active pivot inverses are available. | `higham13_algorithm13_3_source_inverse_bound_table_of_active_schur_pivots` or a direct `higham13_algorithm13_3_diagLowerCert_pivot_bound`/`SchurStageActivePivotInvDiagLower13_7` theorem with no active-product/source-table hypothesis. | After proof: `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `lake env lean -s 65536 examples/LibraryLookup.lean`, placeholder scan, and `#print axioms` for the new source-facing closure. |
| RED | Problem 13.4 and the Eq.13.22/Eq.13.23 premise derivations: `||A21 A11^{-1}|| <= n rho_n kappa(A)` and `kappa(S) <= rho_n kappa(A)` in the source max-entry norm. | Instantiate the recursive source certificate by proving the per-tail direct lower-budget/condition comparison for the Schur-tail chain, then supply the final Eq.13.23 `rho <= 2` proof. | Existing bridges: `maxEntryNormRect_rectMatMul_le`, `maxEntryNormRect_eq_maxEntryNorm`, `maxEntryNormRect_le_maxEntryNorm_of_reindex_eq`, `blockMaxNorm_le_maxEntryNorm_of_reindex_eq`, `maxEntryNorm_const_nonneg`, `higham13_problem13_4_localGrowthEnvelope`, `higham13_problem13_4_localGrowthEnvelope_contains_initial`, `higham13_problem13_4_localGrowthEnvelope_contains_schur`, `higham13_problem13_4_localGrowthEnvelope_contains_block_upper`, `growthFactorEntry_nonneg`, `growthFactorEntry_ge_one_of_maxEntryNorm_le`, `maxEntryNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm`, `blockMaxNorm_le_growthFactorEntry_mul_of_le_maxEntryNorm`, `maxEntryNormRect_le_growthFactorEntry_mul_of_le_maxEntryNorm`, `maxEntryNormRect_invOf_reindex_equiv_nonsingInv_entry_bound`, `higham13_problem13_4_A21A11inv_maxEntryNormRect_from_block_inverse_growth`, `higham13_problem13_4_schur_kappa_maxEntryNormRect_from_block_inverse`, `higham13_problem13_4_maxEntry_bounds_from_block_inverse_growth`, `higham13_problem13_4_maxEntry_bounds_from_source_block_inverse_growth`, `higham13_problem13_4_maxEntry_bounds_from_source_block_inverse_growth_exact_kappa`, `higham13_problem13_4_maxEntry_bounds_from_source_schur_growth_exact_kappa`, `higham13_problem13_4_maxEntry_bounds_from_source_growthFactorEntry_exact_kappa`, `higham13_problem13_4_L21_eq13_22_premise_from_source_growthFactorEntry_exact_kappa`, `higham13_eq13_22_local_product_from_source_growthFactorEntry_exact_kappa`, `higham13_eq13_23_local_product_from_source_growthFactorEntry_exact_kappa`, `higham13_eq13_22_local_block_product_from_source_growthFactorEntry_exact_kappa`, `higham13_eq13_23_local_block_product_from_source_growthFactorEntry_exact_kappa`, `higham13_eq13_22_local_block_product_from_history_envelope_exact_kappa`, `higham13_eq13_23_local_block_product_from_history_envelope_exact_kappa`, `higham13_problem13_4_maxEntry_bounds_from_source_growthFactorEntry_exact_kappa_of_schur_submatrix`, `higham13_problem13_4_schurStageMatrix`, `higham13_problem13_4_schurStageMatrix_lower_right`, `higham13_problem13_4_maxEntry_bounds_from_source_schurStageMatrix_exact_kappa`, `higham13_problem13_4_L21_eq13_22_premise_from_source_schurStageMatrix_exact_kappa`, `higham13_problem13_4_L21_eq13_22_premise_from_matrix_stage_history_first_split_exact_kappa`, `higham13_eq13_22_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa`, `higham13_eq13_22_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa`, `higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa`, `higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa`, `Higham13Eq1322LowerComparisonSourceChain`, `Higham13Eq1322LowerComparisonSourceChain.to_blockLUBudgetChain`, `Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_22_product_exact_kappa`, `Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa`, `higham13_inverse_ratio_one_sided_containment_counterexample`, `higham13_inverse_ratio_not_implied_by_one_sided_containment`, `higham13_inverse_ratio_principal_tail_counterexample`, the older displayed-inverse/full-block adapters, and the auxiliary operator-certificate route. | The old displayed-`A11^{-1}`/`S^{-1}` inverse-entry certificate blocker has been bypassed, the full-inverse max-entry certificate is instantiated from source block identification plus `nonsingInv (r+s) A`, the condition-product certificate is closed by choosing `κ(A) = ||A||_max ||A^{-1}||_max`, the entrywise/norm-level Schur-growth mismatch is closed, `ρ` is now the formal `growthFactorEntry`, the direct norm inclusion is derived from a lower-right submatrix equality, and the local one-step Schur-stage matrix closes that equality by construction. The `ρ >= 1` algebra needed for Eq.13.22 is closed by `growthFactorEntry_ge_one_of_maxEntryNorm_le`; the general lower-factor bridge promotes `nρκ(A)` to `nρ^2κ(A)` for any source growth matrix satisfying the initial/Schur containment premises. The square and block helpers give the matching upper-factor premises from upper-factor containment, the local square/block Eq.13.22/Eq.13.23 product bridges combine these under one common growth object, and the finite local history envelope discharges the initial/Schur/block-upper containments for one local triple. The first-split lower-left matrix-stage bridge discharges the lower-left Eq.13.22 premise for the source first split, the Eq.13.22 one-step product lift packages it with the first-row upper bound plus recursive Schur-tail hypotheses, the Eq.13.22 witness lift adds `BlockLUFactSpec` for the explicit factors, and the Eq.13.23 one-step product/witness lifts specialize the same first-split surface under `rho <= 2`. The source-chain lift now packages recursive induction/lift from source certificate to full factors. A shortcut through the older abstract active-stage theorem was rejected because elementwise matrix max norm has no true `SeminormedRing` multiplication, while the operator-norm matrix ring is not the source max-entry norm. The shortcut that tries to derive the inverse-ratio comparison from ordinary one-sided norm/inverse-norm containment is formally rejected by `higham13_inverse_ratio_not_implied_by_one_sided_containment`, and `higham13_inverse_ratio_principal_tail_counterexample` shows that even a concrete right-inverse/principal-tail full matrix relation with one-sided max-entry containments is still insufficient. What remains is proving the per-tail direct lower-budget/condition comparison that populates `Higham13Eq1322LowerComparisonSourceChain`, with any inverse-ratio proof still requiring a genuine stronger source argument or a direct lower-budget comparison. | Use the source block-inverse max-entry route as the source proof route. Add adapters only if they prove the per-tail direct lower-budget comparison/source certificate or the final `rho <= 2` theorem. | A per-tail direct lower-budget/condition comparison theorem that instantiates `Higham13Eq1322LowerComparisonSourceChain`; the inverse-ratio theorem and the active-stage proof of `rho <= 2` remain separate open routes. | Same Chapter 13 module build/lookup/placeholder scan, plus `#print axioms` for new Problem 13.4/Eq.13.22/Eq.13.23 bridge theorems. |
| RED | Theorem 13.6 and Eq.13.16 implementation-facing block LU solve backward-error theorem. | Prove the algorithm-specific first-order factorization and solve estimates for Algorithm 13.3 Implementation 1, rather than only aggregating supplied estimates. | Existing local support: `Algorithm13_3Implementation1LocalSpec`, `BlockSolveFirstOrderSpec`, `DiagonalBlockSolveFirstOrderSpec`, `higham13_eq13_14_from_block_solve_spec`, `higham13_eq13_15_from_diagonal_block_solve_spec`, `block_lu_solve_backward_error`, and `block_lu_solve_backward_error_firstOrder`. | The book omits the proof and cites Demmel--Higham--Schreiber [326]. Current Lean proves scalar aggregation from model/spec premises, so it intentionally assumes the implementation-local estimates that the source citation is meant to establish. | Acquire/formalize the [326] proof path, or keep only conditional model theorems while the source row stays open. | `block_lu_solve_backward_error_higham_13_6` or a set of local Algorithm 13.3 Implementation 1 first-order factor/solve estimate theorems that imply it. | Build and lookup as above, plus a proof-source ledger update naming the external result and the local closure theorem. |
| CLOSED | Lemma 13.9 SPD block bound `||A21 A11^{-1}||_2 <= sqrt(kappa_2(A))`. | Closed by `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_spd_leading_nonsingInv_kappa2`, which models the displayed `A11^{-1}` as the canonical `nonsingInv` of the leading principal block. | Existing route: `higham13_lemma13_9_cholesky_block_identity`, `higham13_lemma13_9_product_majorant_from_square_bounds`, `higham13_lemma13_9_R12_rectOpNorm2Le_of_A22_cholesky_block`, `higham13_lemma13_9_A22_opNorm2Le_of_full_block`, `higham13_lemma13_9_A11inv_opNorm2Le_of_full_inverse_block`, `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_nonempty_full_operator_bounds_kappa_product`, Cholesky product extraction through `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum`, Loewner/PSD bridges through `finitePSD_cauchy_schwarz`, `finiteLoewnerLe_right_inverse_upper_of_smul_id_le`, `finiteLoewnerLe_smul_id_of_opNorm2Le`, `finiteLoewnerLe_smul_id_le_of_right_inverse_finiteOpNorm2Le`, `finiteLoewnerLe_smul_id_le_of_right_inverse_opNorm2Le`, exact norm bridges `opNorm2`, `opNorm2Le_opNorm2`, `opNorm2_pos_of_right_inverse_at`, `opNorm2_pos_of_right_inverse`, `kappa2`, canonical-inverse bridges `isSymPosDef_to_matrix_posDef`, `isSymPosDef_det_ne_zero`, `isRightInverse_nonsingInv_of_isSymPosDef`, inverse-identification bridges `nonsingInv_eq_of_isRightInverse`, `nonsingInv_rectMatMul_transpose_self_of_IsInverse`, and source-order wrappers through `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_cholesky_fact_fin_sum_spd_kappa2_nonsingInv`. | The block algebra, ordering, Cholesky-factor extraction from SPD, `R11` inverse construction, full-matrix symmetry/PSD, Loewner/operator conversions, exact l2 operator norm surface, product `kappa2` surface, canonical full inverse from SPD, and canonical leading-principal inverse identification are all proved. | Closed by choosing a Cholesky factor from `cholesky_existence`, proving `nonsingInv A11 = R11^{-1}R11^{-T}`, and feeding the exact-`kappa2` route. | `higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_spd_leading_nonsingInv_kappa2`. | Verified by `lake env lean LeanFpAnalysis/FP/Analysis/MatrixAlgebra.lean`, `lake build LeanFpAnalysis.FP.Analysis.MatrixAlgebra`, `lake env lean LeanFpAnalysis/FP/Algorithms/LU/BlockLU.lean`, `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `lake env lean -s 65536 examples/LibraryLookup.lean`, placeholder scan, `git diff --check`, and `#print axioms` with only standard Mathlib axioms. |
| CLOSED | Lemma 13.10 SPD Schur complement condition-number comparison `kappa_2(S) <= kappa_2(A)`. | Closed by `higham13_lemma13_10_schur_kappa_bound_of_spd`, which proves the exact source `Fin (r+s)`/canonical-`nonsingInv` `kappa2` comparison from SPD. | Closure route: `higham13_spd_leadingBlock_posDef`, `higham13_spd_schurComplement_source_posDef`, `higham13_spd_schurComplement_source_loewnerLe_A22_of_full`, `finiteOpNorm2Le_of_finitePSD_of_finiteLoewnerLe_of_finiteOpNorm2Le`, `higham13_lemma13_10_schur_opNorm2Le_of_full_operator_bound`, `higham13_problem13_4_Sinv_eq_full_inverse_lower_right_of_block_inverse`, `higham13_problem13_4_Sinv_finiteOpNorm2Le_from_block_inverse`, `finiteOpNorm2Le_invOf_reindex_equiv_nonsingInv`, `higham13_problem13_4_Sinv_finiteOpNorm2Le_from_source_block_inverse`, `higham13_problem13_4_Sinv_finiteOpNorm2Le_from_source_posDef_block_inverse`, and `kappa2_le_of_opNorm2Le_bounds_general`. | Earlier certificate-only and conditional routes did not close the row because they left SPD-derived constructive invertibility, `⅟S`/`nonsingInv` alignment, or the final `kappa2` product open. The final theorem discharges those obligations; `[Nonempty (Fin s)]` is retained as the domain condition for the trailing Schur complement. Problem 13.4 remains separately open in the source max-entry norm. | Closed by the direct SPD operator route rather than by assuming the target condition-number bound. | `higham13_lemma13_10_schur_kappa_bound_of_spd`. | Verified by direct Lean checks for `MatrixAlgebra.lean` and `BlockLU.lean`, `lake build LeanFpAnalysis.FP.Algorithms.LU.BlockLU`, `lake env lean -s 65536 examples/LibraryLookup.lean`, placeholder scan, `git diff --check`, and `#print axioms` for the closure chain with only standard Mathlib axioms. |

Latest SPD-section checkpoint:
`higham13_lemma13_9_cholesky_route_rectOpNorm2Le_from_spd_leading_nonsingInv_kappa2`
closes Lemma 13.9, and `higham13_lemma13_10_schur_kappa_bound_of_spd`
closes Lemma 13.10.  The active red bottlenecks are now the Algorithm 13.3
active pivot certificate route, Problem 13.4's source max-entry proof route,
and the Theorem 13.6 implementation-facing proof source.  The Algorithm 13.3
row now has a genuine right-inverse/reciprocal route through the direct pivot
bound, active column dominance, active-stage growth, and Eq.13.21 assembled
upper-factor wrappers, plus finite function-block `growthFactorEntry <= 2`
package wrappers from the same right-inverse/reciprocal data, and a source-table route from the Eq.13.18 diagonal
update inequality to the concrete `diagLowerCert` certificate.  The direct
one-sided-certificate wrappers
`higham13_algorithm13_3_stageHistoryGrowthMatrix_le_two_of_column_bdd_diag_lower`,
`higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_column_bdd_diag_lower`,
and
`higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_diag_lower`
now send that concrete certificate straight to the finite function-block
history norm bound, `growthFactorEntry <= 2`, and the paired
Eq.13.21/finite-history package.  The source-table adapters
`higham13_algorithm13_3_diagLowerCert_pivot_bound_of_source_table`,
`higham13_algorithm13_3_active_column_dominance_of_column_bdd_source_table`,
`higham13_algorithm13_3_active_stage_block_bound_of_column_bdd_source_table`,
and
`higham13_algorithm13_3_upperFromStages_eq13_21_blockMaxNorm_bound_of_column_bdd_source_table`
now carry that supplied source table into the direct pivot-product, active
dominance/growth, and Eq.13.21 column-BDD interfaces.
`higham13_algorithm13_3_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table`
also carries the supplied table through the finite function-block stage-history
object to `growthFactorEntry <= 2`, and
`higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table`
packages that fact together with the Eq.13.21 assembled-upper bound from the
same hypotheses; the companion
`higham13_algorithm13_3_upperFromStages_eq13_21_and_stageHistoryGrowthFactor_le_two_of_column_bdd_source_table_of_diag_eq`
accepts the book-style exact diagonal-update recurrence.  The remaining
missing step is
instantiating the source inverse-bound table/active reciprocal upper bound from
actual Schur-stage pivots or proving the direct active product bound; the true
matrix-product dimension-free route remains separate.
The route-rejection theorem
`higham13_algorithm13_3_pivot_right_inverse_not_imply_diagLowerCert_pivot_bound`
now shows that exact active pivot right-inverse data alone cannot replace the
missing reciprocal/table hypothesis: a one-block scalar stage has a certified
pivot inverse but a diagonal lower certificate large enough to violate the
direct pivot product bound.
Problem 13.4 now has a block-inverse max-entry route proving both displayed
inequalities for a concrete local one-step Schur-stage growth matrix from a
formal `growthFactorEntry` instance, source block identifications, and the
exact max-entry product representation of `κ(A)`.  The local Eq.13.22/Eq.13.23
product bridges also combine this lower-block bound with a contained upper
factor under one common growth object; the remaining row work is constructing
that recursive/global growth object and lifting the local block product to the
full factors.
The scalar audit
`higham13_stage_local_budget_not_implied_by_problem13_4_bound` now also rules
out a weaker shortcut: tail-growth domination together with the Problem
13.4-shaped comparison `kappaTail <= rho * kappa` does not by itself imply the
exact `rho^2 kappa` lower-budget transport used by the recursive
Eq.13.22/Eq.13.23 adapters.  The lower-budget comparison therefore still needs
a direct source proof or a genuinely stronger condition comparison.
Conversely, `higham13_stage_local_source_lblock_budget_le_of_problem13_4_bound`
now records the positive scalar step that matches the book's Eq.13.22
derivation: a one-local-growth budget `s * rhoTail * kappaTail` is enlarged to
the fixed full ambient `n * rho^2 * kappa` budget from `s <= n`,
`rhoTail <= rho`, and `kappaTail <= rho * kappa`.  This helps separate the
source-shaped local lower-block route from the stronger exact-tail transport
that the counterexample rejects.
The source-shaped route now composes through the assembled matrix-stage product
surface via
`higham13_algorithm13_3_multiplier_bounds_from_source_lblock_budgets_exact_kappa`,
`higham13_eq13_22_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa`,
and
`higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa`.
These remove the black-box per-stage squared multiplier hypothesis when local
Problem 13.4 lower-block estimates and the scalar comparison table are supplied,
but they do not prove that table or the Eq.13.23 source `rho <= 2` theorem.
The same source-shaped route now has concrete pivot-right witness wrappers
`higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse`
and
`higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse`.
These package the assembled Eq.13.22/Eq.13.23 product bounds as
`BlockLUFactSpec` factors under exact pivot right-inverse data.  They still do
not prove the local lower-block estimate table, scalar comparison table, or
Eq.13.23 source `rho <= 2` theorem.
The canonical-inverse variants
`higham13_eq13_22_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_det_ne_zero`,
`higham13_eq13_23_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_det_ne_zero`,
`higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse_of_det_ne_zero`
and
`higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_source_lblock_budgets_exact_kappa_of_pivot_right_inverse_of_det_ne_zero`
derive the full positive denominator and right-inverse certificate from
`det(blockMatrixFlatFin Ablk) != 0` and use
`nonsingInv (m*r) (blockMatrixFlatFin Ablk)` as the full inverse object.  They
remove that proof-artifact surface from the source-local route but do not
change the remaining source obligations.
The latest dominated-envelope adapters
`higham13_eq13_22_local_block_product_from_dominated_history_envelope_exact_kappa`
and
`higham13_eq13_23_local_block_product_from_dominated_history_envelope_exact_kappa`
reduce the recursive/global part to one explicit theorem: the chosen GE history
matrix must dominate `higham13_problem13_4_localGrowthEnvelope` in max-entry
norm.  They close the local single-domination adapter but do not close the
recursive history theorem or the full-factor lift.
The latest Schur-tail positivity cleanup adds
`det_ne_zero_blockMatrixFlatFin_blockSchur_of_first_split_invertible` and
`maxEntryNorm_blockMatrixFlatFin_blockSchur_pos_of_first_split_invertible`, plus
the flat lower-comparison and non-flat inverse-ratio/lower-comparison
`_of_schur_invertible` successor/product wrappers.  These derive the positive
flattened Schur-tail denominator from the first-split Schur-complement
invertibility already present in the successor route; the non-flat variants
also derive the full positive denominator from determinant nonsingularity.
This removes proof-artifact `hTailPos` and `hApos` premises, but it does not
prove the inverse-ratio comparison, prove the direct lower-budget comparison,
populate the recursive source certificate, or prove the final Eq.13.23
`rho <= 2` source surface.

The ambient-budget recursive-chain checkpoint adds `Higham13BlockLUBudgetChain`,
`Higham13BlockLUBudgetChain.exists_blockLUFact_norms`,
`Higham13BlockLUBudgetChain.mono`,
`Higham13BlockLUBudgetChain.lowerBudget_nonneg`, and
`Higham13BlockLUBudgetChain.exists_blockLUFact_product`, plus the source-shaped
wrappers `Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product` and
`Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product`, and the
exact-κ source wrappers
`Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_22_product_exact_kappa` and
`Higham13BlockLUBudgetChain.exists_blockLUFact_eq13_23_product_exact_kappa`,
plus the exact-κ base/successor constructor instantiations
`higham13_eq13_22_blockLUBudgetChain_one_from_matrix_stage_history_exact_kappa`
and
`higham13_eq13_22_blockLUBudgetChain_succ_from_matrix_stage_history_first_split_exact_kappa`,
`higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa`,
`higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa`,
`higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_inverse_ratio_matrix_stage_history_exact_kappa`,
`higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa`,
`higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa`,
`higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_matrix_stage_history_exact_kappa`,
and the tail-chain successor product witnesses
`higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_chain_matrix_stage_history_exact_kappa`
and
`higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_chain_matrix_stage_history_exact_kappa`.
This closes the
structural recursion from compatible per-stage fixed lower/upper budgets to
concrete `BlockLUFactSpec` factors, budget-enlargement transport for tail
chains, their `C_L*C_U` product bound, and the
Eq.13.22/Eq.13.23 displayed product constants, including the exact source
`growthFactorEntry`/`‖A‖_max‖A^{-1}‖_max` form, once the source budgets are
available.  The base chain and first-split successor constructor cases are now
instantiated from the matrix-stage source data, and the first-split successor
product conclusions are now packaged as concrete `BlockLUFactSpec` witnesses
from a supplied recursive tail chain.  The tail-local inverse-ratio successor
constructor now also composes the exact tail-to-full budget transport with the
first-split chain step, and the tail-local inverse-ratio witness wrappers now
package the corresponding Eq.13.22/Eq.13.23 concrete factor/product witnesses.
The direct lower-comparison successor and witness wrappers provide the same
assembly path when a source block-inverse argument proves the lower-budget
comparison directly, without forcing it through the stronger inverse-ratio
surface.
The determinant-nonzero interface now also removes the explicit
`IsRightInverse ... nonsingInv` proof-artifact premise from these exact-κ
surfaces.  `higham13_blockMatrixFirstSplitFlat_nonsingInv_rightInverse_of_det_ne_zero`
derives that certificate from `det A != 0`, and the `_of_det_ne_zero` successor
chain/product wrappers expose the same Eq.13.22/Eq.13.23 constants under source
nonsingularity instead of an auxiliary inverse-certificate hypothesis.
The one-block base surface now has the same source-style cleanup:
`maxEntryNorm_pos_of_det_ne_zero` supplies the positive growth denominator, and
`higham13_eq13_22_blockLUBudgetChain_one_from_matrix_stage_history_exact_kappa_of_det_ne_zero`
instantiates the exact-κ base chain case from determinant nonsingularity alone.
The concrete one-block witness surfaces now match this cleanup as well:
`higham13_eq13_22_exists_blockLUFact_one_norms_from_matrix_stage_history_exact_kappa_of_det_ne_zero`,
`higham13_eq13_22_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa_of_det_ne_zero`,
and
`higham13_eq13_23_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa_of_det_ne_zero`
derive the separate Eq.13.22 budgets and Eq.13.22/Eq.13.23 product witnesses
from the same determinant premise, leaving only the explicit Eq.13.23
`rho <= 2` side condition on the point-row wrapper.
The first-split/uniform-flat exact-κ representation issue is also closed:
`blockMaxNorm_le_maxEntryNorm_blockMatrixFirstSplitFlat`,
`maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMaxNorm`, and
`maxEntryNorm_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin` prove that the
two flattenings have the same Chapter 13 max-entry norm.  The concrete
equivalences `blockMatrixFirstSplitToFlatProductEquiv` and
`blockMatrixFirstSplitToFlatFinEquiv`, the entrywise reindexing theorem
`blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin_reindex`, and the inverse
bridges `maxEntryNormRect_nonsingInv_blockMatrixFirstSplitFlat_le_blockMatrixFlatFin`,
`maxEntryNormRect_kappa_blockMatrixFirstSplitFlat_le_blockMatrixFlatFin`, and
`maxEntryNormRect_kappa_blockMatrixFirstSplitFlat_le_blockMatrixFlatFin_of_det_ne_zero`
transport the first-split canonical-inverse norm and exact condition product
to the uniform flat representation.  The determinant/growth/budget bridges
`det_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin`,
`det_ne_zero_blockMatrixFirstSplitFlat_of_blockMatrixFlatFin`,
`growthFactorEntry_blockMatrixFirstSplitFlat_eq_blockMatrixFlatFin`,
`higham13_eq13_22_firstSplit_lower_budget_le_flat_matrix_stage_history_exact_kappa`,
and
`higham13_eq13_22_firstSplit_upper_budget_eq_flat_matrix_stage_history_exact_kappa`
now also transport determinant nonsingularity, the matrix-stage growth factor,
and the complete Eq.13.22 lower/upper budget surfaces from the first-split
constructor to the uniform flat source representation.  This removes the
representation mismatch, but it does not prove the Schur-tail
lower-budget/source comparison.
The successor-chain surface now also has the uniform-flat determinant wrapper
`higham13_eq13_22_blockLUBudgetChain_succ_from_flat_matrix_stage_history_exact_kappa_of_det_ne_zero`,
which builds the successor under `blockMatrixFlatFin` exact-κ budgets directly
from a supplied recursive tail chain under those same budgets.  This removes a
first-split budget artifact from the recursive successor statement, but it still
does not instantiate the recursive tail chain or prove the source lower-budget
comparison.
The matching concrete witness surface is now available as
`higham13_eq13_22_exists_blockLUFact_succ_product_from_flat_tail_chain_matrix_stage_history_exact_kappa_of_det_ne_zero`
and
`higham13_eq13_23_exists_blockLUFact_succ_product_from_flat_tail_chain_matrix_stage_history_exact_kappa_of_det_ne_zero`.
These compose the uniform-flat successor chain with the exact-κ chain-to-product
packagers, so the final `BlockLUFactSpec` witnesses and Eq.13.22/Eq.13.23
product bounds are stated directly against `blockMatrixFlatFin Ablk`.  This
removes the remaining first-split representation artifact from that supplied
tail-chain product surface.
The flat tail-transport bridge
`higham13_eq13_22_tail_chain_to_flat_budget_from_lower_comparison_matrix_stage_history_exact_kappa_of_det_ne_zero`
and the combined successor
`higham13_eq13_22_blockLUBudgetChain_succ_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero`
now take a tail-local recursive chain plus the direct lower-budget comparison
to the uniform-flat full successor chain.  The companion witness wrappers
`higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero`
and
`higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_local_chain_lower_comparison_flat_matrix_stage_history_exact_kappa_of_det_ne_zero`
package the corresponding concrete Eq.13.22/Eq.13.23 factor products.  This
closes the first-split budget representation artifact on the lower-comparison
route itself.
The source-chain lift now adds `Higham13Eq1322LowerComparisonSourceChain`,
`Higham13Eq1322LowerComparisonSourceChain.det_ne_zero`,
`Higham13Eq1322LowerComparisonSourceChain.to_blockLUBudgetChain`,
`Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_22_product_exact_kappa`,
and
`Higham13Eq1322LowerComparisonSourceChain.exists_blockLUFact_eq13_23_product_exact_kappa`.
This recursive certificate replaces the prebuilt ambient
`Higham13BlockLUBudgetChain` hypothesis by source-shaped per-tail determinant,
pivot, dimension, and direct lower-budget comparison data, then packages the
Eq.13.22/Eq.13.23 concrete factor/product witnesses.  It does not prove the
per-tail direct source lower-budget comparison or supply the Eq.13.23
`rho <= 2` theorem.
The remaining blocker is no longer the
abstract induction/product-packaging shape.  The shifted-tail history
comparison is also available as
`higham13_algorithm13_3_matrixStageHistoryBound_tail_le` and
`higham13_algorithm13_3_matrixStageHistoryGrowthMatrix_tail_le`, and the exact
upper-budget scalar package is
`higham13_eq13_22_tail_upper_budget_le_full_matrix_stage_history_exact_kappa`,
using `growthFactorEntry_mul_maxEntryNormRect_eq_maxEntryNorm`.  The transport
adapter
`higham13_eq13_22_tail_chain_to_full_budget_from_lower_comparison_matrix_stage_history_exact_kappa`
now applies `Higham13BlockLUBudgetChain.mono` with that proved upper comparison,
while
`higham13_eq13_22_tail_lower_budget_le_full_from_inverse_ratio_matrix_stage_history_exact_kappa`
reduces the lower comparison to the explicit inverse-ratio/condition
hypothesis, and
`higham13_eq13_22_tail_chain_to_full_budget_from_inverse_ratio_matrix_stage_history_exact_kappa`
packages the full tail-chain transport directly from that hypothesis.
Thus the upper-growth half of transporting recursive Schur-tail budgets to the
full ambient history, the successor-chain assembly after that transport, and
the successor product-witness packaging are no longer blockers.  The active
blocker is the per-tail source lower-budget/condition comparison needed to
justify the source certificate from Problem 13.4 scalar condition/inverse
estimates.  The ordinary-containment-to-inverse-ratio
shortcut remains formally rejected, so any inverse-ratio proof would still need
a genuinely stronger source comparison.  For Eq.13.23 the route also needs
supplying the final `rho <= 2` hypothesis at the source surface.

The matrix-stage shape checkpoint adds
`higham13_algorithm13_3_upperFromMatrixStages_eq_of_le`,
`higham13_algorithm13_3_upperFromMatrixStages_lower_zero`,
`higham13_algorithm13_3_upperFromMatrixStages_first_row`,
`higham13_algorithm13_3_lowerFromMatrixStages_eq_of_lt`,
`higham13_algorithm13_3_lowerFromMatrixStages_diag`,
`higham13_algorithm13_3_lowerFromMatrixStages_upper_zero`,
`higham13_algorithm13_3_lowerFromMatrixStages_first_column`,
`higham13_algorithm13_3_schurStageMatrixBlock_tail_shift`,
`higham13_algorithm13_3_upperFromMatrixStages_succ_eq_blockLUOneStepU`,
`higham13_algorithm13_3_lowerFromMatrixStages_succ_eq_blockLUOneStepL`,
`higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_left_inverse`,
`higham13_algorithm13_3_matrixStages_product_eq_of_pivot_left_inverse`,
`higham13_algorithm13_3_pivot_left_inverse_of_pivot_right_inverse`,
`higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_pivot_right_inverse`,
`higham13_algorithm13_3_matrixStages_product_eq_of_pivot_right_inverse`,
`higham13_algorithm13_3_matrixStages_blockLUFactSpec_of_product_eq`,
`higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound`,
`higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound_of_pivot_left_inverse`,
`higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound_of_pivot_right_inverse`,
`higham13_algorithm13_3_matrixStages_exists_blockLUFact_product_bound_of_pivotInv_eq_invOf`,
`higham13_eq13_22_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds`,
`higham13_eq13_23_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds`,
`higham13_eq13_22_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivot_left_inverse`,
and
`higham13_eq13_23_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivot_left_inverse`,
plus the corresponding pivot-right-inverse wrappers
`higham13_eq13_22_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivot_right_inverse`
and
`higham13_eq13_23_exists_blockLUFact_matrix_stage_product_from_multiplier_bounds_of_pivot_right_inverse`,
with exact-κ companions
`higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa`
and
`higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa`,
plus the pivot-left-inverse exact-κ companions
`higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_left_inverse`
and
`higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_left_inverse`,
and the exact-κ pivot-right-inverse companions
`higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_right_inverse`
and
`higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_pivot_right_inverse`.
This closes the definitional triangular/entry shape, including the first
source row/column entries, of the assembled matrix-stage factors, proves the
recursive Schur-tail shift and one-step assembled `L`/`U` identifications, and
packages the existing product bounds as `BlockLUFactSpec` witnesses from
explicit pivot-left-inverse certificates, from exact pivot right-inverse
certificates via `isLeftInverse_of_isRightInverse`, or from `pivotInv = ⅟pivot`
data via `isRightInverse_of_eq_invOf`.  The free assembled product-equality
hypothesis remains available in older low-level wrappers, but the certified
matrix-stage route no longer treats product equality itself as the blocker.
The remaining source obligations are exact pivot inverse certificates for
the chosen `pivotInv` sequence (either as right-inverse certificates or as
`⅟pivot` data plus invertibility), the per-stage multiplier bounds, and the
Eq.13.23 active-stage growth bound.

The 2026-06-22 post-handoff pass adds
`higham13_problem13_4_L21_eq13_22_premise_from_matrix_stage_history_first_split_exact_kappa`.
This proves the source first-split lower-left Eq.13.22 premise directly from
matrix-product Algorithm 13.3 stage-history containment, the first-split Schur
flattening equality, and the existing Problem 13.4 lower-left bridge.  It is a
real dependency for the full-factor lift, but it does not prove the recursive
`L`/`U` theorem by itself.

Two routes were explicitly rejected or left open in that pass.  First, the
older abstract active-stage theorem should not be instantiated with true
matrix blocks to prove source max-entry matrix-product bounds: the elementwise
matrix norm matches `maxEntryNorm` but has no `SeminormedRing` for true matrix
multiplication, while the operator-norm matrix ring has the wrong norm for the
source statement.  Second, the stage-local inverse-ratio hypothesis in
`higham13_eq13_22_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa`
is stronger than a plain local inverse-norm containment because it compares
inverse-to-input norm ratios; it remains an open selected-scope dependency
rather than a hidden assumption to discharge by an unrelated block-inverse
lemma.

The one-block base-case checkpoint adds
`higham13_eq13_22_exists_blockLUFact_one_norms_from_matrix_stage_history_exact_kappa`,
`higham13_eq13_22_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa`,
and
`higham13_eq13_23_exists_blockLUFact_one_product_from_matrix_stage_history_exact_kappa`.
These construct the base recursive factors `L = I` and `U = A`, prove
`BlockLUFactSpec`, preserve the separate Eq.13.22 lower/upper budgets, and
package the Eq.13.22/Eq.13.23 product bounds from the matrix-stage history
object.  This closes the base of the full-factor induction route; the
remaining blocker is the recursive theorem that combines this base with the
one-step witness lifts across all Schur tails.

The subsequent one-step lift checkpoint adds
`higham13_eq13_22_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa`.
It instantiates the first-split lower-left premise and first block-row upper
bound from the matrix-stage history, combines them with recursive Schur-tail
lower/upper hypotheses, and proves the source-shaped one-step
`n rho^3 kappa(A) ||A||` product bound for `blockLUOneStepL`/`blockLUOneStepU`.
The remaining Eq.13.22 blocker is therefore the recursive induction theorem
that supplies the tail hypotheses at every Schur level and identifies the final
recursive factors.  Eq.13.23 additionally needs the source proof of the
active-stage `rho <= 2` bridge at the final recursive surface.

The follow-up one-step witness checkpoint adds
`higham13_eq13_22_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa`.
It derives the first-pivot left-inverse identity from `invOf_mul_self`, applies
`block_lu_one_step_explicit` to a Schur-tail `BlockLUFactSpec`, and packages
the resulting explicit full factors with the one-step Eq.13.22 product bound.
This removes the gap between the one-step norm theorem and an actual
factorization witness, while still leaving the recursive induction over Schur
tails open.

The Eq.13.23 one-step checkpoint adds
`higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa`
and
`higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa`.
These compose the one-step Eq.13.22 product/witness surface with `rho <= 2`,
giving the explicit `8 n kappa(A) ||A||` first-split product bound and
matching `BlockLUFactSpec` witness.  This closes the one-step Eq.13.23
analogue; the full recursive theorem and the source proof of `rho <= 2` remain
open.

The Eq.13.23 existential-tail successor checkpoint adds
`higham13_eq13_23_exists_blockLUFact_succ_product_from_tail_witness_matrix_stage_history_exact_kappa`.
It packages the Eq.13.23 one-step witness behind the same existential
Schur-tail budget witness used by the Eq.13.22 successor wrapper, while keeping
the source-side `rho <= 2` assumption explicit.  This closes the standalone
Eq.13.23 successor surface; the global row still needs recursive compatible
tail witnesses and the source proof of `rho <= 2` where the point-row theorem
uses it.

The separate-budget one-step checkpoint adds
`higham13_eq13_22_blockLUOneStep_norms_from_matrix_stage_history_first_split_tail_exact_kappa`
and
`higham13_eq13_22_exists_blockLUOneStep_fact_norms_from_matrix_stage_history_first_split_tail_exact_kappa`.
Unlike the product-only wrappers, these preserve the lower and upper budgets
separately for the explicit `blockLUOneStepL/U` factors and package them with
`BlockLUFactSpec`.  This is the direct recursive-induction hook for Eq.13.22:
the next theorem should supply the Schur-tail hypotheses at every stage and
thread this separate-budget witness lift through the recursive factors.

The existential-tail successor checkpoint adds
`higham13_eq13_22_exists_blockLUFact_succ_norms_from_tail_witness_matrix_stage_history_exact_kappa`.
It packages the separate-budget one-step witness behind an existential witness
for the strict Schur tail, producing a successor-size `BlockLUFactSpec` with
the same source Eq.13.22 lower and upper budgets.  This closes the standalone
successor surface; the remaining theorem must recursively supply compatible
strict-tail witnesses, starting from the one-block base case.

The Eq.13.22 product successor checkpoint adds
`higham13_eq13_22_exists_blockLUFact_succ_product_from_tail_witness_matrix_stage_history_exact_kappa`.
It packages the Eq.13.22 one-step product witness behind the same existential
Schur-tail separate-budget witness, yielding the source
`n rho^3 kappa(A) ||A||` product bound for the successor factors.  This closes
the standalone Eq.13.22 product successor surface; the recursive tail-witness
supply remains the active global blocker.

The finite Algorithm 13.3 stage-history checkpoint adds
`higham13_algorithm13_3_stageHistoryBound` and
`higham13_algorithm13_3_stageHistoryGrowthMatrix`, with proofs that the history
dominates the input block table, every concrete recorded Schur stage, and the
assembled upper factor.  The bottleneck has therefore narrowed again: the next
Problem 13.4 theorem should identify the relevant flattened two-block local
Schur complement and upper factor as entries/blocks of this finite stage
history, yielding the single local-envelope domination hypothesis required by
the dominated-envelope adapters.

The local-envelope domination bridge
`higham13_problem13_4_localGrowthEnvelope_le_of_bounds` /
`higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_initial_schur`
closes the universal-property part of that single-domination step.  In the
stage-history route, the upper-factor containment is no longer a separate
blocking obligation because it is discharged by
`higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_upperFromStages`.
The bottleneck is now exactly the flattened initial-matrix containment and the
flattened local Schur-complement containment for the relevant stage/tail, after
which the existing dominated-envelope Eq.13.22/Eq.13.23 adapters can be
composed before the final full-recursive-factor lift.

The flat/stage-history containment pass closes the generic part of those two
containments.  `blockMatrixFlatFin` and
`maxEntryNorm_blockMatrixFlatFin_eq_blockMaxNorm` show that the standard
`Fin (m*r)` flattening of the block input has exactly the same max-entry norm
as the block table, so
`higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_flat_initial`
discharges the flat-initial side.  The generic theorem
`higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_stage_submatrix`
handles any scalar submatrix of any recorded stage, and
`higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_flat_initial_stage_submatrix`
composes this with the local-envelope bridge.  The active bottleneck is now
the concrete recursive tail-index equality for the local Schur complement,
not the max-entry comparison or finite-history envelope machinery.
The packaged tail pass adds `higham13_algorithm13_3_schurStageTailBlock`,
`higham13_algorithm13_3_stageHistoryGrowthMatrix_contains_flat_stage_tail`, and
`higham13_problem13_4_localGrowthEnvelope_le_stageHistoryGrowthMatrix_of_flat_initial_flat_stage_tail`,
so the remaining equality can target a named flattened stage-tail matrix rather
than the more general submatrix interface.  The source-faithful
matrix-product wrapper `higham13_algorithm13_3_schurStageMatrixBlock` and
`higham13_algorithm13_3_schurStageMatrixBlock_one_tail_eq_blockSchur` close the
first-tail identity with the actual `blockSchur` formula.  The follow-up
matrix-stage-history bridge
`higham13_problem13_4_localGrowthEnvelope_le_matrixStageHistoryGrowthMatrix_of_blockSchur_first_tail`
now dominates that local source Schur complement by the matrix-product finite
history.  The first-split reindexing/product layer
`blockMatrixFirstSplit_schur_eq_blockMatrixFlatFin_blockSchur`,
`higham13_eq13_22_local_block_product_from_matrix_stage_history_first_split_exact_kappa`,
and
`higham13_eq13_23_local_block_product_from_matrix_stage_history_first_split_exact_kappa`
also closes the local source Eq.13.22/Eq.13.23 block-product route.  The active
bottleneck is the global/recursive full-factor Eq.13.22/Eq.13.23 lift.  The
structural norm-lift dependencies
`blockLUOneStepL_blockMaxNorm_le_of_firstSplit_tail` and
`blockLUOneStepU_blockMaxNorm_le_of_firstRow_tail`, plus the packaged product
lift `blockLUOneStep_blockMaxNorm_product_le_of_firstSplit_tail`, are now
available for the explicit one-step lower and upper factors.  The source-facing
separate-budget lift
`higham13_eq13_22_exists_blockLUOneStep_fact_norms_from_matrix_stage_history_first_split_tail_exact_kappa`
is the induction-strength wrapper; the product and witness lifts
`higham13_eq13_22_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa`
and
`higham13_eq13_22_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa`
specialize these dependencies to the first source split; the Eq.13.23
specializations
`higham13_eq13_23_blockLUOneStep_product_from_matrix_stage_history_first_split_tail_exact_kappa`
and
`higham13_eq13_23_exists_blockLUOneStep_fact_product_from_matrix_stage_history_first_split_tail_exact_kappa`
add the `rho <= 2` product surface.  The recursive induction theorem combining
these one-step witness lifts across all Schur tails into the full
Eq.13.22/Eq.13.23 `L`/`U` factor bounds remains open.
The matrix-stage route also now has the assembled lower-factor surface
`higham13_algorithm13_3_lowerFromMatrixStages`, its norm lift
`higham13_algorithm13_3_lowerFromMatrixStages_blockMaxNorm_bound`, and the
full assembled product wrapper
`higham13_algorithm13_3_matrixStages_LU_product_bound`.  The conditional
assembled Eq.13.22/Eq.13.23 wrappers
`higham13_eq13_22_matrix_stage_product_from_multiplier_bounds` and
`higham13_eq13_23_matrix_stage_product_from_multiplier_bounds` are also
available, together with the stage-history specializations
`higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds` and
`higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds` that
discharge assembled-upper containment.  The pivot-left/right-inverse witness
wrappers now turn these product bounds into concrete `BlockLUFactSpec`
witnesses without an extra product-equality hypothesis once the pivot
certificates are supplied.  The open piece there is proving the per-stage
multiplier bounds for every active column; the lower diagonal
nonvacuity side condition `1 <= nρ^2κ(A)` is now closed by
`higham13_eq13_22_lower_diagonal_budget_from_right_inverse_growth` under the
right-inverse, initial-containment, and dimension-dominance hypotheses, and the
exact-κ stage-history wrappers
`higham13_eq13_22_matrix_stage_history_product_from_multiplier_bounds_exact_kappa`
and
`higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa`
instantiate it for the flattened source input.  The Eq.13.23 point-row
`ρ <= 2` hypothesis is now reduced by
`higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_active_stage_bound`
to active-stage `2‖A‖` max-entry bounds for the matrix-product Schur-stage
table.  The companion
`higham13_algorithm13_3_matrix_active_stage_bound_of_local_schur_bound` and
`higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_local_schur_bound`
derive that active-stage/`ρ <= 2` surface from active column dominance plus an
explicit local Schur max-entry estimate for the true matrix-product stage table,
while `maxEntryNorm_sub_le` and
`higham13_algorithm13_3_matrix_active_local_schur_bound_of_product_bound`
reduce that local Schur estimate to the exact matrix-product update plus an
explicit triple-product max-entry bound.  The source-conditional wrappers
`higham13_algorithm13_3_matrix_active_stage_bound_of_product_bound_diag_update`,
`higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_of_product_bound_diag_update`,
and
`higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_product_bound_diag_update`
thread that triple-product premise plus the diagonal lower-update certificate
through the active-stage, finite-history `ρ <= 2`, and exact-κ Eq.13.23 product
surfaces.  The helpers
`maxEntryNorm_matrix_mul_mul_le_dim_sq`,
`higham13_algorithm13_3_matrix_active_local_schur_bound_with_dim_factor`,
`higham13_algorithm13_3_matrix_active_column_dominance_with_dim_factor`,
`higham13_algorithm13_3_matrix_active_stage_bound_with_dim_factor`,
`higham13_algorithm13_3_matrix_active_stage_bound_with_dim_factor_of_diag_update`,
`higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_with_dim_factor`,
and
`higham13_algorithm13_3_matrixStageHistoryGrowthFactor_le_two_with_dim_factor_of_diag_update`
close the true matrix-product version with the explicit entrywise max-norm
factor `(r : ℝ)^2`, composing it all the way to finite-history `ρ <= 2` under
the strengthened pivot budget and the diagonal lower-update certificate.  This
is useful boundary evidence but not the source-compatible dimension-free
structured estimate needed for the displayed `ρ <= 2` route.  The new audit
theorems `maxEntryNorm_matrix_mul_dimension_free_counterexample` and
`maxEntryNorm_matrix_mul_mul_dimension_free_counterexample` formalize the
reason the generic matrix-norm shortcut is invalid: all-ones `2 × 2` matrices
violate both the binary and triple-product dimension-free max-entry estimates.
The wrappers
`higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_of_active_stage_bound`
and
`higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_with_dim_factor`
and
`higham13_eq13_23_matrix_stage_history_product_from_multiplier_bounds_exact_kappa_with_dim_factor_of_diag_update`
compose those active-stage reductions with the exact-κ product wrapper, with
the latter two using the strengthened dimension-aware pivot budget.  The
source-compatible active-stage proof itself is not yet closed from the
point-row dominance/source-compatible local-Schur route.  The stage-local
inverse-ratio route now also composes with these diagonal-update active-stage
surfaces via
`higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_product_bound_diag_update`,
`higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_with_dim_factor_of_diag_update`,
`higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_product_bound_diag_update_of_pivot_right_inverse`,
and
`higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_with_dim_factor_of_diag_update_of_pivot_right_inverse`.
These wrappers do not discharge the inverse/condition-number ratio; they only
thread it through the already-proved active-stage composition layers.  The new local
adapter
`higham13_problem13_4_single_block_multiplier_bound_from_local_growth_budget`
closes the extraction of one multiplier block from a local `2 × 2` Problem
13.4 budget, and
`higham13_algorithm13_3_stage_multiplier_bound_from_local_growth_budget`
specializes this extraction to the concrete Algorithm 13.3 stage table.
The local-stage packaging layer
`higham13_algorithm13_3_stageLocalBlockMatrix`,
`higham13_algorithm13_3_stageLocalFlatMatrix`,
`higham13_algorithm13_3_stageLocalSchurOfInv`, and
`higham13_eq13_22_matrix_stage_history_product_from_stage_local_budgets_exact_kappa`,
`higham13_eq13_23_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_active_stage_bound`
now feeds those single-stage adapters into the exact-κ Eq.13.23 product theorem
for every active pair, with the Eq.13.22 companion reducing the same
lower-multiplier side without the point-row `ρ <= 2` hypothesis.  The witness
wrappers
`higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_pivot_right_inverse`
and
`higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse`
package those product bounds as concrete `BlockLUFactSpec` factors under exact
pivot right-inverse data.  The local-invertible variants
`higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_pivot_right_inverse_of_local_invertible`
and
`higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse_of_local_invertible`
remove the separate local positivity table by deriving it from local full-stage
invertibility.  Thus the
multiplier side is reduced to proving the local-to-global budget comparison for
each active `2 × 2` stage partition.
For the canonical stage-local growth direct-budget route, the determinant
wrappers
`higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_pivot_right_inverse_of_det_ne_zero`
and
`higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_active_stage_bound_of_pivot_right_inverse_of_det_ne_zero`
also remove the ambient `Ainv`, full positive-denominator, and full
right-inverse proof artifacts by specializing to `nonsingInv (m*r)
(blockMatrixFlatFin Ablk)` under `det(blockMatrixFlatFin Ablk) != 0`.
They do not prove the local-to-global budget comparison or the Eq.13.23
active-stage bound.
The canonical local-growth layer
`higham13_algorithm13_3_stageLocalSchurOfPivot`,
`higham13_algorithm13_3_stageLocalGrowthMatrix`, and
`higham13_eq13_22_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa`,
`higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_budgets_exact_kappa_of_active_stage_bound`
discharges the local initial/Schur containment hypotheses for those
stage-local wrappers.  The remaining multiplier-side blocker is therefore the
local-to-global comparison for this canonical local growth budget, not local
containment bookkeeping.
The domination lemmas
`higham13_algorithm13_3_stageLocalSchurOfPivot_eq_next_diag`,
`higham13_algorithm13_3_stageLocalFlatMatrix_le_matrixStageHistoryGrowthMatrix`,
`higham13_algorithm13_3_stageLocalSchurOfPivot_le_matrixStageHistoryGrowthMatrix`,
and
`higham13_algorithm13_3_stageLocalGrowthMatrix_le_matrixStageHistoryGrowthMatrix`
now close the max-entry stage-history containment part of that comparison for
each active pair `j < i`.  The remaining local-to-global budget blocker is the
inverse/condition-number comparison between the local `2 × 2` stage partition
and the ambient flattened source matrix.
The scalar `rhoLocal <= rhoFull` row is now reduced by
`growthFactorEntry_le_of_growth_le_of_base_le` and
`higham13_algorithm13_3_stageLocalGrowthFactor_le_matrixStageHistoryGrowthFactor_of_base_le`:
the already-proved local-growth numerator domination suffices once the source
also supplies the denominator/base comparison
`||A||_max <= ||A_local||_max`.  The new audit theorem
`higham13_stage_local_base_comparison_counterexample` rules out that
denominator/base comparison as a generic stage-local consequence: a `3 × 3`
scalar-block input can have its global max entry outside the active local
`2 × 2` pair.  The remaining source work is therefore a source-specific
condition comparison or a different direct/inverse-ratio local-to-global budget
route; the theorem does not assert the denominator comparison for free.
The direct local lower-block side is now closed separately by
`higham13_problem13_4_single_block_source_lblock_bound_from_local_growth` and
`higham13_algorithm13_3_source_lblock_bound_from_stageLocalGrowth_le`: these
prove the source-shaped `r * rhoLocal * kappaLocal` estimate from the canonical
stage-local growth object and local budget domination hypotheses.  The open
source work is therefore the local-to-full scalar comparison table
(`rhoLocal <= rhoFull`, `kappaLocal <= rhoFull * kappaFull`) and the Eq.13.23
`rho <= 2` theorem, not the local Problem 13.4 lower-block extraction.  The
adapter
`higham13_algorithm13_3_multiplier_bounds_from_stageLocalGrowth_source_comparisons_exact_kappa`
now composes that local estimate with the positive scalar bridge, so supplying
only those two scalar comparison rows for every active pair is enough to obtain
the exact per-stage multiplier hypothesis consumed downstream.  The new
wrappers
`higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa`,
`higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa`,
`higham13_eq13_22_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_det_ne_zero`,
`higham13_eq13_23_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_det_ne_zero`,
`higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse`,
`higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero`,
and
`higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse`,
`higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stageLocalGrowth_source_comparisons_exact_kappa_of_pivot_right_inverse_of_det_ne_zero`
feed that multiplier theorem directly into the Eq.13.22/Eq.13.23 product and
`BlockLUFactSpec` witness surfaces, removing the local lower-block estimate
hypothesis from this canonical route.  The determinant variants also remove the
arbitrary ambient inverse/right-inverse/full-denominator proof artifacts by
specializing to `nonsingInv (m*r) (blockMatrixFlatFin Ablk)` under
`det(blockMatrixFlatFin Ablk) != 0`, and they derive the local stage
positive-denominator table from the existing local invertibility table, while
leaving the two scalar comparisons and the Eq.13.23 `rho <= 2` side condition
explicit.
The scalar adapter
`growthFactorEntry_sq_kappa_budget_le_of_growth_le_inv_ratio` and the wrappers
`higham13_eq13_22_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa`,
`higham13_eq13_23_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_active_stage_bound`,
`higham13_eq13_22_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_pivot_right_inverse`,
and
`higham13_eq13_23_exists_blockLUFact_matrix_stage_history_product_from_stage_local_growth_inverse_ratio_exact_kappa_of_active_stage_bound_of_pivot_right_inverse`
now reduce that budget blocker to an explicit cross-multiplied inverse-norm
ratio for every active pair and package the result as concrete
`BlockLUFactSpec` witnesses when exact pivot right-inverse data are supplied.
This is a real narrowing of the hypothesis surface, not a proof of the
inverse/condition-number comparison.
The local positive denominator side condition for those `growthFactorEntry`
terms is closed separately by `maxEntryNorm_pos_of_invertible`,
`higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible`, and
`higham13_algorithm13_3_stageLocalFlatMatrix_pos_of_invertible_table`, using
the already-present invertibility of the local `2 x 2` stage block.  The
`..._of_pivot_right_inverse_of_local_invertible` witness wrappers use this
adapter so the open blocker is the inverse/condition-number ratio itself, not a
local positivity artifact.
`matrix_invOf_eq_of_isRightInverse` discharges the pivot-identification
side condition for `⅟pivot`, `isRightInverse_of_eq_invOf` turns `⅟pivot` data
back into exact right-inverse data, and `isLeftInverse_of_isRightInverse` plus
the matrix-stage pivot-right wrappers discharge the reconstruction certificate.
The active missing theorems are
now the active-pair inverse-ratio theorem for each Schur-stage local flat
matrix, the active-column-dominance/local-Schur instantiation for true
matrix-product stages, and the final source-facing Eq.13.23 `ρ <= 2` bridge.
